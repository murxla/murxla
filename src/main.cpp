/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include <fcntl.h>
#include <signal.h>
#include <stdarg.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include <cstdlib>
#include <ctime>
#include <fstream>
#include <iostream>
#include <numeric>
#include <regex>
#include <sstream>

#include "dd.hpp"
#include "except.hpp"
#include "exit.hpp"
#include "fs.hpp"
#include "murxla.hpp"
#include "options.hpp"
#include "solver_option.hpp"
#include "statistics.hpp"
#include "util.hpp"

using namespace murxla;
using namespace statistics;
using namespace nlohmann;

static std::string TMP_DIR = "";

/* -------------------------------------------------------------------------- */

/** Map normalized error message to pair (original error message, seeds). */
static Murxla::ErrorMap g_errors;
static bool g_errors_print_csv = false;

/* -------------------------------------------------------------------------- */

static Statistics*
initialize_statistics()
{
  int fd;
  std::stringstream ss;
  std::string shmfilename;
  Statistics* stats;

  ss << "/tmp/murxla-shm-" << getpid();
  shmfilename = ss.str();

  MURXLA_EXIT_ERROR((fd = open(shmfilename.c_str(), O_RDWR | O_CREAT, S_IRWXU))
                    < 0)
      << "failed to create shared memory file for statistics";

  stats = static_cast<Statistics*>(mmap(0,
                                        sizeof(Statistics),
                                        PROT_READ | PROT_WRITE,
                                        MAP_ANONYMOUS | MAP_SHARED,
                                        fd,
                                        0));
  memset(stats, 0, sizeof(Statistics));

  MURXLA_EXIT_ERROR(close(fd))
      << "failed to close shared memory file for statistics";
  (void) unlink(shmfilename.c_str());
  return stats;
}

static bool
path_is_dir(const std::string& path)
{
  struct stat buffer;
  if (stat(path.c_str(), &buffer) != 0) return false;  // doesn't exist
  return (buffer.st_mode & S_IFMT) == S_IFDIR;         // is a directory?
}

void
create_tmp_directory(const std::string& tmp_dir)
{
  filesystem::path p(tmp_dir);
  p /= "murxla-" + std::to_string(getpid());
  if (!filesystem::exists(p))
  {
    filesystem::create_directory(p);
  }
  TMP_DIR = p.string();
}

std::string
escape_csv(const std::string& str)
{
  std::vector<std::pair<std::string, std::string>> escape;
  escape.emplace_back("\n", "\\n");
  escape.emplace_back("\"", "\"\"");

  std::string s(str);

  for (const auto& [search, replace] : escape)
  {
    size_t pos = s.find(search);
    while (pos != std::string::npos)
    {
      s.replace(pos, search.size(), replace);
      pos = s.find(search, pos + replace.size());
    }
  }

  return s;
}

void
print_error_summary()
{
  if (g_errors.size())
  {
    std::cout << "\nError statistics (" << g_errors.size() << " in total):\n"
              << std::endl;

    if (g_errors_print_csv)
    {
      for (const auto& [e_norm, e_info] : g_errors)
      {
        std::cout << "murxla:csv:" << e_info.seeds.size() << ",";
        std::cout << "\"" << escape_csv(e_info.errmsg) << "\",";
        for (auto seed : e_info.seeds)
        {
          std::cout << std::hex << seed << " ";
        }
        std::cout << std::endl;
      }
    }
    else
    {
      Terminal term;
      for (const auto& [e_norm, e_info] : g_errors)
      {
        std::cout << term.red() << e_info.seeds.size()
                  << " errors: " << term.defaultcolor();
        for (size_t i = 0; i < std::min<size_t>(e_info.seeds.size(), 10); ++i)
        {
          if (i > 0)
          {
            std::cout << " ";
          }
          std::cout << std::hex << e_info.seeds[i] << std::dec;
        }
        std::cout << "\n" << e_info.errmsg << "\n" << std::endl;
      }
    }
  }
}

/* -------------------------------------------------------------------------- */
/* Signal handling                                                            */
/* -------------------------------------------------------------------------- */

/* Signal handler for printing error summary. */
static void (*sig_int_handler_esummary)(int32_t);

static void
catch_signal_esummary(int32_t sig)
{
  static int32_t caught_signal = 0;
  if (!caught_signal)
  {
    print_error_summary();
    caught_signal = sig;
  }
  if (filesystem::exists(TMP_DIR))
  {
    filesystem::remove_all(TMP_DIR);
  }

  (void) signal(SIGINT, sig_int_handler_esummary);
  raise(sig);
  exit(EXIT_ERROR);
}

static void
set_sigint_handler_stats(void)
{
  sig_int_handler_esummary = signal(SIGINT, catch_signal_esummary);
}

/* -------------------------------------------------------------------------- */
/* Help message                                                               */
/* -------------------------------------------------------------------------- */

#define MURXLA_USAGE                                                           \
  "Usage:"                                                                     \
  "  murxla [options]\n"                                                       \
  "\n"                                                                         \
  "  -h, --help                 print this message and exit\n"                 \
  "  -p, --profile <profile>    load solver profile\n"                         \
  "  -v, --verbosity            increase verbosity\n"                          \
  "  -T, --tmp-dir <dir>        write temporary files to given directory\n"    \
  "  -O, --out-dir <dir>        write output files to given directory\n"       \
  "  -l, --smt-lib              generate SMT-LIB compliant traces only\n"      \
  "  -y, --random-symbols       use random symbol names\n"                     \
  "  --stats                    print statistics\n"                            \
  "  --print-fsm                print FSM configuration, may be combined\n"    \
  "                             with solver option to show config for \n"      \
  "\n"                                                                         \
  " Continuous mode options:\n"                                                \
  "  -t, --time <double>        time limit per test run\n"                     \
  "  -m, --max-runs <int>       limit number of test runs\n"                   \
  "  --csv                      print error summary in csv format\n"           \
  "  -e, --export-errors <out>  export found errors to JSON file <out>\n"      \
  "\n"                                                                         \
  " One-shot mode options:\n"                                                  \
  "  -s, --seed <int>           seed for random number generator\n"            \
  "  -a, --api-trace <file>     trace API call sequence into <file>\n"         \
  "  -f, --smt2-file <file>     write --smt2 output to <file>\n"               \
  "  -u, --untrace <file>       replay given API call sequence\n"              \
  "  --solver-trace             print native solver API trace to stdout\n"     \
  "\n"                                                                         \
  " Trace minimizer:\n"                                                        \
  "  -d, --dd                   enable delta debugging\n"                      \
  "  --dd-match-err <string>    check for occurrence of <string> in stderr\n"  \
  "                             output when delta debugging\n"                 \
  "  --dd-match-out <string>    check for occurrence of <string> in stdout\n"  \
  "                             output when delta debugging\n"                 \
  "  --dd-ignore-err            ignore stderr output when delta debugging\n"   \
  "  --dd-ignore-out            ignore stdout output when delta debugging\n"   \
  "  -D, --dd-trace <file>      delta debug API trace into <file>\n"           \
  "\n"                                                                         \
  " Solvers:\n"                                                                \
  "  --btor                     test Boolector\n"                              \
  "  --bzla                     test Bitwuzla\n"                               \
  "  --cvc5                     test cvc5\n"                                   \
  "  --yices                    test Yices\n"                                  \
  "  --smt2 [<binary>]          print SMT-LIB 2 (optionally to solver "        \
  "binary\n"                                                                   \
  "                             via stdout)\n"                                 \
  "  -o name=value,...          solver options enabled by default\n"           \
  "  --fuzz-opts [wildcard,...] restrict options to be fuzzed with multiple\n" \
  "                             wildcards, which are matched against option\n" \
  "                             names. use ^ to indicate a wildcard must\n"    \
  "                             match the beginning of an option name\n"       \
  "  -c, --cross-check <solver> cross check with <solver> (SMT-LIB only)\n"    \
  "  --cross-check-opts name=value,...\n"                                      \
  "                             options for cross check solver\n"              \
  "  -C, --check [<solver>]     check unsat cores/assumptions and \n"          \
  "                             model values with <solver>\n"                  \
  "\n"                                                                         \
  " Enable/disable theories:\n"                                                \
  "  --[no-]arrays                theory of arrays\n"                          \
  "  --[no-]bags                  theory of bags\n"                            \
  "  --[no-]bv                    theory of bit-vectors\n"                     \
  "  --[no-]dt                    theory of datatypes\n"                       \
  "  --[no-]fp                    theory of floating-points\n"                 \
  "  --[no-]ints                  theory of integers\n"                        \
  "  --[no-]quant                 quantifiers\n"                               \
  "  --[no-]reals                 theory of reals\n"                           \
  "  --[no-]seq                   theory of sequences\n"                       \
  "  --[no-]sets                  theory of sets\n"                            \
  "  --[no-]strings               theory of strings\n"                         \
  "  --[no-]trans                 theory of transcendentals\n"                 \
  "  --[no-]uf                    uninterpreted functions\n"                   \
  "\n"                                                                         \
  " Options for enabled theories:\n"                                           \
  "  --linear                   restrict arithmetic to linear fragment"

/* -------------------------------------------------------------------------- */
/* Command-line option parsing                                                */
/* -------------------------------------------------------------------------- */

void
check_next_arg(const std::string& option, size_t i, size_t argc)
{
  MURXLA_EXIT_ERROR(i >= argc)
      << "missing argument to option '" << option << "'";
}

void
check_solver(const SolverKind& solver_kind)
{
  if (solver_kind == SOLVER_BTOR)
  {
#ifndef MURXLA_USE_BOOLECTOR
    MURXLA_EXIT_ERROR(true) << "Boolector not configured";
#endif
  }
  else if (solver_kind == SOLVER_BZLA)
  {
#ifndef MURXLA_USE_BITWUZLA
    MURXLA_EXIT_ERROR(true) << "Bitwuzla not configured";
#endif
  }
  else if (solver_kind == SOLVER_CVC5)
  {
#ifndef MURXLA_USE_CVC5
    MURXLA_EXIT_ERROR(true) << "cvc5 not configured";
#endif
  }
  else if (solver_kind == SOLVER_YICES)
  {
#ifndef MURXLA_USE_YICES
    MURXLA_EXIT_ERROR(true) << "Yices not configured";
#endif
  }
}

bool
is_valid_solver_str(const std::string& name)
{
  return name == SOLVER_BTOR || name == SOLVER_BZLA || name == SOLVER_CVC5
         || name == SOLVER_YICES;
}

void
get_options(Options& options,
            int argc,
            char* argv[],
            std::vector<std::string>& args)
{
  /* Check if a trace file was specified. */
  std::string trace_file_name;
  for (int32_t i = 1; i < argc; i++)
  {
    std::string arg(argv[i]);
    if (arg == "-u" || arg == "--untrace")
    {
      i += 1;
      check_next_arg(args.back(), i, argc);
      options.untrace_file_name = argv[i];
      continue;
    }
    args.push_back(arg);
  }

  if (!options.untrace_file_name.empty())
  {
    std::vector<std::string> opts;
    std::ifstream trace(options.untrace_file_name);
    if (trace.good())
    {
      std::string line;
      std::getline(trace, line);
      if (line.rfind("set-murxla-options", 0) == 0)
      {
        opts = split(line, ' ');
        args.insert(args.begin(), opts.begin() + 1, opts.end());
      }
    }
  }
}

void
parse_options(Options& options, int argc, char* argv[])
{
  std::vector<std::string> args, record_args;
  get_options(options, argc, argv, args);

  for (size_t i = 0, size = args.size(); i < size; ++i)
  {
    std::string arg = args[i];
    if (arg == "-h" || arg == "--help")
    {
      std::cout << MURXLA_USAGE << std::endl;
      exit(0);
    }
    else if (arg == "-s" || arg == "--seed")
    {
      std::stringstream ss;
      i += 1;
      check_next_arg(arg, i, size);
      ss << args[i];
      MURXLA_EXIT_ERROR(ss.str().find('-') != std::string::npos)
          << "invalid argument to option '" << arg << "': " << ss.str();

      // Check if given seed is hexadecimal
      auto seed_str = ss.str();
      if (std::all_of(seed_str.begin(), seed_str.end(), [](unsigned char c) {
            return std::isxdigit(c);
          }))
      {
        ss >> std::hex >> options.seed;
      }
      else
      {
        ss >> options.seed;
      }
      options.is_seeded = true;
    }
    else if (arg == "-t" || arg == "--time")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.time = std::atof(args[i].c_str());
    }
    else if (arg == "-v" || arg == "--verbosity")
    {
      options.verbosity += 1;
    }
    else if (arg == "-p" || arg == "--profile")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.solver_profile_filename = args[i];
    }
    else if (arg == "-a" || arg == "--api-trace")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.api_trace_file_name = args[i];
    }
    else if (arg == "-d" || arg == "--dd")
    {
      options.dd = true;
    }
    else if (arg == "--dd-match-out")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.dd_match_out = args[i];
    }
    else if (arg == "--dd-match-err")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.dd_match_err = args[i];
    }
    else if (arg == "--dd-ignore-out")
    {
      options.dd_ignore_out = true;
    }
    else if (arg == "--dd-ignore-err")
    {
      options.dd_ignore_err = true;
    }
    else if (arg == "-D" || arg == "--dd-trace")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.dd_trace_file_name = args[i];
    }
    else if (arg == "-u" || arg == "--untrace")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.untrace_file_name = args[i];
    }
    else if (arg == "-c" || arg == "--cross-check")
    {
      record_args.push_back(arg);
      i += 1;
      check_next_arg(arg, i, size);
      SolverKind solver = args[i];
      record_args.push_back(solver);
      MURXLA_EXIT_ERROR(!is_valid_solver_str(solver))
          << "invalid argument " << solver << " to option '" << arg << "'";
      check_solver(solver);
      options.cross_check = solver;
    }
    else if (arg == "-C" || arg == "--check")
    {
      record_args.push_back(arg);
      options.check_solver = true;
      if (size > i && is_valid_solver_str(args[i + 1]))
      {
        options.check_solver_name = args[i + 1];
        record_args.push_back(args[i + 1]);
        i += 1;
      }
    }
    else if (arg == "--no-check")
    {
      record_args.push_back(arg);
      options.check_solver = false;
    }
    else if (arg == "-y" || arg == "--random-symbols")
    {
      options.simple_symbols = false;
    }
    else if (arg == "-T" || arg == "--tmp-dir")
    {
      i += 1;
      check_next_arg(arg, i, size);
      MURXLA_EXIT_ERROR(!path_is_dir(args[i]))
          << "given path is not a directory '" << args[i] << "'";
      options.tmp_dir = args[i];
    }
    else if (arg == "-O" || arg == "--out-dir")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.out_dir = args[i];
    }
    else if (arg == "--btor")
    {
      check_solver(SOLVER_BTOR);
      options.solver = SOLVER_BTOR;
      record_args.push_back(arg);
    }
    else if (arg == "--bzla")
    {
      check_solver(SOLVER_BZLA);
      options.solver = SOLVER_BZLA;
      record_args.push_back(arg);
    }
    else if (arg == "--cvc5")
    {
      check_solver(SOLVER_CVC5);
      options.solver = SOLVER_CVC5;
      record_args.push_back(arg);
    }
    else if (arg == "--yices")
    {
      check_solver(SOLVER_YICES);
      options.solver = SOLVER_YICES;
      record_args.push_back(arg);
    }
    else if (arg == "--smt2")
    {
      record_args.push_back(arg);
      if (i + 1 < size && args[i + 1][0] != '-')
      {
        MURXLA_EXIT_ERROR(!options.solver.empty())
            << "multiple solvers defined";
        i += 1;
        options.solver_binary = args[i];
        record_args.push_back(args[i]);
      }
      options.solver = SOLVER_SMT2;
    }
    else if (arg == "-f" || arg == "--smt2-file")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.smt2_file_name = args[i];
    }
    else if (arg == "-o" || arg == "--cross-check-opts")
    {
      record_args.push_back(arg);
      i += 1;
      check_next_arg(arg, i, size);
      const std::string prefix =
          arg == "--cross-check-opts" ? MURXLA_CHECK_SOLVER_OPT_PREFIX : "";
      auto solver_options = split(args[i], ',');
      record_args.push_back(args[i]);
      for (auto opt : solver_options)
      {
        auto split_opt = split(opt, '=');
        if (split_opt.empty()) continue;
        MURXLA_EXIT_ERROR(split_opt.size() != 2)
            << "invalid solver option format: '" << opt
            << "', expected 'name=value'";
        options.solver_options.emplace_back(prefix + split_opt[0],
                                            split_opt[1]);
      }
    }
    else if (arg == "--stats")
    {
      options.print_stats = true;
    }
    else if (arg == "--print-fsm")
    {
      options.print_fsm = true;
    }
    else if (arg == "--csv")
    {
      g_errors_print_csv = true;
    }
    else if (arg == "-e" || arg == "--export-errors")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.export_errors_filename = args[i];
    }
    else if (arg == "--solver-trace")
    {
      options.solver_trace = true;
    }
    else if (arg == "-m" || arg == "--max-runs")
    {
      i += 1;
      check_next_arg(arg, i, size);
      options.max_runs = std::stoi(args[i]);
    }
    else if (arg == "-l" || arg == "--smt-lib")
    {
      options.smtlib_compliant = true;
    }
    else if (arg == "--fuzz-opts")
    {
      options.fuzz_options = true;
      if (i + 1 < size && args[i + 1][0] != '-')
      {
        i += 1;
        if (!options.fuzz_options_filter.empty())
        {
          options.fuzz_options_filter += ",";
        }
        options.fuzz_options_filter += args[i];
      }
    }
    else if (arg == "--arrays")
    {
      options.enabled_theories.push_back(THEORY_ARRAY);
    }
    else if (arg == "--bags")
    {
      options.enabled_theories.push_back(THEORY_BAG);
    }
    else if (arg == "--bv")
    {
      options.enabled_theories.push_back(THEORY_BV);
    }
    else if (arg == "--dt")
    {
      options.enabled_theories.push_back(THEORY_DT);
    }
    else if (arg == "--fp")
    {
      options.enabled_theories.push_back(THEORY_FP);
    }
    else if (arg == "--ints")
    {
      options.enabled_theories.push_back(THEORY_INT);
    }
    else if (arg == "--quant")
    {
      options.enabled_theories.push_back(THEORY_QUANT);
    }
    else if (arg == "--reals")
    {
      options.enabled_theories.push_back(THEORY_REAL);
    }
    else if (arg == "--trans")
    {
      options.enabled_theories.push_back(THEORY_TRANSCENDENTAL);
    }
    else if (arg == "--linear")
    {
      options.arith_linear = true;
    }
    else if (arg == "--seq")
    {
      options.enabled_theories.push_back(THEORY_SEQ);
    }
    else if (arg == "--sets")
    {
      options.enabled_theories.push_back(THEORY_SET);
    }
    else if (arg == "--strings")
    {
      options.enabled_theories.push_back(THEORY_STRING);
    }
    else if (arg == "--uf")
    {
      options.enabled_theories.push_back(THEORY_UF);
    }
    else if (arg == "--no-arrays")
    {
      options.disabled_theories.insert(THEORY_ARRAY);
    }
    else if (arg == "--no-bv")
    {
      options.disabled_theories.insert(THEORY_BV);
    }
    else if (arg == "--no-bags")
    {
      options.disabled_theories.insert(THEORY_BAG);
    }
    else if (arg == "--no-dt")
    {
      options.disabled_theories.insert(THEORY_DT);
    }
    else if (arg == "--no-fp")
    {
      options.disabled_theories.insert(THEORY_FP);
    }
    else if (arg == "--no-ints")
    {
      options.disabled_theories.insert(THEORY_INT);
    }
    else if (arg == "--no-quant")
    {
      options.disabled_theories.insert(THEORY_QUANT);
    }
    else if (arg == "--no-reals")
    {
      options.disabled_theories.insert(THEORY_REAL);
    }
    else if (arg == "--no-seq")
    {
      options.disabled_theories.insert(THEORY_SEQ);
    }
    else if (arg == "--no-sets")
    {
      options.disabled_theories.insert(THEORY_SET);
    }
    else if (arg == "--no-strings")
    {
      options.disabled_theories.insert(THEORY_STRING);
    }
    else if (arg == "--no-trans")
    {
      options.disabled_theories.insert(THEORY_TRANSCENDENTAL);
    }
    else if (arg == "--no-uf")
    {
      options.disabled_theories.insert(THEORY_UF);
    }
    else
    {
      MURXLA_EXIT_ERROR(true) << "unknown option '" << arg << "'";
    }
  }

  if (options.solver.empty())
  {
    options.solver = SOLVER_SMT2;
  }

  if (options.solver == SOLVER_SMT2)
  {
    options.check_solver      = false;
    options.check_solver_name = "";
  }

  /* Use an instance of the same solver for checking unsat cores if not
   * otherwise specified. */
  if (options.check_solver && options.check_solver_name.empty())
  {
    options.check_solver_name = options.solver;
  }

  /* Record command line options for tracing. */
  std::stringstream ss;
  ss << "set-murxla-options";
  for (const auto& arg : record_args)
  {
    ss << " " << arg;
  }
  options.cmd_line_trace = ss.str();
}

/* ========================================================================== */

int
main(int argc, char* argv[])
{
  statistics::Statistics* stats = initialize_statistics();
  SolverOptions solver_options;
  Options options;

  parse_options(options, argc, argv);

  bool is_untrace    = !options.untrace_file_name.empty();
  bool is_continuous = !options.is_seeded && !is_untrace;
  bool is_forked     = options.dd || is_continuous;

  create_tmp_directory(options.tmp_dir);

  std::string api_trace_file_name = options.api_trace_file_name;

  MURXLA_EXIT_ERROR(!api_trace_file_name.empty()
                    && api_trace_file_name == options.untrace_file_name)
      << "tracing into the file that is untraced is not supported";

  try
  {
    Murxla murxla(stats, options, &solver_options, &g_errors, TMP_DIR);

    if (options.print_fsm)
    {
      murxla.print_fsm();
      exit(0);
    }

    if (is_continuous)
    {
      set_sigint_handler_stats();
      murxla.test();
    }
    else
    {
      std::string api_trace_file_name = options.api_trace_file_name;
      std::string dd_trace_file_name  = options.dd_trace_file_name;
      std::string out_file_name = DEVNULL;
      std::string err_file_name = DEVNULL;

      if (options.dd)
      {
        if (api_trace_file_name.empty())
        {
          /* When delta-debugging, trace into file instead of stdout. */
          api_trace_file_name = get_tmp_file_path("tmp.trace", TMP_DIR);
        }

        if (dd_trace_file_name.empty())
        {
          /* Minimized trace file name. */
          if (is_untrace)
          {
            dd_trace_file_name = replace_suffix_file_name(
                options.untrace_file_name, ".min.trace");
            MURXLA_MESSAGE_DD << "minimizing untraced file '"
                              << options.untrace_file_name << "'";
          }
          else
          {
            std::stringstream ss;
            ss << "murxla-" << std::hex << options.seed << ".min.trace";
            dd_trace_file_name = ss.str();
            MURXLA_MESSAGE_DD << "minimizing run with seed " << std::hex
                              << options.seed;
          }
        }
      }

      (void) murxla.run(options.seed,
                        options.time,
                        out_file_name,
                        err_file_name,
                        api_trace_file_name,
                        options.untrace_file_name,
                        is_forked,
                        true,
                        api_trace_file_name.empty()
                            ? Murxla::TraceMode::TO_STDOUT
                            : Murxla::TraceMode::TO_FILE);

      if (options.dd)
      {
        DD(&murxla, options.seed).run(api_trace_file_name, dd_trace_file_name);
      }
    }
  }
  catch (MurxlaConfigException& e)
  {
    MURXLA_EXIT_ERROR_CONFIG(true) << e.get_msg();
  }
  catch (MurxlaException& e)
  {
    MURXLA_EXIT_ERROR(true) << e.get_msg();
  }

  print_error_summary();

  if (options.print_stats)
  {
    stats->print();
  }

  MURXLA_EXIT_ERROR(munmap(stats, sizeof(Statistics)))
      << "failed to unmap shared memory for statistics";

  if (filesystem::exists(TMP_DIR))
  {
    filesystem::remove_all(TMP_DIR);
  }

  return 0;
}
