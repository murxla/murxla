/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdarg.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include <atomic>
#include <chrono>
#include <cstdlib>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>

#include "dd.hpp"
#include "except.hpp"
#include "exit.hpp"
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
/* Parallel fuzzing (`-j/--jobs`) globals.                                    */
/*                                                                            */
/* Populated only when num_jobs > 1. The SIGINT handler reads g_worker_pids   */
/* to send SIGTERM to all live workers; access is signal-safe because we     */
/* finish populating it before installing the signal handler.                 */
/* -------------------------------------------------------------------------- */

static constexpr size_t MAX_WORKERS = 1024;
/** sig_atomic count of populated entries. */
static volatile sig_atomic_t g_worker_pid_count = 0;
/** Worker pids; only entries [0, g_worker_pid_count) are valid. */
static volatile pid_t g_worker_pids[MAX_WORKERS];

/* -------------------------------------------------------------------------- */

static Statistics*
initialize_statistics()
{
  Statistics* stats;
  stats = static_cast<Statistics*>(mmap(0,
                                        sizeof(Statistics),
                                        PROT_READ | PROT_WRITE,
                                        MAP_ANONYMOUS | MAP_SHARED,
                                        -1,
                                        0));
  memset(stats, 0, sizeof(Statistics));
  return stats;
}

static Aggregate*
initialize_aggregate()
{
  void* p = mmap(0,
                 sizeof(Aggregate),
                 PROT_READ | PROT_WRITE,
                 MAP_ANONYMOUS | MAP_SHARED,
                 -1,
                 0);
  MURXLA_EXIT_ERROR(p == MAP_FAILED)
      << "failed to map shared memory for aggregate counters";
  Aggregate* agg = new (p) Aggregate();
  agg->num_runs.store(0, std::memory_order_relaxed);
  agg->num_timeouts.store(0, std::memory_order_relaxed);
  agg->last_seed.store(0, std::memory_order_relaxed);
  return agg;
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
  std::filesystem::path p(tmp_dir);
  p /= "murxla-" + std::to_string(getpid());
  if (!std::filesystem::exists(p))
  {
    std::filesystem::create_directory(p);
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
    /* Send SIGTERM to each worker's process group so the worker AND its
     * solver/timeout grandchildren all die together. Using async-signal-safe
     * calls only. */
    sig_atomic_t n = g_worker_pid_count;
    for (sig_atomic_t i = 0; i < n; ++i)
    {
      pid_t p = g_worker_pids[i];
      if (p > 0) kill(-p, SIGTERM);
    }
    /* Reap workers so their PIDs don't linger as zombies. */
    for (sig_atomic_t i = 0; i < n; ++i)
    {
      pid_t p = g_worker_pids[i];
      if (p > 0)
      {
        int status;
        (void) waitpid(p, &status, 0);
      }
    }
    print_error_summary();
    caught_signal = sig;
  }
  if (std::filesystem::exists(TMP_DIR))
  {
    std::filesystem::remove_all(TMP_DIR);
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
  "  -j, --jobs <int>           number of parallel fuzzing jobs\n"             \
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
  "  -d, --dd                   enable delta debugging (in continuous\n"       \
  "                             mode, only the first trace of an error\n"      \
  "                             group is minimized)\n"                         \
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
  "  --bitwuzla                 test Bitwuzla\n"                               \
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
  else if (solver_kind == SOLVER_BITWUZLA)
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
  return name == SOLVER_BTOR || name == SOLVER_BITWUZLA || name == SOLVER_CVC5
         || name == SOLVER_YICES;
}

void
get_options(Options& options,
            size_t argc,
            char* argv[],
            std::vector<std::string>& args)
{
  /* Check if a trace file was specified. */
  std::string trace_file_name;
  for (size_t i = 1; i < argc; i++)
  {
    std::string arg(argv[i]);
    if (arg == "-u" || arg == "--untrace")
    {
      i += 1;
      check_next_arg(arg, i, argc);
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
  get_options(options, (size_t) argc, argv, args);

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
    else if (arg == "--bitwuzla")
    {
      check_solver(SOLVER_BITWUZLA);
      options.solver = SOLVER_BITWUZLA;
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
      options.max_runs = (uint32_t) std::stoi(args[i]);
    }
    else if (arg == "-j" || arg == "--jobs")
    {
      i += 1;
      check_next_arg(arg, i, size);
      int n = std::stoi(args[i]);
      MURXLA_EXIT_ERROR(n < 1) << "invalid argument to option '" << arg
                               << "': " << args[i] << " (must be >= 1)";
      options.num_jobs = (uint32_t) n;
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
    else if (arg == "--ff")
    {
      options.enabled_theories.push_back(THEORY_FF);
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
    else if (arg == "--no-ff")
    {
      options.disabled_theories.insert(THEORY_FF);
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
/* Parallel fuzzing: coordinator main loop.                                   */
/* ========================================================================== */

namespace {

bool
read_all_fd(int fd, void* buf, size_t n)
{
  char* p = static_cast<char*>(buf);
  while (n > 0)
  {
    ssize_t r = ::read(fd, p, n);
    if (r < 0)
    {
      if (errno == EINTR) continue;
      return false;
    }
    if (r == 0) return false;
    p += r;
    n -= static_cast<size_t>(r);
  }
  return true;
}

bool
write_all_fd(int fd, const void* buf, size_t n)
{
  const char* p = static_cast<const char*>(buf);
  while (n > 0)
  {
    ssize_t w = ::write(fd, p, n);
    if (w < 0)
    {
      if (errno == EINTR) continue;
      return false;
    }
    if (w == 0) return false;
    p += w;
    n -= static_cast<size_t>(w);
  }
  return true;
}

void
print_aggregate_status_line(Aggregate* agg,
                            statistics::Statistics* stats,
                            uint64_t num_errors,
                            double start_time,
                            uint64_t& num_printed_lines,
                            Terminal& term)
{
  uint64_t num_runs     = agg->num_runs.load(std::memory_order_relaxed);
  uint64_t num_timeouts = agg->num_timeouts.load(std::memory_order_relaxed);
  uint64_t last_seed    = agg->last_seed.load(std::memory_order_relaxed);
  double cur_time       = get_cur_wall_time();
  double rate = (cur_time > start_time)
                    ? static_cast<double>(num_runs) / (cur_time - start_time)
                    : 0.0;

  if (term.is_term())
  {
    term.erase(std::cout);
  }
  if (num_printed_lines % 100 == 0)
  {
    std::cout << std::setw(16) << "seed";
    std::cout << " " << std::setw(5) << "runs";
    std::cout << " " << std::setw(8) << "r/s";
    std::cout << " " << std::setw(5) << "sat";
    std::cout << " " << std::setw(5) << "unsat";
    std::cout << " " << std::setw(5) << "unknw";
    std::cout << " " << std::setw(5) << "to";
    std::cout << " " << std::setw(5) << "err";
    std::cout << std::endl;
    ++num_printed_lines;
  }
  std::cout << std::setw(16) << std::hex << last_seed << std::dec;
  std::cout << " " << std::setw(5) << num_runs;
  std::cout << " " << std::setw(8) << std::setprecision(2) << std::fixed
            << rate;
  std::cout << " " << std::setw(5) << stats->d_results[Solver::Result::SAT];
  std::cout << " " << std::setw(5) << stats->d_results[Solver::Result::UNSAT];
  std::cout << " " << std::setw(5) << stats->d_results[Solver::Result::UNKNOWN];
  std::cout << " " << std::setw(5) << num_timeouts;
  std::cout << " " << std::setw(5) << num_errors;
  std::cout << std::flush;
  if (!term.is_term())
  {
    std::cout << std::endl;
    ++num_printed_lines;
  }
}

/**
 * Read one length-prefixed message from `fd`. Returns false on EOF or error.
 */
bool
coord_read_msg(int fd, uint8_t& type, std::string& payload)
{
  uint8_t hdr[5];
  if (!read_all_fd(fd, hdr, sizeof(hdr))) return false;
  type         = hdr[0];
  uint32_t len = (uint32_t) hdr[1] | ((uint32_t) hdr[2] << 8)
                 | ((uint32_t) hdr[3] << 16) | ((uint32_t) hdr[4] << 24);
  payload.assign(len, '\0');
  if (len == 0) return true;
  return read_all_fd(fd, payload.data(), len);
}

void
run_coordinator_loop(Murxla& murxla,
                     statistics::Statistics* stats,
                     Aggregate* aggregate,
                     std::vector<int>& req_fds,
                     std::vector<int>& resp_fds,
                     double start_time)
{
  size_t num_workers = req_fds.size();
  std::vector<bool> alive(num_workers, true);
  size_t num_alive           = num_workers;
  uint64_t num_printed_lines = 0;
  Terminal term;

  auto last_status           = std::chrono::steady_clock::now();
  const auto status_interval = std::chrono::milliseconds(250);
  uint64_t last_num_runs     = 0;
  uint64_t last_num_errors   = 0;
  bool force_redraw          = true;

  while (num_alive > 0)
  {
    std::vector<struct pollfd> pfds;
    std::vector<size_t> idx;
    pfds.reserve(num_workers);
    idx.reserve(num_workers);
    for (size_t i = 0; i < num_workers; ++i)
    {
      if (!alive[i]) continue;
      struct pollfd p;
      p.fd      = req_fds[i];
      p.events  = POLLIN;
      p.revents = 0;
      pfds.push_back(p);
      idx.push_back(i);
    }

    int rc = poll(pfds.data(), pfds.size(), 250);
    if (rc < 0)
    {
      if (errno == EINTR) continue;
      MURXLA_EXIT_ERROR(true) << "poll failed: " << strerror(errno);
    }

    if (rc > 0)
    {
      for (size_t k = 0; k < pfds.size(); ++k)
      {
        if (!(pfds[k].revents & (POLLIN | POLLHUP | POLLERR))) continue;
        size_t i = idx[k];
        uint8_t type;
        std::string payload;
        if (!coord_read_msg(req_fds[i], type, payload))
        {
          /* EOF or error: worker has exited. */
          alive[i] = false;
          --num_alive;
          close(req_fds[i]);
          close(resp_fds[i]);
          continue;
        }
        if (type == (uint8_t) Murxla::RpcMsg::ADD_ERROR)
        {
          /* Decode payload, dedup centrally, reply. */
          if (payload.size() < sizeof(uint64_t) + sizeof(uint32_t))
          {
            alive[i] = false;
            --num_alive;
            close(req_fds[i]);
            close(resp_fds[i]);
            continue;
          }
          size_t off = 0;
          uint64_t seed;
          std::memcpy(&seed, &payload[off], sizeof(seed));
          off += sizeof(seed);
          uint32_t flen;
          std::memcpy(&flen, &payload[off], sizeof(flen));
          off += sizeof(flen);
          std::string filtered_err(&payload[off], flen);
          off += flen;
          uint32_t nlen;
          std::memcpy(&nlen, &payload[off], sizeof(nlen));
          off += sizeof(nlen);
          std::string normalized_err(&payload[off], nlen);

          auto [kind, error_id, ndup] =
              murxla.insert_error(filtered_err, normalized_err, seed);
          Murxla::RpcErrorReply reply;
          reply.kind        = static_cast<uint8_t>(kind);
          reply.error_id    = error_id;
          reply.nduplicates = ndup;
          if (!write_all_fd(resp_fds[i], &reply, sizeof(reply)))
          {
            alive[i] = false;
            --num_alive;
            close(req_fds[i]);
            close(resp_fds[i]);
          }
        }
        else if (type == (uint8_t) Murxla::RpcMsg::LOG)
        {
          /* Erase running status line, write the worker's text, redraw on
           * next status tick. */
          if (term.is_term()) term.erase(std::cout);
          std::cout << payload << std::flush;
          /* Force a redraw next tick. */
          force_redraw = true;
          last_status -= status_interval;
        }
        else
        {
          /* Unknown message type — protocol error; close worker. */
          alive[i] = false;
          --num_alive;
          close(req_fds[i]);
          close(resp_fds[i]);
        }
      }
    }

    auto now = std::chrono::steady_clock::now();
    if (now - last_status >= status_interval)
    {
      uint64_t cur_runs   = aggregate->num_runs.load(std::memory_order_relaxed);
      uint64_t cur_errors = g_errors.size();
      bool changed        = force_redraw || cur_runs != last_num_runs
                            || cur_errors != last_num_errors;
      if (changed)
      {
        print_aggregate_status_line(
            aggregate, stats, cur_errors, start_time, num_printed_lines, term);
        last_num_runs   = cur_runs;
        last_num_errors = cur_errors;
        force_redraw    = false;
      }
      last_status = now;
    }
  }

  /* Final status update + newline so the last line reflects the true totals
   * and the prompt comes back on its own line. */
  print_aggregate_status_line(
      aggregate, stats, g_errors.size(), start_time, num_printed_lines, term);
  std::cout << std::endl;
}

}  // namespace

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

  MURXLA_EXIT_ERROR(options.num_jobs > 1 && !is_continuous)
      << "-j/--jobs > 1 requires continuous mode (no -s/--seed, no "
         "-u/--untrace)";
  MURXLA_EXIT_ERROR(options.num_jobs > MAX_WORKERS)
      << "-j/--jobs exceeds maximum (" << MAX_WORKERS << ")";

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
      if (options.num_jobs > 1)
      {
        /* Parallel fuzzing: coordinator + N workers. The coordinator owns
         * g_errors and stdout; workers run their own test() loops and
         * report errors / log output via pipe RPC. */
        const uint32_t num_jobs = options.num_jobs;
        Aggregate* aggregate    = initialize_aggregate();

        std::vector<int> req_r(num_jobs), req_w(num_jobs);
        std::vector<int> resp_r(num_jobs), resp_w(num_jobs);
        for (uint32_t i = 0; i < num_jobs; ++i)
        {
          int rp[2], sp[2];
          MURXLA_EXIT_ERROR(pipe(rp) != 0)
              << "pipe() failed: " << strerror(errno);
          MURXLA_EXIT_ERROR(pipe(sp) != 0)
              << "pipe() failed: " << strerror(errno);
          req_r[i]  = rp[0];
          req_w[i]  = rp[1];
          resp_r[i] = sp[0];
          resp_w[i] = sp[1];
        }

        /* Distribute max_runs across workers. */
        uint32_t per_worker_max_runs = 0;
        if (options.max_runs > 0)
        {
          per_worker_max_runs = (options.max_runs + num_jobs - 1) / num_jobs;
        }

        /* Block SIGINT during fork so the (still-default) handler can't
         * fire while we're populating g_worker_pids. */
        sigset_t mask, prev;
        sigemptyset(&mask);
        sigaddset(&mask, SIGINT);
        sigprocmask(SIG_BLOCK, &mask, &prev);

        double start_time = get_cur_wall_time();

        for (uint32_t i = 0; i < num_jobs; ++i)
        {
          pid_t pid = fork();
          MURXLA_EXIT_ERROR(pid < 0) << "fork() failed: " << strerror(errno);
          if (pid == 0)
          {
            /* Put each worker in its own process group so the coordinator
             * can take down the whole subtree (worker + its solver/timeout
             * grandchildren) with `kill(-pgid, SIGTERM)`. */
            (void) setpgid(0, 0);

            /* Each worker needs its own tmp directory: tmp.err,
             * run-tmp1.{out,err}, tmp-api.trace, tmp-smt2.smt2 are all per-run
             * scratch files. Sharing one dir across workers causes concurrent
             * solver children to clobber each other's stderr, which in turn
             * corrupts the error message that the worker forwards to the
             * coordinator (often appearing empty). */
            {
              std::filesystem::path worker_tmp(TMP_DIR);
              worker_tmp /= "worker-" + std::to_string(i);
              std::error_code ec;
              std::filesystem::create_directories(worker_tmp, ec);
              murxla.d_tmp_dir = worker_tmp.string();
            }

            /* Worker: close unused pipe ends, configure Murxla, run. */
            for (uint32_t j = 0; j < num_jobs; ++j)
            {
              if (j != i)
              {
                close(req_r[j]);
                close(req_w[j]);
                close(resp_r[j]);
                close(resp_w[j]);
              }
            }
            close(req_r[i]);  /* worker doesn't read its own req */
            close(resp_w[i]); /* worker doesn't write its own resp */

            /* Reset SIGINT to default so workers die quickly on Ctrl+C
             * and the coordinator's handler does the cleanup. */
            signal(SIGINT, SIG_DFL);
            sigprocmask(SIG_SETMASK, &prev, nullptr);

            /* Each worker starts from a different seed so their fuzzing
             * sequences don't overlap. SeedGenerator already mixes time
             * and pid, so even with the same starting seed siblings
             * naturally diverge — but we partition explicitly to keep
             * `--seed S` reproducibility-friendly. */
            if (options.is_seeded)
            {
              options.seed = splitmix64(
                  options.seed ^ ((uint64_t) (i + 1) * 0x9E3779B97F4A7C15ULL));
            }
            options.max_runs = per_worker_max_runs;

            murxla.set_parallel_role(
                Murxla::Role::WORKER, req_w[i], resp_r[i], aggregate);

            try
            {
              murxla.test();
            }
            catch (MurxlaConfigException& e)
            {
              /* Send a one-line LOG and exit. */
              std::string s =
                  std::string("config error: ") + e.get_msg() + "\n";
              (void) ::write(req_w[i], s.data(), s.size());
              _exit(EXIT_ERROR);
            }
            catch (MurxlaException& e)
            {
              std::string s = std::string("error: ") + e.get_msg() + "\n";
              (void) ::write(req_w[i], s.data(), s.size());
              _exit(EXIT_ERROR);
            }
            close(req_w[i]);
            close(resp_r[i]);
            _exit(0);
          }

          /* Parent: place the worker in its own process group (mirrors the
           * setpgid in the child to avoid a race where SIGINT arrives
           * before the child has set its own pgid). */
          (void) setpgid(pid, pid);

          /* Record pid and close unused pipe ends. */
          g_worker_pids[g_worker_pid_count] = pid;
          g_worker_pid_count                = g_worker_pid_count + 1;
          close(req_w[i]);
          close(resp_r[i]);
        }

        /* Now safe to install our SIGINT handler that knows about
         * g_worker_pids. */
        set_sigint_handler_stats();
        sigprocmask(SIG_SETMASK, &prev, nullptr);

        murxla.set_parallel_role(Murxla::Role::COORDINATOR, -1, -1, aggregate);

        run_coordinator_loop(
            murxla, stats, aggregate, req_r, resp_w, start_time);

        /* Reap any remaining workers (most should already be reaped via
         * pipe EOF detection in the coordinator loop, but harvest
         * exit statuses to avoid zombies). */
        for (sig_atomic_t i = 0; i < g_worker_pid_count; ++i)
        {
          int status;
          (void) waitpid(g_worker_pids[i], &status, WNOHANG);
        }

        munmap(aggregate, sizeof(Aggregate));
      }
      else
      {
        set_sigint_handler_stats();
        murxla.test();
      }
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

  if (std::filesystem::exists(TMP_DIR))
  {
    std::filesystem::remove_all(TMP_DIR);
  }

  return 0;
}
