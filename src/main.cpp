#include <fcntl.h>
#include <stdarg.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include <cstdlib>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <numeric>
#include <regex>
#include <sstream>
#include <toml.hpp>

#include "except.hpp"
#include "exit.hpp"
#include "murxla.hpp"
#include "options.hpp"
#include "solver_option.hpp"
#include "statistics.hpp"
#include "util.hpp"

using namespace murxla;
using namespace statistics;

static std::string TMP_DIR = "";

/* -------------------------------------------------------------------------- */

/** Map normalized error message to pair (original error message, seeds). */
static Murxla::ErrorMap g_errors;

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
  std::filesystem::path p(tmp_dir);
  p /= "murxla-" + std::to_string(getpid());
  if (!std::filesystem::exists(p))
  {
    std::filesystem::create_directory(p);
  }
  TMP_DIR = p.string();
}

void
print_error_summary()
{
  if (g_errors.size())
  {
    std::cout << "\nError statistics (" << g_errors.size() << " in total):\n"
              << std::endl;
    for (const auto& p : g_errors)
    {
      const auto& err   = p.second.first;
      const auto& seeds = p.second.second;
      std::cout << COLOR_RED << seeds.size() << " errors: " << COLOR_DEFAULT;
      for (size_t i = 0; i < std::min<size_t>(seeds.size(), 10); ++i)
      {
        if (i > 0)
        {
          std::cout << " ";
        }
        std::cout << seeds[i];
      }
      std::cout << "\n" << err << "\n" << std::endl;
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
  "usage:\n"                                                                   \
  "  murxla [options]\n\n"                                                     \
  "  -h, --help                 print this message and exit\n"                 \
  "  -s, --seed <int>           seed for random number generator\n"            \
  "  -S, --trace-seeds          trace seed for each API call\n"                \
  "  -t, --time <double>        time limit for MBT runs\n"                     \
  "  -v, --verbosity            increase verbosity\n"                          \
  "  -m, --max-runs <int>       limit number of test runs\n"                   \
  "  -d, --dd                   enable delta debugging\n"                      \
  "  --dd-err <string>          check for occurrence of <string> in stderr\n"  \
  "                             output when delta debugging\n"                 \
  "  --dd-out <string>          check for occurrence of <string> in stdout\n"  \
  "                             output when delta debugging\n"                 \
  "  -D, --dd-trace <file>      delta debug API trace into <file>\n"           \
  "  -a, --api-trace <file>     trace API call sequence into <file>\n"         \
  "  -u, --untrace <file>       replay given API call sequence\n"              \
  "  -o, --options <file>       solver option model toml file\n"               \
  "  -f, --smt2-file <file>     write --smt2 output to <file>\n"               \
  "  -l, --smt-lib              generate SMT-LIB compliant traces only\n"      \
  "  -c, --cross-check <solver> cross check with <solver> (SMT-lib2 only)\n"   \
  "  -y, --random-symbols       use random symbol names\n"                     \
  "  -T, --tmp-dir <dir>        write tmp files to given directory\n"          \
  "  -O, --out-dir <dir>        write output files to given directory\n"       \
  "  --btor                     test Boolector\n"                              \
  "  --bzla                     test Bitwuzla\n"                               \
  "  --cvc5                     test cvc5\n"                                   \
  "  --yices                    test Yices\n"                                  \
  "  --smt2 [<binary>]          dump SMT-LIB 2 (optionally to solver binary\n" \
  "                             via stdout)\n"                                 \
  "  --stats                    print statistics\n\n"                          \
  " enabling specific theories:\n"                                             \
  "  --arrays                   theory of arrays\n"                            \
  "  --bv                       theory of bit-vectors\n"                       \
  "  --fp                       theory of floating-points\n"                   \
  "  --ints                     theory of integers\n"                          \
  "  --quant                    quantifiers\n"                                 \
  "  --reals                    theory of reals\n"                             \
  "  --strings                  theory of strings\n"                           \
  " constraining/extending features based for enabled theories:\n"             \
  "  --linear                   restrict arithmetic to linear fragment\n"      \
  "  --uf                       uninterpreted functions"

/* -------------------------------------------------------------------------- */
/* Command-line option parsing                                                */
/* -------------------------------------------------------------------------- */

void
check_next_arg(std::string& option, int i, int argc)
{
  MURXLA_EXIT_ERROR(i >= argc)
      << "missing argument to option '" << option << "'";
}

void
parse_options(Options& options, int argc, char* argv[])
{
  for (int i = 1; i < argc; i++)
  {
    std::string arg = argv[i];
    if (arg == "-h" || arg == "--help")
    {
      MURXLA_MESSAGE << MURXLA_USAGE;
      exit(0);
    }
    else if (arg == "-s" || arg == "--seed")
    {
      std::stringstream ss;
      i += 1;
      check_next_arg(arg, i, argc);
      ss << argv[i];
      MURXLA_EXIT_ERROR(ss.str().find('-') != std::string::npos)
          << "invalid argument to option '" << argv[i - 1] << "': " << ss.str();
      ss >> options.seed;
      options.is_seeded = true;
    }
    else if (arg == "-t" || arg == "--time")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.time = std::atof(argv[i]);
    }
    else if (arg == "-v" || arg == "--verbosity")
    {
      options.verbosity += 1;
    }
    else if (arg == "-a" || arg == "--api-trace")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.api_trace_file_name = argv[i];
    }
    else if (arg == "-d" || arg == "--dd")
    {
      options.dd = true;
    }
    else if (arg == "--dd-out")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.dd_out_string = argv[i];
    }
    else if (arg == "--dd-err")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.dd_err_string = argv[i];
    }
    else if (arg == "-D" || arg == "--dd-trace")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.dd_trace_file_name = argv[i];
    }
    else if (arg == "-u" || arg == "--untrace")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.untrace_file_name = argv[i];
    }
    else if (arg == "-c" || arg == "--cross-check")
    {
      MURXLA_EXIT_ERROR(options.solver == Murxla::SOLVER_SMT2)
          << "option " << arg << " is incompatible with option --smt2";
      i += 1;
      check_next_arg(arg, i, argc);
      std::string solver = argv[i];
      MURXLA_EXIT_ERROR(
          solver != Murxla::SOLVER_BTOR && solver != Murxla::SOLVER_BZLA
          && solver != Murxla::SOLVER_CVC5 && solver != Murxla::SOLVER_YICES)
          << "invalid argument " << solver << " to option '" << arg << "'";
      options.cross_check = solver;
    }
    else if (arg == "-y" || arg == "--random-symbols")
    {
      options.simple_symbols = false;
    }
    else if (arg == "-T" || arg == "--tmp-dir")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      MURXLA_EXIT_ERROR(!path_is_dir(argv[i]))
          << "given path is not a directory '" << argv[i] << "'";
      options.tmp_dir = argv[i];
    }
    else if (arg == "-O" || arg == "--out-dir")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      MURXLA_EXIT_ERROR(!path_is_dir(argv[i]))
          << "given path is not a directory '" << argv[i] << "'";
      options.out_dir = argv[i];
    }
    else if (arg == "--btor")
    {
      MURXLA_EXIT_ERROR(!options.solver.empty()) << "multiple solvers defined";
      options.solver = Murxla::SOLVER_BTOR;
    }
    else if (arg == "--bzla")
    {
      MURXLA_EXIT_ERROR(!options.solver.empty()) << "multiple solvers defined";
      options.solver = Murxla::SOLVER_BZLA;
    }
    else if (arg == "--cvc5")
    {
      MURXLA_EXIT_ERROR(!options.solver.empty()) << "multiple solvers defined";
      options.solver = Murxla::SOLVER_CVC5;
    }
    else if (arg == "--yices")
    {
      MURXLA_EXIT_ERROR(!options.solver.empty()) << "multiple solvers defined";
      options.solver = Murxla::SOLVER_YICES;
    }
    else if (arg == "--smt2")
    {
      MURXLA_EXIT_ERROR(!options.cross_check.empty())
          << "option " << arg
          << " is incompatible with option -c, --cross-check";
      if (i + 1 < argc && argv[i + 1][0] != '-')
      {
        MURXLA_EXIT_ERROR(!options.solver.empty())
            << "multiple solvers defined";
        i += 1;
        options.solver_binary = argv[i];
      }
      options.solver = Murxla::SOLVER_SMT2;
    }
    else if (arg == "-f" || arg == "--smt2-file")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.smt2_file_name = argv[i];
    }
    else if (arg == "-o" || arg == "--options")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.solver_options_file = argv[i];
    }
    else if (arg == "-S" || arg == "--trace-seeds")
    {
      options.trace_seeds = true;
    }
    else if (arg == "--stats")
    {
      options.print_stats = true;
    }
    else if (arg == "-m" || arg == "--max-runs")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.max_runs = std::stoi(argv[i]);
    }
    else if (arg == "-l" || arg == "--smt-lib")
    {
      options.smt = true;
    }
    else if (arg == "--arrays")
    {
      options.enabled_theories.push_back(THEORY_ARRAY);
    }
    else if (arg == "--bv")
    {
      options.enabled_theories.push_back(THEORY_BV);
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
    else if (arg == "--linear")
    {
      options.arith_linear = true;
    }
    else if (arg == "--strings")
    {
      options.enabled_theories.push_back(THEORY_STRING);
    }
    else if (arg == "--uf")
    {
      options.enabled_theories.push_back(THEORY_UF);
    }
    else
    {
      MURXLA_EXIT_ERROR(true) << "unknown option '" << arg << "'";
    }
  }

  MURXLA_EXIT_ERROR(options.solver.empty()) << "No solver selected";
}

/* -------------------------------------------------------------------------- */
/* Solver option parsing                                                      */
/* -------------------------------------------------------------------------- */

template <class T>
std::pair<T, T>
get_limits(const toml::table& table)
{
  T min = (table.find("min") != table.end()) ? toml::get<T>(table.at("min"))
                                             : std::numeric_limits<T>::min();
  T max = (table.find("max") != table.end()) ? toml::get<T>(table.at("max"))
                                             : std::numeric_limits<T>::max();
  return std::make_pair(min, max);
}

void
parse_solver_options_file(Options& options, SolverOptions& solver_options)
{
  const auto options_data = toml::parse(options.solver_options_file);
  const std::vector<toml::table> tables =
      toml::find<std::vector<toml::table>>(options_data, "option");

  std::unordered_map<std::string, SolverOption*> options_map;

  SolverOption* opt;
  for (const toml::table& table : tables)
  {
    std::string name = toml::get<std::string>(table.at("name"));
    std::string type = toml::get<std::string>(table.at("type"));
    std::vector<std::string> depends =
        toml::get<std::vector<std::string>>(table.at("depends"));
    std::vector<std::string> conflicts =
        toml::get<std::vector<std::string>>(table.at("conflicts"));

    if (type == "bool")
    {
      opt = new SolverOptionBool(name, depends, conflicts);
    }
    else if (type == "int" || type == "int16_t" || type == "int32_t"
             || type == "int64_t")
    {
      int64_t min, max;
      if (type == "int16_t")
      {
        std::tie(min, max) = get_limits<int16_t>(table);
      }
      else if (type == "int64_t")
      {
        std::tie(min, max) = get_limits<int64_t>(table);
      }
      else
      {
        std::tie(min, max) = get_limits<int32_t>(table);
      }
      opt = new SolverOptionNum<int64_t>(name, depends, conflicts, min, max);
    }
    else if (type == "unsigned" || type == "unsigned long" || type == "uint16_t"
             || type == "uint32_t" || type == "uint64_t")
    {
      uint64_t min, max;
      if (type == "uint16_t")
      {
        std::tie(min, max) = get_limits<uint16_t>(table);
      }
      else if (type == "uint64_t" || type == "unsigned long")
      {
        std::tie(min, max) = get_limits<uint64_t>(table);
      }
      else
      {
        std::tie(min, max) = get_limits<uint32_t>(table);
      }
      opt = new SolverOptionNum<uint64_t>(name, depends, conflicts, min, max);
    }
    else if (type == "double")
    {
      double min, max;
      std::tie(min, max) = get_limits<double>(table);
      opt = new SolverOptionNum<double>(name, depends, conflicts, min, max);
    }
    else if (type == "list")
    {
      std::vector<std::string> values =
          toml::get<std::vector<std::string>>(table.at("values"));
      opt = new SolverOptionList(name, depends, conflicts, values);
    }
    else
    {
      MURXLA_EXIT_ERROR(true) << "Unknown option type " << type;
    }

    solver_options.push_back(std::unique_ptr<SolverOption>(opt));
    options_map.emplace(std::make_pair(name, opt));
  }

  /* Check option names and propagate conflicts/dependencies to options_map. */
  for (const auto& uptr : solver_options)
  {
    const auto& confl = uptr->get_conflicts();
    const auto& deps  = uptr->get_depends();

    for (const auto& o : confl)
    {
      MURXLA_EXIT_ERROR(options_map.find(o) == options_map.end())
          << "Unknown conflicting option name '" << o << "' for option "
          << uptr->get_name();
      options_map.at(o)->add_conflict(uptr->get_name());
    }

    for (const auto& o : deps)
    {
      MURXLA_EXIT_ERROR(options_map.find(o) == options_map.end())
          << "Unknown dependency option name '" << o << "' for option "
          << uptr->get_name();
      options_map.at(o)->add_depends(uptr->get_name());
    }
  }
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
  bool is_cross      = !options.cross_check.empty();
  bool is_forked     = options.dd || is_continuous;

  create_tmp_directory(options.tmp_dir);

  if (!options.solver_options_file.empty())
  {
    parse_solver_options_file(options, solver_options);
  }

  std::string smt2_file_name      = options.smt2_file_name;
  std::string api_trace_file_name = options.api_trace_file_name;

  try
  {
    if (is_continuous)
    {
      set_sigint_handler_stats();
      Murxla murxla(stats, options, &solver_options, &g_errors, TMP_DIR);
      murxla.test();
    }
    else
    {
      std::string api_trace_file_name = options.api_trace_file_name;
      std::string dd_trace_file_name  = options.dd_trace_file_name;
      std::string out_file_name = DEVNULL;
      std::string err_file_name = DEVNULL;

      if (options.dd && dd_trace_file_name.empty()
          && api_trace_file_name.empty())
      {
        /* When delta-debugging, trace into file instead of stdout. */
        api_trace_file_name = get_tmp_file_path("tmp.trace", TMP_DIR);
        /* Minimized trace file name. */
        if (is_untrace)
        {
          dd_trace_file_name = prepend_prefix_to_file_name(
              Murxla::DD_PREFIX, options.untrace_file_name);
          MURXLA_MESSAGE_DD << "minimizing untraced file '"
                            << options.untrace_file_name.c_str() << "'";
        }
        else
        {
          std::stringstream ss;
          ss << Murxla::DD_PREFIX << options.seed << ".trace";
          dd_trace_file_name = ss.str();
          MURXLA_MESSAGE_DD << "minimizing run with seed " << options.seed;
        }
      }

      if (is_cross)
      {
        if (api_trace_file_name.empty())
        {
          /* When cross checking, we don't want to pollute stdout with the api
           * trace, we need it to only contain the check-sat answers. */
          api_trace_file_name = DEVNULL;
        }
        /* When cross checking, check-sat answers and the error output of
         * solver must be recorded for the actual cross check. */
        out_file_name = get_tmp_file_path("tmp.out", TMP_DIR);
        err_file_name = get_tmp_file_path("tmp.err", TMP_DIR);
      }
      else if (options.solver == Murxla::SOLVER_SMT2
               && options.smt2_file_name.empty())
      {
        /* We always dump .smt2 if the SMT2 solver is enabled. If no file name
         * given, we use a generic (but unique) file name. */
        options.smt2_file_name =
            get_smt2_file_name(options.seed, options.untrace_file_name);
        if (!options.out_dir.empty())
        {
          options.smt2_file_name =
              prepend_path(options.out_dir, options.smt2_file_name);
        }
      }

      Murxla murxla(stats, options, &solver_options, &g_errors, TMP_DIR);

      (void) murxla.run(out_file_name,
                        err_file_name,
                        api_trace_file_name,
                        options.untrace_file_name,
                        is_forked,
                        api_trace_file_name.empty()
                            ? Murxla::TraceMode::TO_STDOUT
                            : Murxla::TraceMode::TO_FILE);

      if (options.dd)
      {
        murxla.dd(api_trace_file_name, dd_trace_file_name);
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
