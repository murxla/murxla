#include <fcntl.h>
#include <stdarg.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include <fstream>
#include <iostream>
#include <sstream>
#include <toml.hpp>

#include "btor_solver.hpp"
#include "cvc4_solver.hpp"
#include "fsm.hpp"
#include "solver_option.hpp"

using namespace smtmbt;

struct Options
{
  uint32_t seed      = 0;
  uint32_t verbosity = 0;
  uint32_t time      = 0;

  bool use_btor    = false;
  bool use_cvc4    = false;
  bool trace_seeds = false;
  std::string api_trace;
  std::string untrace_file;
  bool dd = false;
  std::string dd_trace;
  std::string solver_options_file;
};

static Options g_options;

enum Result
{
  RESULT_ERROR,
  RESULT_OK,
  RESULT_SIGNAL,
  RESULT_TIMEOUT,
  RESULT_UNKNOWN,
};

enum ExitCodes
{
  EXIT_ERROR,
  EXIT_OK,
  EXIT_TIMEOUT,
};

/*****************************************************************************/

static void
warn(const char* msg, ...)
{
  assert(msg);
  va_list list;
  va_start(list, msg);
  fprintf(stdout, "[smtmbt] ");
  vfprintf(stdout, msg, list);
  fprintf(stdout, "\n");
  va_end(list);
  fflush(stdout);
}

static void
warn(const std::string& msg)
{
  warn(msg.c_str());
}

static void
die(const std::string& msg)
{
  warn(msg);
  exit(EXIT_ERROR);
}

/*****************************************************************************/

static void (*sig_int_handler)(int32_t);
static void (*sig_segv_handler)(int32_t);
static void (*sig_abrt_handler)(int32_t);
static void (*sig_term_handler)(int32_t);
static void (*sig_bus_handler)(int32_t);
static void (*sig_alrm_handler)(int32_t);

static void
reset_signal_handlers(void)
{
  (void) signal(SIGINT, sig_int_handler);
  (void) signal(SIGSEGV, sig_segv_handler);
  (void) signal(SIGABRT, sig_abrt_handler);
  (void) signal(SIGTERM, sig_term_handler);
  (void) signal(SIGBUS, sig_bus_handler);
}

static void
catch_signal(int32_t signal)
{
  static int32_t caught_signal = 0;
  if (!caught_signal)
  {
    caught_signal = signal;
  }
  reset_signal_handlers();
  raise(signal);
  exit(EXIT_ERROR);
}

static void
set_signal_handlers(void)
{
  sig_int_handler  = signal(SIGINT, catch_signal);
  sig_segv_handler = signal(SIGSEGV, catch_signal);
  sig_abrt_handler = signal(SIGABRT, catch_signal);
  sig_term_handler = signal(SIGTERM, catch_signal);
  sig_bus_handler  = signal(SIGBUS, catch_signal);
}

static void
reset_alarm(void)
{
  alarm(0);
  (void) signal(SIGALRM, sig_alrm_handler);
}

static void
catch_alarm(int32_t signal)
{
  (void) signal;
  assert(signal == SIGALRM);
  reset_alarm();
  exit(EXIT_TIMEOUT);
}

static void
set_alarm(void)
{
  sig_alrm_handler = signal(SIGALRM, catch_alarm);
  assert(g_options.time > 0);
  alarm(g_options.time);
}

/*****************************************************************************/

#define SMTMBT_USAGE                                                \
  "smtmbt: a model-based tester for SMT solvers\n"                  \
  "usage:\n"                                                        \
  "  smtmbt [options]\n\n"                                          \
  "  -h, --help              print this message and exit\n"         \
  "  -s, --seed <int>        seed for random number generator\n"    \
  "  -t, --time <int>        time limit for MBT runs\n"             \
  "  -v, --verbosity         increase verbosity\n"                  \
  "  -a, --api-trace <file>  trace API call sequence into <file>\n" \
  "  -u, --untrace <file>    replay given API call sequence\n"      \
  "  -o, --options <file>    solver option model toml file\n"       \
  "  --btor                  test Boolector\n"                      \
  "  --cvc4                  test CVC4\n"

void
check_next_arg(std::string& option, int i, int argc)
{
  if (i >= argc)
  {
    std::stringstream es;
    es << "missing argument to option '" << option << "'";
    die(es.str());
  }
}

void
parse_options(Options& options, int argc, char* argv[])
{
  for (int i = 1; i < argc; i++)
  {
    std::string arg = argv[i];
    if (arg == "-h" || arg == "--help")
    {
      std::cout << SMTMBT_USAGE << std::endl;
      exit(0);
    }
    else if (arg == "-s" || arg == "--seed")
    {
      std::stringstream ss;
      i += 1;
      check_next_arg(arg, i, argc);
      ss << argv[i];
      if (ss.str().find('-') != std::string::npos)
      {
        std::stringstream es;
        es << "invalid argument to option '" << argv[i - 1]
           << "': " << ss.str();
        die(es.str());
      }
      ss >> options.seed;
    }
    else if (arg == "-t" || arg == "--time")
    {
      std::stringstream ss;
      i += 1;
      check_next_arg(arg, i, argc);
      ss << argv[i];
      if (ss.str().find('-') != std::string::npos)
      {
        std::stringstream es;
        es << "invalid argument to " << argv[i - 1] << ": " << ss.str();
        die(es.str());
      }
      ss >> options.time;
    }
    else if (arg == "-v" || arg == "--verbosity")
    {
      options.verbosity += 1;
    }
    else if (arg == "-a" || arg == "--api-trace")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.api_trace = argv[i];
    }
    else if (arg == "-u" || arg == "--untrace")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.untrace_file = argv[i];
    }
    else if (arg == "--btor")
    {
      options.use_btor = true;
    }
    else if (arg == "--cvc4")
    {
      options.use_cvc4 = true;
    }
    else if (arg == "-o" || arg == "--options")
    {
      i += 1;
      check_next_arg(arg, i, argc);
      options.solver_options_file = std::string(argv[i]);
    }
    else if (arg == "-S" || arg == "--trace-seeds")
    {
      options.trace_seeds = true;
    }
  }

  if (!options.use_btor && !options.use_cvc4)
  {
    die("No solver selected");
  }
}

static Result
run(uint32_t seed,
    Options& options,
    SolverOptions& solver_options,
    bool run_forked,
    std::string file_out,
    std::string file_err)
{
  bool untrace = !options.untrace_file.empty();
  int32_t status, fd;
  Result result;
  pid_t pid = 0;
  std::streambuf* trace_buf;
  std::ofstream trace_file;

  if (!options.api_trace.empty())
  {
    trace_file.open(options.api_trace);
    trace_buf = trace_file.rdbuf();
  }
  else
  {
    trace_buf = std::cout.rdbuf();
  }
  std::ostream trace(trace_buf);

  RNGenerator rng(seed);

  result = RESULT_UNKNOWN;

  /* If seeded run in main process. */
  if (run_forked)
  {
    pid = fork();
    if (pid == -1)
    {
      die("Fork failed.");
    }
  }

  /* parent */
  if (pid)
  {
    reset_alarm();
    wait(&status);
  }
  /* child */
  else
  {
    if (options.time)
    {
      set_alarm();
    }

    if (run_forked)
    {
      set_signal_handlers();
      /* redirect stdout and stderr of child process to /dev/null */
      fd = open(file_out.c_str(), O_CREAT | O_WRONLY, S_IRUSR | S_IWUSR);
      dup2(fd, STDOUT_FILENO);
      close(fd);
      fd = open(file_err.c_str(), O_CREAT | O_WRONLY, S_IRUSR | S_IWUSR);
      dup2(fd, STDERR_FILENO);
      close(fd);
    }

    Solver *solver= nullptr;

    if (options.use_btor)
    {
      solver = new btor::BtorSolver(rng);
    }
    else if (options.use_cvc4)
    {
      solver = new cvc4::CVC4Solver(rng);
    }

    FSM fsm(rng, solver, trace, solver_options, options.trace_seeds);
    fsm.configure();

    /* replay/untrace given API trace */
    if (untrace)
    {
      std::ifstream untrace_file;
      untrace_file.open(options.untrace_file);
      assert(untrace_file.is_open());
      fsm.untrace(untrace_file);
      untrace_file.close();
    }
    /* regular MBT run */
    else
    {
      fsm.run();
    }

    if (trace_file.is_open()) trace_file.close();
    exit(EXIT_OK);
  }

  if (WIFEXITED(status))
  {
    int exit_code = WEXITSTATUS(status);
    switch (exit_code)
    {
      case EXIT_OK: result = RESULT_OK; break;
      case EXIT_ERROR: result = RESULT_ERROR; break;
      case EXIT_TIMEOUT: result = RESULT_TIMEOUT; break;
      default: result = RESULT_UNKNOWN;
    }
  }
  else if (WIFSIGNALED(status))
  {
    result = RESULT_SIGNAL;
  }
  return result;
}

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
      std::stringstream es;
      es << "Unknown option type " << type;
      die(es.str());
    }

    solver_options.push_back(std::unique_ptr<SolverOption>(opt));
    options_map.emplace(std::make_pair(name, opt));
  }

  /* Check option names and propagate conflicts/dependencies to all options_map.
   */
  for (const auto& uptr : solver_options)
  {
    const auto& confl = uptr->get_conflicts();
    const auto& deps  = uptr->get_depends();

    for (const auto& o : confl)
    {
      if (options_map.find(o) == options_map.end())
      {
        std::stringstream es;
        es << "Unknown conflicting option name '" << o << "' for option "
           << uptr->get_name();
        die(es.str());
      }
      options_map.at(o)->add_conflict(uptr->get_name());
    }

    for (const auto& o : deps)
    {
      if (options_map.find(o) == options_map.end())
      {
        std::stringstream es;
        es << "Unknown dependency option name '" << o << "' for option "
           << uptr->get_name();
        die(es.str());
      }
      options_map.at(o)->add_depends(uptr->get_name());
    }
  }
}

int
main(int argc, char* argv[])
{
  uint32_t seed, num_runs = 0;
  char* env_file_name = nullptr;
  std::string devnull = "/dev/null";

  parse_options(g_options, argc, argv);

  SeedGenerator sg(g_options.seed);
  SolverOptions solver_options;
  bool is_seeded = g_options.seed > 0;
  bool is_untrace = !g_options.untrace_file.empty();
  bool is_forked;

  if (!g_options.solver_options_file.empty())
  {
    parse_solver_options_file(g_options, solver_options);
  }

  g_options.dd = true;
  is_forked    = g_options.dd || (!is_seeded && g_options.untrace_file.empty());

  if ((env_file_name = getenv("SMTMBTAPITRACE")))
  {
    unsetenv("SMTMBTAPITRACE");
  }

  do
  {
    seed = sg.next();

    if (is_forked)
    {
      std::cout << num_runs++ << " " << seed << std::flush;
    }

    /* We do not trace into file by default, only on replay in case of an error.
     * We also do not fork when a seed is given, or when untracing. */
    Result res =
        run(seed, g_options, solver_options, is_forked, devnull, devnull);

    /* report status */
    std::stringstream info;
    switch (res)
    {
      case RESULT_OK: break;
      case RESULT_ERROR: info << " error"; break;
      case RESULT_SIGNAL: info << " signal"; break;
      case RESULT_TIMEOUT:
        info << " timed out after " << g_options.time << " seconds ";
        break;
      default: assert(res == RESULT_UNKNOWN); info << " unknown";
    }
    if (info.str().empty())
    {
      std::cout << "\33[2K\r" << std::flush;
    }
    else
    {
      std::cout << info.str() << std::endl << std::flush;
    }
    std::cout << res;

    /* replay and trace on error */
    if (res != RESULT_OK && res != RESULT_TIMEOUT)
    {
      if (g_options.dd)
      {
        std::string gold_out_file_name  = "smtmbt-dd-gold-tmp.out";
        std::string gold_err_file_name  = "smtmbt-dd-gold-tmp.err";
        std::string tmp_out_file_name   = "smtmbt-dd-tmp.out";
        std::string tmp_err_file_name   = "smtmbt-dd-tmp.err";
        std::string tmp_trace_file_name = "smtmbt-dd-tmp.trace";

        Options o(g_options);
        o.verbosity = 0;
        o.api_trace = tmp_trace_file_name;
        o.dd        = false;
        o.dd_trace  = std::string();

        // golden run

        setenv("SMTMBTAPITRACE", o.api_trace.c_str(), 1);
        Result golden_res = run(seed,
                                o,
                                solver_options,
                                true,
                                gold_out_file_name,
                                gold_err_file_name);
        unsetenv("SMTMBTAPITRACE");

        // start delta debugging
      }
      else if (is_forked)
      {
        if (g_options.api_trace.empty())
        {
          if (!env_file_name)
          {
            std::stringstream ss;
            ss << "smtmbt-" << seed << ".trace";
            g_options.api_trace = ss.str();
          }
          else
          {
            g_options.api_trace = env_file_name;
          }
        }
        setenv("SMTMBTAPITRACE", g_options.api_trace.c_str(), 1);
        Result res_replay =
            run(seed, g_options, solver_options, true, devnull, devnull);
        assert(res == res_replay);
        unsetenv("SMTMBTAPITRACE");
        if (!env_file_name)
        {
          g_options.api_trace = "";
        }
      }
    }
    std::cout << "\r" << std::flush;
  } while (!is_seeded && !is_untrace);

  return 0;
}
