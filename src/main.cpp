#include <fcntl.h>
#include <stdarg.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <unistd.h>

#include <cstdlib>
#include <ctime>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <toml.hpp>

#include "btor_solver.hpp"
#include "cvc4_solver.hpp"
#include "exit.hpp"
#include "fsm.hpp"
#include "smt2_solver.hpp"
#include "solver_option.hpp"
#include "statistics.hpp"

using namespace smtmbt;
using namespace statistics;

#define SMTMBT_SOLVER_BTOR "btor"
#define SMTMBT_SOLVER_CVC4 "cvc4"
#define SMTMBT_SOLVER_SMT2 "smt2"

#define SMTMBT_SMT2_READ_END 0
#define SMTMBT_SMT2_WRITE_END 1

const std::string COLOR_BLUE    = "\33[94m";
const std::string COLOR_DEFAULT = "\33[39m";
const std::string COLOR_GREEN   = "\33[92m";
const std::string COLOR_RED     = "\33[91m";

const std::string DEVNULL = "/dev/null";

/* -------------------------------------------------------------------------- */

struct Options
{
  uint32_t seed      = 0;
  uint32_t verbosity = 0;
  double time        = 0;
  uint32_t max_runs  = 0;

  bool is_seeded      = false;
  bool trace_seeds = false;
  bool simple_symbols = false;
  bool smt         = false;
  bool print_stats = false;
  std::string solver;
  std::string solver_binary;
  std::string api_trace_file_name;
  std::string untrace_file_name;
  std::string smt2_file_name;
  bool dd = false;
  std::string dd_trace_file_name;
  std::string cross_check;
  std::string solver_options_file;
  TheoryIdVector enabled_theories;
};

static Options g_options;
static Statistics* g_stats;

enum Result
{
  RESULT_ERROR,
  RESULT_ERROR_CONFIG,
  RESULT_OK,
  RESULT_TIMEOUT,
  RESULT_UNKNOWN,
};

/* -------------------------------------------------------------------------- */

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
die(const std::string& msg, ExitCode exit_code = EXIT_ERROR)
{
  warn(msg);
  exit(exit_code);
}

static std::string
get_info(Result res)
{
  std::stringstream info;
  switch (res)
  {
    case RESULT_OK: info << " ok"; break;
    case RESULT_ERROR: info << " error"; break;
    case RESULT_ERROR_CONFIG: info << " config error"; break;
    case RESULT_TIMEOUT: info << " timeout"; break;
    default: assert(res == RESULT_UNKNOWN); info << " unknown";
  }
  return info.str();
}

static double
get_cur_wall_time()
{
  struct timeval time;
  if (gettimeofday(&time, nullptr))
  {
    die("failed to get time");
  }
  return (double) time.tv_sec + (double) time.tv_usec / 1000000;
}

static Statistics*
initialize_statistics()
{
  int fd;
  std::stringstream ss;
  std::string shmfilename;
  Statistics* stats;

  ss << "/tmp/smtmbt-shm-" << getpid();
  shmfilename = ss.str();

  if ((fd = open(shmfilename.c_str(), O_RDWR | O_CREAT, S_IRWXU)) < 0)
    die("failed to create shared memory file for statistics");

  stats = static_cast<Statistics*>(mmap(0,
                                        sizeof(Statistics),
                                        PROT_READ | PROT_WRITE,
                                        MAP_ANONYMOUS | MAP_SHARED,
                                        fd,
                                        0));

  if (close(fd)) die("failed to close shared memory file for statistics");
  (void) unlink(shmfilename.c_str());
  return stats;
}

static std::ifstream
open_ifile(std::string& file_name)
{
  std::ifstream res(file_name);
  if (!res.is_open())
  {
    std::stringstream ss;
    ss << "unable to open file " << file_name;
    die(ss.str());
  }
  return res;
}

static std::ofstream
open_ofile(std::string& file_name)
{
  std::ofstream res(file_name, std::ofstream::out | std::ofstream::trunc);
  if (!res.is_open())
  {
    std::stringstream ss;
    ss << "unable to open file " << file_name;
    die(ss.str());
  }
  return res;
}

static bool
compare_files(std::string file_name1, std::string file_name2)
{
  std::ifstream file1(file_name1, std::ifstream::binary | std::ifstream::ate);
  std::ifstream file2(file_name2, std::ifstream::binary | std::ifstream::ate);

  if (file1.fail() || file2.fail())
  {
    return false;
  }

  if (file1.tellg() != file2.tellg())
  {
    return false;
  }

  file1.seekg(0, file1.beg);
  file2.seekg(0, file2.beg);
  return std::equal(std::istreambuf_iterator<char>(file1.rdbuf()),
                    std::istreambuf_iterator<char>(),
                    std::istreambuf_iterator<char>(file2.rdbuf()));
}

static void
diff_files(std::ostream& out, std::string file_name1, std::string file_name2)
{
  std::ifstream file1 = open_ifile(file_name1);
  std::ifstream file2 = open_ifile(file_name2);
  std::string line1, line2;

  while (std::getline(file1, line1))
  {
    if (std::getline(file2, line2))
    {
      if (line1 == line2)
      {
        out << COLOR_DEFAULT << "  ";
      }
      else
      {
        out << COLOR_RED << "x ";
      }
      out << std::left << std::setw(9) << line1;
      out << std::left << std::setw(9) << line2;
    }
    else
    {
      out << COLOR_RED << "x ";
      out << std::left << std::setw(9) << line1;
    }
    out << std::endl;
  }
  while (std::getline(file2, line2))
  {
    out << COLOR_RED << "x ";
    out << std::left << std::setw(9) << " ";
    out << std::left << std::setw(9) << line2 << std::endl;
  }
  out << COLOR_DEFAULT << std::flush;
  file1.close();
  file2.close();
}

/* -------------------------------------------------------------------------- */
/* Signal handling                                                            */
/* -------------------------------------------------------------------------- */

/* Signal handler for printing statistics */
// TODO: Remove handler
static void (*sig_int_handler_stats)(int32_t);

static void
catch_signal_stats(int32_t sig)
{
  static int32_t caught_signal = 0;
  if (!caught_signal)
  {
    caught_signal = sig;
  }
  (void) signal(SIGINT, sig_int_handler_stats);
  raise(sig);
  exit(EXIT_ERROR);
}

static void
set_sigint_handler_stats(void)
{
  sig_int_handler_stats = signal(SIGINT, catch_signal_stats);
}

/* -------------------------------------------------------------------------- */
/* Help message                                                               */
/* -------------------------------------------------------------------------- */

#define SMTMBT_USAGE                                                           \
  "usage:\n"                                                                   \
  "  smtmbt [options]\n\n"                                                     \
  "  -h, --help                 print this message and exit\n"                 \
  "  -s, --seed <int>           seed for random number generator\n"            \
  "  -S, --trace-seeds          trace seed for each API call\n"                \
  "  -t, --time <double>        time limit for MBT runs\n"                     \
  "  -v, --verbosity            increase verbosity\n"                          \
  "  -d, --dd                   enable delta debugging\n"                      \
  "  -D, --dd-trace <file>      delta debug API trace into <file>\n"           \
  "  -a, --api-trace <file>     trace API call sequence into <file>\n"         \
  "  -u, --untrace <file>       replay given API call sequence\n"              \
  "  -o, --options <file>       solver option model toml file\n"               \
  "  -l, --smt-lib              generate SMT-LIB compliant traces only\n"      \
  "  -c, --cross-check <solver> cross check with <solver> (SMT-lib2 only)\n"   \
  "  -y, --simple-symbols       use symbols of the form '_sX'\n"               \
  "  -f, --smt2-out <file>      write --smt2 output to <file>\n"               \
  "  --btor                     test Boolector\n"                              \
  "  --cvc4                     test CVC4\n"                                   \
  "  --smt2 [<binary>]          dump SMT-LIB 2 (optionally to solver binary\n" \
  "                             via stdout)\n"                                 \
  "  --stats                    print statistics\n\n"                          \
  " enabling specific theories:\n"                                             \
  "  --arrays                   theory of arrays\n"                            \
  "  --bv                       theory of bit-vectors\n"                       \
  "  --fp                       theory of floating-points\n"                   \
  "  --quant                    quantifiers"

/* -------------------------------------------------------------------------- */
/* Command-line option parsing                                                */
/* -------------------------------------------------------------------------- */

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
      if (options.solver == SMTMBT_SOLVER_SMT2)
      {
        std::stringstream es;
        es << "option " << arg << " is incompatible with option --smt2";
        die(es.str());
      }
      i += 1;
      check_next_arg(arg, i, argc);
      std::string solver = argv[i];
      if (solver != "btor" && solver != "cvc4")
      {
        std::stringstream es;
        es << "invalid argument " << solver << " to option '" << arg << "'";
        die(es.str());
      }
      options.cross_check = solver;
    }
    else if (arg == "-y" || arg == "--simple-symbols")
    {
      options.simple_symbols = true;
    }
    else if (arg == "--btor")
    {
      options.solver = SMTMBT_SOLVER_BTOR;
    }
    else if (arg == "--cvc4")
    {
      options.solver = SMTMBT_SOLVER_CVC4;
    }
    else if (arg == "--smt2")
    {
      if (!options.cross_check.empty())
      {
        std::stringstream es;
        es << "option " << arg << " is incompatible with option -c, --cross-check";
        die(es.str());
      }
      options.solver = SMTMBT_SOLVER_SMT2;
      if (i + 1 < argc && argv[i + 1][0] != '-')
      {
        i += 1;
        options.solver_binary = argv[i];
      }
    }
    else if (arg == "-f" || arg == "--smt2-out")
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
    else if (arg == "--quant")
    {
      options.enabled_theories.push_back(THEORY_QUANT);
    }
  }

  if (options.solver.empty())
  {
    die("No solver selected");
  }
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

/* -------------------------------------------------------------------------- */
/* Run MBT                                                                    */
/* -------------------------------------------------------------------------- */

static Result
run_aux(uint32_t seed,
        Options& options,
        SolverOptions& solver_options,
        bool run_forked,
        std::string file_out,
        std::string file_err,
        Statistics* stats)
{
  bool untrace = !options.untrace_file_name.empty();
  bool smt2_online = !options.solver_binary.empty();
  int32_t status, fd;
  Result result;
  pid_t solver_pid = 0, timeout_pid = 0;
  std::streambuf* trace_buf, *smt2_buf;
  std::ofstream trace_file;
  std::ofstream smt2_file;

  if (!options.api_trace_file_name.empty())
  {
    trace_file = open_ofile(options.api_trace_file_name);
    trace_buf = trace_file.rdbuf();
  }
  else
  {
    trace_buf = std::cout.rdbuf();
  }
  std::ostream trace(trace_buf);
  if (!options.smt2_file_name.empty())
  {
    smt2_file = open_ofile(options.smt2_file_name);
    smt2_buf = smt2_file.rdbuf();
  }
  else
  {
    smt2_buf = std::cout.rdbuf();
  }
  std::ostream smt2(smt2_buf);

  RNGenerator rng(seed);

  result = RESULT_UNKNOWN;

  /* If seeded run in main process. */
  if (run_forked)
  {
    solver_pid = fork();
    if (solver_pid == -1)
    {
      die("forking solver process failed.");
    }
  }

  /* parent */
  if (solver_pid)
  {
    /* If a time limit is given, fork another process that kills the solver_pid
     * after g_option.time seconds. (https://stackoverflow.com/a/8020324) */
    if (g_options.time)
    {
      timeout_pid = fork();
      if (timeout_pid == -1)
      {
        die("forking timeout process failed");
      }
      if (timeout_pid == 0)
      {
        usleep(g_options.time * 1000000);
        _exit(EXIT_OK);
      }
    }

    /* Wait for the first process to finish (solver_pid or timeout_pid). */
    pid_t exited_pid = wait(&status);

    if (exited_pid == solver_pid)
    {
      /* Kill and collect timeout process if solver process terminated first. */
      if (timeout_pid)
      {
        kill(timeout_pid, SIGKILL);
        waitpid(timeout_pid, nullptr, 0);
      }
      if (WIFEXITED(status))
      {
        switch (WEXITSTATUS(status))
        {
          case EXIT_OK: result = RESULT_OK; break;
          case EXIT_ERROR_CONFIG: result = RESULT_ERROR_CONFIG; break;
          default:
            assert(WEXITSTATUS(status) == EXIT_ERROR);
            result = RESULT_ERROR;
        }
      }
      else if (WIFSIGNALED(status))
      {
        result = RESULT_ERROR;
      }
    }
    else
    {
      /* Kill and collect solver process if time limit is exceeded. */
      assert(timeout_pid);
      kill(solver_pid, SIGKILL);
      waitpid(solver_pid, nullptr, 0);
      result = RESULT_TIMEOUT;
    }
  }
  /* child */
  else
  {
    int32_t fd_to[2], fd_from[2];
    FILE *to_external = nullptr, *from_external = nullptr;
    pid_t smt2_pid = 0;

    if (run_forked)
    {
      /* Redirect stdout and stderr of child process into given files. */
      fd = open(
          file_out.c_str(), O_CREAT | O_WRONLY | O_TRUNC, S_IRUSR | S_IWUSR);
      dup2(fd, STDOUT_FILENO);
      close(fd);
      fd = open(
          file_err.c_str(), O_CREAT | O_WRONLY | O_TRUNC, S_IRUSR | S_IWUSR);
      dup2(fd, STDERR_FILENO);
      close(fd);
    }

    Solver *solver= nullptr;

    if (options.solver == SMTMBT_SOLVER_BTOR)
    {
      solver = new btor::BtorSolver(rng);
    }
    else if (options.solver == SMTMBT_SOLVER_CVC4)
    {
      solver = new cvc4::CVC4Solver(rng);
    }
    else if (options.solver == SMTMBT_SOLVER_SMT2)
    {
      if (smt2_online)
      {
        /* Open input/output pipes from and to the external online solver. */
        if (pipe(fd_to) != 0 || pipe(fd_from) != 0)
        {
          die("creating input and/or output pipes failed");
        }

        smt2_pid = fork();
        if (smt2_pid == -1)
        {
          die("forking solver process failed.");
        }

        if (smt2_pid == 0)  // child
        {
          close(fd_to[SMTMBT_SMT2_WRITE_END]);
          dup2(fd_to[SMTMBT_SMT2_READ_END], STDIN_FILENO);

          close(fd_from[SMTMBT_SMT2_READ_END]);
          /* Redirect stdout of external solver to write end. */
          dup2(fd_from[SMTMBT_SMT2_WRITE_END], STDOUT_FILENO);
          /* Redirect stderr of external solver to write end. */
          dup2(fd_from[SMTMBT_SMT2_WRITE_END], STDERR_FILENO);

          std::vector<std::string> args;
          std::string arg;
          std::stringstream ss(options.solver_binary);
          while (std::getline(ss, arg, ' '))
          {
            args.push_back(arg);
          }
          size_t n        = args.size();
          char** execargs = new char*[n + 1];
          for (size_t i = 0; i < n; ++i)
          {
            size_t m    = args[i].size() + 1;
            execargs[i] = new char[m];
            std::strncpy(execargs[i], args[i].c_str(), m);
          }
          execargs[n] = nullptr;

          execv(execargs[0], execargs);
          for (size_t i = 0; i < n; ++i)
          {
            delete[] execargs[i];
          }
          delete[] execargs;
          std::stringstream es;
          es << "'" << options.solver_binary << "' is not executable";
          die(es.str());
        }

        close(fd_to[SMTMBT_SMT2_READ_END]);
        to_external = fdopen(fd_to[SMTMBT_SMT2_WRITE_END], "w");
        close(fd_from[SMTMBT_SMT2_WRITE_END]);
        from_external = fdopen(fd_from[SMTMBT_SMT2_READ_END], "r");

        if (to_external == nullptr || from_external == nullptr)
        {
          die("opening read/write channels to external solver failed");
        }
      }
      solver = new smt2::Smt2Solver(
          rng, smt2, smt2_online, to_external, from_external);
    }

    FSM fsm(rng,
            solver,
            trace,
            solver_options,
            options.trace_seeds,
            !options.cross_check.empty(),
            options.simple_symbols,
            options.smt,
            stats,
            options.enabled_theories);
    fsm.configure();

    try
    {
      /* replay/untrace given API trace */
      if (untrace)
      {
        fsm.untrace(options.untrace_file_name);
      }
      /* regular MBT run */
      else
      {
        fsm.run();
      }
    }
    catch (SmtMbtFSMConfigException& e)
    {
      die(e.get_msg(), EXIT_ERROR_CONFIG);
    }
    catch (SmtMbtFSMException& e)
    {
      die(e.get_msg());
    }

    if (smt2_online) waitpid(smt2_pid, nullptr, 0);

    if (trace_file.is_open()) trace_file.close();
    if (smt2_file.is_open()) smt2_file.close();

    if (run_forked)
    {
      _exit(EXIT_OK);
    }
    else
    {
      result = RESULT_OK;
    }
  }

  return result;
}

static Result
run(uint32_t seed,
    Options& options,
    SolverOptions& solver_options,
    bool run_forked,
    std::string file_out,
    std::string file_err,
    Statistics* stats)
{
  bool cross  = !options.cross_check.empty();
  bool forked = run_forked || cross;
  std::string tmp_file_out = "smtmbt-run-tmp1.out";
  std::string tmp_file_err = "smtmbt-run-tmp1.err";

  Result res = run_aux(
      seed, options, solver_options, forked, tmp_file_out, tmp_file_err, stats);

  if (cross)
  {
    std::streambuf *obuf, *ebuf;
    std::ofstream fout, ferr;

    if (options.dd)
    {
      fout.open(file_out);
      ferr.open(file_err);
      obuf = fout.rdbuf();
      ebuf = ferr.rdbuf();
    }
    else
    {
      obuf = std::cout.rdbuf();
      ebuf = std::cout.rdbuf();
    }
    std::ostream out(obuf), err(ebuf);

    SolverOptions csolver_options;  // not used for now
    std::string tmp_file_cross_out = "smtmbt-run-tmp2.out";
    std::string tmp_file_cross_err = "smtmbt-run-tmp2.err";

    Options coptions(options);
    coptions.solver = options.cross_check;

    Result cres = run_aux(seed,
                          coptions,
                          csolver_options,
                          forked,
                          tmp_file_cross_out,
                          tmp_file_cross_err,
                          stats);

    /* write result / error output to .err */
    if (res != cres)
    {
      err << options.solver << ":" << get_info(res) << std::endl;
      if (res == RESULT_ERROR)
      {
        std::ifstream tmp_err = open_ifile(tmp_file_err);
        err << tmp_err.rdbuf();
        tmp_err.close();
        err << std::endl;
      }
      err << options.cross_check << ":" << get_info(cres) << std::endl;

      if (cres == RESULT_ERROR)
      {
        std::ifstream tmp_err = open_ifile(tmp_file_cross_err);
        err << tmp_err.rdbuf();
        tmp_err.close();
      }
      res = RESULT_ERROR;
    }

    /* write output diff to .out */
    if (!compare_files(tmp_file_out, tmp_file_cross_out))
    {
      out << "output differs";
      if (options.dd)
      {
        out << std::endl;
      }
      else
      {
        out << ":" << std::endl;
        diff_files(out, tmp_file_out, tmp_file_cross_out);
      }
      res = RESULT_ERROR;
    }
    std::remove(tmp_file_cross_out.c_str());
    std::remove(tmp_file_cross_err.c_str());
  }
  else if (forked)
  {
    std::ofstream err = open_ofile(file_err);
    std::ofstream out = open_ofile(file_out);

    std::ifstream tmp_out = open_ifile(tmp_file_out);
    out << tmp_out.rdbuf();
    tmp_out.close();

    std::ifstream tmp_err = open_ifile(tmp_file_err);
    err << tmp_err.rdbuf();
    tmp_err.close();

    out.close();
    err.close();
  }
  std::remove(tmp_file_out.c_str());
  std::remove(tmp_file_err.c_str());
  return res;
}

/* -------------------------------------------------------------------------- */
/* Delta debug trace                                                          */
/* -------------------------------------------------------------------------- */

static void
write_idxs_to_file(const std::vector<std::string>& lines,
                   const std::vector<size_t> indices,
                   std::string& out_file_name)
{
  size_t size = lines.size();
  std::ofstream out_file = open_ofile(out_file_name);
  for (size_t idx : indices)
  {
    assert(idx < size);
    out_file << lines[idx] << std::endl;
  }
  out_file.close();
}

static std::vector<size_t>
remove_subsets(std::vector<std::vector<size_t>>& subsets,
               std::unordered_set<size_t>& excluded_sets)
{
  std::vector<size_t> res;

  for (size_t i = 0, n = subsets.size(); i < n; ++i)
  {
    if (excluded_sets.find(i) != excluded_sets.end()) continue;
    res.insert(res.end(), subsets[i].begin(), subsets[i].end());
  }
  return res;
}

static void
dd(uint32_t seed,
   Options& options,
   SolverOptions& solver_options,
   std::string& api_trace_file_name,
   std::string& untrace_file_name)
{
  assert(!api_trace_file_name.empty());

  std::string gold_out_file_name  = "smtmbt-dd-gold-tmp.out";
  std::string gold_err_file_name  = "smtmbt-dd-gold-tmp.err";
  std::string tmp_trace_file_name = "smtmbt-dd-tmp.trace";
  std::string tmp_out_file_name   = "smtmbt-dd-tmp.out";
  std::string tmp_err_file_name   = "smtmbt-dd-tmp.err";
  std::ifstream gold_out_file, gold_err_file;
  std::ofstream dd_trace_file;
  std::vector<std::string> lines;
  std::string line, token;
  Result gold_exit, exit;
  statistics::Statistics stats;

  /* init options object for golden (replay of original) run */
  Options o(options);
  o.verbosity           = 0;
  o.api_trace_file_name = tmp_trace_file_name;
  o.untrace_file_name   = api_trace_file_name;

  /* init trace file name for minimized trace */
  if (o.dd_trace_file_name.empty())
  {
    std::stringstream ss;
    if (untrace_file_name.empty())
    {
      if (api_trace_file_name.empty())
      {
        ss << "smtmbt-dd-" << seed << ".trace";
      }
      else
      {
        ss << "smtmbt-dd-" << api_trace_file_name;
      }
    }
    else
    {
      ss << "smtmbt-dd-" << options.untrace_file_name;
    }
    o.dd_trace_file_name = ss.str();
  }

  /* golden run */
  gold_exit = run(seed,
                  o,
                  solver_options,
                  true,
                  gold_out_file_name,
                  gold_err_file_name,
                  &stats);

  /* start delta debugging */

  /* represent input trace as vector of lines, trace statements that expect and
   * are accompanied by a return statement are represented as one element of
   * the vector */

  std::ifstream trace_file = open_ifile(tmp_trace_file_name);
  while (std::getline(trace_file, line))
  {
    if (line[0] == '#') continue;
    if (std::getline(std::stringstream(line), token, ' ') && token == "return")
    {
      std::stringstream ss;
      assert(lines.size() > 0);
      std::string prev = lines.back();
      ss << prev << std::endl << line;
      lines.pop_back();
      lines.push_back(ss.str());
    }
    else
    {
      lines.push_back(line);
    }
  }
  trace_file.close();

  /* while delta debugging, do not trace to file */
  o.api_trace_file_name = DEVNULL;
  o.untrace_file_name   = tmp_trace_file_name;

  int64_t size = lines.size();
  std::vector<size_t> superset(size);
  std::iota(superset.begin(), superset.end(), 0);
  int64_t subset_size = size / 2;
  uint32_t n_tests = 0, n_failed_tests = 0;
  while (subset_size > 0)
  {
    std::vector<std::vector<size_t>> subsets;
    auto begin = superset.begin();
    auto end   = superset.begin();
    for (int64_t lo = 0; end != superset.end(); lo += subset_size)
    {
      /* split original set into chunks of size 'subset_size' (last subset will
       * contain the remaining m > subset_size lines if 'subset_size' does not
       * divide 'size') */
      int64_t hi = lo + subset_size;
      end =
          hi > size || (size - hi) < subset_size ? superset.end() : begin + hi;
      std::vector<size_t> subset(begin + lo, end);
      subsets.push_back(subset);
    }
    assert(subsets.size() == (size_t) size / subset_size);

    std::vector<size_t> cur_superset;
    std::unordered_set<size_t> excluded_sets;
    for (size_t i = 0, n = subsets.size(); i < n; ++i)
    {
      std::unordered_set<size_t> ex(excluded_sets);
      ex.insert(i);
      std::vector<size_t> tmp = remove_subsets(subsets, ex);

      write_idxs_to_file(lines, tmp, tmp_trace_file_name);
      exit = run(seed,
                 o,
                 solver_options,
                 true,
                 tmp_out_file_name,
                 tmp_err_file_name,
                 &stats);
      n_tests += 1;
      if (exit == gold_exit
          && compare_files(tmp_out_file_name, gold_out_file_name)
          && compare_files(tmp_err_file_name, gold_err_file_name))
      {
        cur_superset = tmp;
        excluded_sets.insert(i);
        n_failed_tests += 1;
      }
    }
    if (cur_superset.empty())
    {
      subset_size = subset_size / 2;
    }
    else
    {
      /* write found subset immediately to file and continue */
      write_idxs_to_file(lines, cur_superset, o.dd_trace_file_name);
      superset    = cur_superset;
      size        = superset.size();
      subset_size = size / 2;
    }
  }
  std::cout << "[smtmbt] dd: tests " << n_failed_tests << "/" << n_tests
            << std::endl;
  std::cout << "[smtmbt] dd: " << o.dd_trace_file_name << std::endl;
  std::remove(gold_out_file_name.c_str());
  std::remove(gold_err_file_name.c_str());
  std::remove(tmp_trace_file_name.c_str());
  std::remove(tmp_out_file_name.c_str());
  std::remove(tmp_err_file_name.c_str());
}

/* ========================================================================== */

static std::string
get_api_trace_file_name(uint32_t seed,
                        bool is_dd,
                        std::string untrace_file_name = "")
{
  if (untrace_file_name.empty())
  {
    std::stringstream ss;
    ss << "smtmbt-" << seed << ".trace";
    return ss.str();
  }
  if (is_dd)
  {
    std::stringstream ss;
    ss << "smtmbt-dd-tmp-" << untrace_file_name;
    return ss.str();
  }
  return DEVNULL;
}

static std::string
get_smt2_file_name(uint32_t seed, std::string& untrace_file_name)
{
  std::stringstream ss;
  ss << "smtmbt-";
  if (untrace_file_name.empty())
  {
    ss << seed << ".smt2";
  }
  else
  {
    ss << untrace_file_name << ".smt2";
  }
  return ss.str();
}

static Result
replay(uint32_t seed,
       Options& options,
       SolverOptions& solver_options,
       std::string& api_trace_file_name,
       std::string& untrace_file_name,
       std::string& smt2_file_name,
       std::string& out_file_name,
       std::string& err_file_name)
{
  statistics::Statistics replay_stats;
  std::string tmp_trace_file_name;

  options.api_trace_file_name =
      api_trace_file_name.empty()
          ? get_api_trace_file_name(seed, options.dd, untrace_file_name)
          : api_trace_file_name;
  options.smt2_file_name =
      options.solver == SMTMBT_SOLVER_SMT2 && smt2_file_name.empty()
          ? get_smt2_file_name(seed, untrace_file_name)
          : smt2_file_name;

  Result res = run(seed,
                   options,
                   solver_options,
                   true,
                   out_file_name,
                   err_file_name,
                   &replay_stats);

  if (options.dd)
  {
    dd(seed, options, solver_options, api_trace_file_name, untrace_file_name);
  }
  else
  {
    std::cout << options.api_trace_file_name << std::endl;
  }
  options.api_trace_file_name = api_trace_file_name;
  options.smt2_file_name      = smt2_file_name;
  if (!tmp_trace_file_name.empty()) std::remove(tmp_trace_file_name.c_str());
  return res;
}

static void
test(Options& options, SolverOptions& solver_options, Statistics* stats)
{
  uint32_t num_runs         = 0;
  double start_time         = get_cur_wall_time();
  bool is_cross             = !options.cross_check.empty();
  std::string out_file_name = DEVNULL;
  std::string err_file_name = DEVNULL;
  SeedGenerator sg(options.seed);

  std::string smt2_file_name      = options.smt2_file_name;
  std::string api_trace_file_name = options.api_trace_file_name;

  do
  {
    uint32_t seed   = sg.next();
    double cur_time = get_cur_wall_time();

    std::cout << std::setw(10) << seed;
    std::cout << " " << std::setw(5) << num_runs++ << " runs";
    std::cout << " " << std::setw(8);
    std::cout << std::setprecision(2) << std::fixed;
    std::cout << num_runs / (cur_time - start_time) << " r/s";
    std::cout << " " << std::setw(4);
    std::cout << stats->d_results[Solver::Result::SAT] << " sat";
    std::cout << " " << std::setw(4);
    std::cout << stats->d_results[Solver::Result::UNSAT] << " unsat";
    std::cout << std::flush;

    if (is_cross)
    {
      options.api_trace_file_name = DEVNULL;
      out_file_name               = "smtmbt-tmp.out";
      err_file_name               = "smtmbt-tmp.err";
    }
    else if (options.solver == SMTMBT_SOLVER_SMT2)
    {
      if (!options.solver_binary.empty())
      {
        options.smt2_file_name = "";
      }
      else if (options.smt2_file_name.empty())
      {
        /* If no online solver is configured, we'll never run into the error
         * case below and replay (the Smt2Solver only answers 'unknown' and
         * dumps SMT2 -> should never terminate with an error).
         * We therefore dump every generated sequence to smt2 continuously. */
        options.smt2_file_name =
            get_smt2_file_name(seed, options.untrace_file_name);
      }
    }

    /* Run and test for error without tracing to trace file (we by default still
     * trace to stdout here, which is redirected to /dev/null).
     * If error encountered, replay and trace below. */
    Result res = run(seed,
                     options,
                     solver_options,
                     true,
                     out_file_name,
                     err_file_name,
                     stats);

    options.smt2_file_name = smt2_file_name;

    /* report status */
    if (res == RESULT_OK)
    {
      std::cout << "\33[2K\r" << std::flush;
    }
    else
    {
      std::stringstream info;
      info << " [";
      switch (res)
      {
        case RESULT_ERROR: info << COLOR_RED << "error"; break;
        case RESULT_TIMEOUT: info << COLOR_BLUE << "timeout"; break;
        default: assert(res == RESULT_UNKNOWN); info << "unknown";
      }
      info << COLOR_DEFAULT << "]";

      std::cout << info.str() << std::flush;
      if (res == RESULT_ERROR)
        std::cout << " ";
      else
        std::cout << std::endl;
    }

    /* Replay and trace on error.
     *
     * If SMT2 solver with online solver configured, dump smt2 on replay.
     * If SMT2 solver configured without an online solver, we'll never enter
     * here (the SMT2 solver should never return an error result). */
    if (res != RESULT_OK && res != RESULT_TIMEOUT)
    {
      Result res_replay = replay(seed,
                                 options,
                                 solver_options,
                                 api_trace_file_name,
                                 options.untrace_file_name,
                                 smt2_file_name,
                                 out_file_name,
                                 err_file_name);
      assert(res == res_replay);
    }
    std::cout << "\r" << std::flush;
  } while (options.max_runs == 0 || num_runs < options.max_runs);

  if (is_cross)
  {
    std::remove(out_file_name.c_str());
    std::remove(err_file_name.c_str());
  }
}

int
main(int argc, char* argv[])
{
  parse_options(g_options, argc, argv);

  SolverOptions solver_options;
  bool is_untrace    = !g_options.untrace_file_name.empty();
  bool is_continuous = !g_options.is_seeded && !is_untrace;
  bool is_cross      = !g_options.cross_check.empty();
  bool is_forked     = g_options.dd || is_continuous;

  if (!g_options.solver_options_file.empty())
  {
    parse_solver_options_file(g_options, solver_options);
  }

  g_stats = initialize_statistics();
  set_sigint_handler_stats();

  std::string smt2_file_name      = g_options.smt2_file_name;
  std::string api_trace_file_name = g_options.api_trace_file_name;

  if (is_continuous)
  {
    test(g_options, solver_options, g_stats);
  }
  else
  {
    std::string tmp_api_trace_file_name;
    std::string out_file_name = DEVNULL;
    std::string err_file_name = DEVNULL;

    if (g_options.dd && g_options.api_trace_file_name.empty())
    {
      /* When delta-debugging, we need to trace into file. */
      tmp_api_trace_file_name       = "smtmbt-tmp.trace";
      g_options.api_trace_file_name = tmp_api_trace_file_name;
    }

    if (is_cross)
    {
      if (g_options.api_trace_file_name.empty())
      {
        /* When cross checking, we don't want to pollute stdout with the api
         * trace, we need it to only contain the check-sat answers. */
        g_options.api_trace_file_name = DEVNULL;
      }
      /* When cross checking, check-sat answers and the error output of
       * solver must be recorded for the actual cross check. */
      out_file_name = "smtmbt-tmp.out";
      err_file_name = "smtmbt-tmp.err";
    }
    else if (g_options.solver == SMTMBT_SOLVER_SMT2
             && g_options.smt2_file_name.empty())
    {
      /* We always dump .smt2 if the SMT2 solver is enabled. If no file name
       * given, we use a generic (but unique) file name. */
      g_options.smt2_file_name =
          get_smt2_file_name(g_options.seed, g_options.untrace_file_name);
    }

    (void) run(g_options.seed,
               g_options,
               solver_options,
               is_forked,
               out_file_name,
               err_file_name,
               g_stats);

    if (g_options.dd)
    {
      dd(g_options.seed,
         g_options,
         solver_options,
         g_options.api_trace_file_name,
         g_options.untrace_file_name);
    }

    if (is_cross)
    {
      std::remove(out_file_name.c_str());
      std::remove(err_file_name.c_str());
    }

    if (!tmp_api_trace_file_name.empty())
    {
      std::remove(tmp_api_trace_file_name.c_str());
    }
  }

  if (g_options.print_stats) g_stats->print();

  if (munmap(g_stats, sizeof(Statistics)))
    die("failed to unmap shared memory for statistics");

  return 0;
}
