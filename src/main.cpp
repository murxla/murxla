#include <fcntl.h>
#include <stdarg.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include <fstream>
#include <iostream>
#include <sstream>

#include "btor_solver.hpp"
#include "cvc4_solver.hpp"
#include "fsm.hpp"

using namespace smtmbt;

struct Options
{
  uint32_t seed      = 0;
  bool seeded        = false;
  uint32_t verbosity = 0;
  uint32_t time      = 0;

  bool use_btor   = false;
  bool use_cvc4   = false;
  char* api_trace = nullptr;
  char* untrace   = nullptr;
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

#ifdef SMTMBT_USE_BOOLECTOR
void
test_btor_smgr(RNGenerator& rng)
{
#if 0
  btor::BtorSolverManager smgr(rng);

  smgr.set_solver(boolector_new());
  Btor* btor = smgr.get_solver();

  BoolectorSort bv32 = boolector_bitvec_sort(btor, 32);
  BoolectorSort bv31 = boolector_bitvec_sort(btor, 31);
  BoolectorNode* x = boolector_var(btor, bv32, "x");
  BoolectorNode* y = boolector_var(btor, bv31, "y");
  BoolectorNode* z = boolector_var(btor, bv32, "z");

#if 1
  smgr.add_term(x, THEORY_BV);
  smgr.add_term(y, THEORY_BV);
  smgr.add_term(y, THEORY_BV);
  smgr.add_term(z, THEORY_BV);

  BoolectorNode* n0 = smgr.pick_term(bv32);
  BoolectorNode* n1 = smgr.pick_term(bv32);

  BoolectorNode* eq = boolector_eq(btor, n0, n1);
  smgr.add_term(eq, THEORY_BOOL);

  BoolectorNode *n2 = smgr.pick_term(THEORY_BOOL);
  BoolectorNode *n3 = smgr.pick_term(THEORY_BOOL);
  BoolectorNode *a = boolector_and(btor, n2, n3);
  smgr.add_term(a, THEORY_BOOL);

#endif

  boolector_release_sort(btor, bv32);
  boolector_release_sort(btor, bv31);
  boolector_release(btor, x);
  boolector_release(btor, y);
  boolector_release(btor, z);
  boolector_release(btor, eq);
  boolector_release(btor, a);
#endif
}

void
test_btor_fsm(RNGenerator& rng)
{
#if 0
  btor::BtorSolverManager smgr(rng);
  smgr.set_solver(boolector_new());
  smgr.run();
#endif
}
#endif

#ifdef SMTMBT_USE_CVC4
void
test_cvc4_smgr(RNGenerator& rng)
{
#if 0
  cvc4::CVC4SolverManager smgr(rng);

  smgr.set_solver(new CVC4::api::Solver());
  CVC4::api::Solver* cvc4 = smgr.get_solver();

  CVC4::api::Sort bv32 = cvc4->mkBitVectorSort(32);
  CVC4::api::Sort bv31 = cvc4->mkBitVectorSort(31);
  CVC4::api::Term x    = cvc4->mkVar(bv32, "x");
  CVC4::api::Term y    = cvc4->mkVar(bv32, "y");

#if 1
  smgr.add_sort(bv32, THEORY_BV);
  smgr.add_sort(bv31, THEORY_BV);

  smgr.add_term(x, THEORY_BV);
  smgr.add_term(y, THEORY_BV);
#endif
#endif
}

void
test_cvc4_fsm(RNGenerator& rng)
{
#if 0
  cvc4::CVC4SolverManager smgr(rng);
  smgr.set_solver(new CVC4::api::Solver());
  smgr.run();
#endif
}
#endif

void
test()
{
#if 0
  RNGenerator rng;
#ifdef SMTMBT_USE_BOOLECTOR
  test_btor_smgr(rng);
  test_btor_fsm(rng);
#endif
#ifdef SMTMBT_USE_CVC4
  test_cvc4_smgr(rng);
  test_cvc4_fsm(rng);
#endif
#endif
}

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
  "  --btor                  test Boolector\n"                      \
  "  --cvc4                  test CVC4\n"

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

    if (arg == "-s" || arg == "--seed")
    {
      std::stringstream ss;
      i += 1;
      if (i >= argc)
      {
        std::stringstream es;
        es << "missing argument to option '" << argv[i - 1] << "'";
        die(es.str());
      }
      ss << argv[i];
      if (ss.str().find('-') != std::string::npos)
      {
        std::stringstream es;
        es << "invalid argument to option '" << argv[i - 1]
           << "': " << ss.str();
        die(es.str());
      }
      ss >> g_options.seed;
    }

    if (arg == "-t" || arg == "--time")
    {
      std::stringstream ss;
      i += 1;
      if (i >= argc)
      {
        std::stringstream es;
        es << "missing argument to " << argv[i - 1];
        die(es.str());
      }
      ss << argv[i];
      if (ss.str().find('-') != std::string::npos)
      {
        std::stringstream es;
        es << "invalid argument to " << argv[i - 1] << ": " << ss.str();
        die(es.str());
      }
      ss >> g_options.time;
    }

    if (arg == "-v" || "--verbosity")
    {
      g_options.verbosity += 1;
    }

    if (arg == "-a" || arg == "--api-trace")
    {
      i += 1;
      if (i >= argc)
      {
        std::stringstream es;
        es << "missing argument to " << argv[i - 1];
        die(es.str());
      }
      g_options.api_trace = argv[i];
    }

    if (arg == "-u" || arg == "--untrace")
    {
      i += 1;
      if (i >= argc)
      {
        std::stringstream es;
        es << "missing argument to " << argv[i - 1];
        die(es.str());
      }
      g_options.untrace = argv[i];
    }

    if (arg == "--btor")
      if (arg == "--btor")
      {
        g_options.use_btor = true;
      }

    if (arg == "--cvc4")
    {
      g_options.use_cvc4 = true;
    }
  }

  if (!options.use_btor && !options.use_cvc4)
  {
    die("No solver selected");
  }
}

static Result
run(uint32_t seed, Options& options)
{
  int status, devnull;
  Result result;
  pid_t pid = 0;
  std::streambuf* trace_buf;
  std::ofstream trace_file;

  if (g_options.api_trace)
  {
    trace_file.open(g_options.api_trace);
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
  if (!g_options.untrace && options.seed == 0)
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
    if (g_options.time)
    {
      set_alarm();
    }

    if (!g_options.untrace && options.seed == 0)
    {
      set_signal_handlers();
      /* redirect stdout and stderr of child process to /dev/null */
      devnull = open("/dev/null", O_WRONLY);
      dup2(devnull, STDOUT_FILENO);
      dup2(devnull, STDERR_FILENO);
      close(devnull);
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

    FSM fsm(rng, solver, trace);

    /* replay/untrace given API trace */
    if (g_options.untrace)
    {
      std::ifstream untrace;
      untrace.open(g_options.untrace);
      fsm.untrace(untrace);
      untrace.close();
    }
    /* regular MBT run */
    else
    {
      fsm.configure();
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

int
main(int argc, char* argv[])
{
  //  test();

  uint32_t seed, num_runs = 0;
  char* env_file_name = nullptr;

  parse_options(g_options, argc, argv);

  bool is_seeded = g_options.seed > 0;
  SeedGenerator sg(g_options.seed);

  if ((env_file_name = getenv("SMTMBTAPITRACE")))
  {
    unsetenv("SMTMBTAPITRACE");
  }

  do
  {
    seed = sg.next();

    if (!is_seeded && !g_options.untrace)
    {
      std::cout << num_runs++ << " " << seed << std::flush;
    }

    /* we do not trace into file by default, only on replay in case of an error
     * (see below) */
    Result res = run(seed, g_options);

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
    if (!info.str().empty())
    {
      std::cout << info.str() << std::endl << std::flush;
    }
    std::cout << res << std::endl;

    /* replay and trace on error if not in untrace mode */
    if (!g_options.untrace && res != RESULT_OK && res != RESULT_TIMEOUT)
    {
      if (g_options.api_trace == nullptr)
      {
        if (!env_file_name)
        {
          std::stringstream ss;
          ss << "smtmbt-" << seed << ".trace";
          g_options.api_trace =
              strndup(ss.str().c_str(), ss.str().length() + 1);
        }
        else
        {
          g_options.api_trace = env_file_name;
        }
      }
      setenv("SMTMBTAPITRACE", g_options.api_trace, 1);
      Result res_replay = run(seed, g_options);
      assert(res == res_replay);
      unsetenv("SMTMBTAPITRACE");
      if (!env_file_name)
      {
        free(g_options.api_trace);
        g_options.api_trace = nullptr;
      }
    }
    std::cout << "\r" << std::flush;
  } while (!is_seeded);

  return 0;
}
