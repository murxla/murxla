#include <fcntl.h>
#include <stdarg.h>
#include <sys/wait.h>
#include <unistd.h>
#include <iostream>

#include <cxxopts.hpp>

#include "btor_solver_manager.hpp"
#include "cvc4_solver_manager.hpp"
#include "fsm.hpp"
#include "options.hpp"

using namespace smtmbt;

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
}

void
test_btor_fsm(RNGenerator& rng)
{
  btor::BtorSolverManager smgr(rng);
  smgr.set_solver(boolector_new());
  smgr.run();
}
#endif

#ifdef SMTMBT_USE_CVC4
void
test_cvc4_smgr(RNGenerator& rng)
{
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
}

void
test_cvc4_fsm(RNGenerator& rng)
{
  cvc4::CVC4SolverManager smgr(rng);
  smgr.set_solver(new CVC4::api::Solver());
  smgr.run();
}
#endif

void
test()
{
  RNGenerator rng;
#ifdef SMTMBT_USE_BOOLECTOR
  test_btor_smgr(rng);
  test_btor_fsm(rng);
#endif
#ifdef SMTMBT_USE_CVC4
  test_cvc4_smgr(rng);
  test_cvc4_fsm(rng);
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

void
parse_options(Options& options, int argc, char* argv[])
{
  cxxopts::Options optparse("smtmbt",
                            "SMTMBT: Model-based tester for SMT solvers");

  std::string solver_name;

  /* clang-format off */
  optparse.add_options()

    ("h,help", "Show help message")

    ("s,seed", "Seed for random number generator",
     cxxopts::value<uint32_t>(options.seed))

    ("t,time", "Time limit for MBT runs",
     cxxopts::value<uint32_t>(options.time))

    ("v,verbosity", "Verbosity level",
     cxxopts::value<uint32_t>(options.verbosity))

    ("btor", "Test Boolector", cxxopts::value<bool>(options.use_btor))

    ("cvc4", "Test CVC4", cxxopts::value<bool>(options.use_cvc4))

    ;
  /* clang-format on */

  try
  {
    auto opts = optparse.parse(argc, argv);

    if (opts.count("help"))
    {
      std::cout << optparse.help() << std::endl;
      exit(0);
    }
  }
  catch (cxxopts::option_not_exists_exception& e)
  {
    die(e.what());
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

  RNGenerator rng(seed);

  result = RESULT_UNKNOWN;

  /* If seeded run in main process. */
  if (options.seed == 0)
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

    if (options.seed == 0)
    {
      /* redirect stdout and stderr of child process to /dev/null */
      devnull = open("/dev/null", O_WRONLY);
      dup2(devnull, STDOUT_FILENO);
      dup2(devnull, STDERR_FILENO);
      close(devnull);
    }

    if (options.use_btor)
    {
      btor::BtorSolverManager mgr(rng);
      mgr.set_rng(rng);
      mgr.run();
    }
    else if (options.use_cvc4)
    {
      cvc4::CVC4SolverManager mgr(rng);
      mgr.set_rng(rng);
      mgr.run();
    }

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

  switch (result)
  {
    case RESULT_OK: break;
    case RESULT_ERROR: std::cout << std::flush << " error" << std::endl; break;
    case RESULT_SIGNAL:
      std::cout << std::flush << " signal" << std::endl;
      break;
    case RESULT_TIMEOUT:
      std::cout << std::flush << " timed out after " << g_options.time
                << " seconds " << std::endl;
      break;
    default:
      assert(result == RESULT_UNKNOWN);
      std::cout << std::flush << " unknown" << std::endl;
  }

  return result;
}

int
main(int argc, char* argv[])
{
  //  test();

  Result res;

  parse_options(g_options, argc, argv);

  bool is_seeded = g_options.seed > 0;
  SeedGenerator sg(g_options.seed);
  uint32_t seed, num_runs = 0;
  do
  {
    seed = sg.next();
    std::cout << num_runs++ << " " << seed;
    res = run(seed, g_options);
    std::cout << "\r" << std::flush;
  } while (!is_seeded);

  return 0;
}
