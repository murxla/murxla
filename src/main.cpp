#include <fcntl.h>
#include <sys/wait.h>
#include <unistd.h>
#include <iostream>

#include <cxxopts.hpp>

#include "btor_solver_manager.hpp"
#include "cvc4_solver_manager.hpp"
#include "fsm.hpp"
#include "options.hpp"

using namespace smtmbt;

enum Result
{
  RESULT_ERROR,
  RESULT_OK,
  RESULT_SIGNAL,
  RESULT_UNKNOWN,
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
  CVC4::api::Term x    = cvc4->mkVar("x", bv32);
  CVC4::api::Term y    = cvc4->mkVar("y", bv32);

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
die(const std::string& msg)
{
  std::cerr << msg << std::endl;
  exit(EXIT_FAILURE);
}

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
    wait(&status);
  }
  /* child */
  else
  {
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

    exit(EXIT_SUCCESS);
  }

  if (WIFEXITED(status))
  {
    int exit_code = WEXITSTATUS(status);
    result        = (exit_code == EXIT_SUCCESS) ? RESULT_OK : RESULT_ERROR;
  }
  else if (WIFSIGNALED(status))
  {
    result = RESULT_SIGNAL;
  }

  switch (result)
  {
    case RESULT_OK: break;
    case RESULT_ERROR: std::cout << std::flush << " error" << std::endl; break;
    case RESULT_SIGNAL: std::cout << std::flush <<" signal" << std::endl; break;
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
  Options options;

  parse_options(options, argc, argv);

  bool is_seeded = options.seed > 0;
  SeedGenerator sg(options.seed);
  uint32_t seed, num_runs = 0;
  do
  {
    seed = sg.next();
    std::cout << num_runs << " " << seed << "\r" << std::flush;
    res = run(seed, options);
  } while (!is_seeded);

  return 0;
}
