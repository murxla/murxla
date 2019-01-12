#include <iostream>

#include "btor_solver_manager.hpp"
#include "cvc4_solver_manager.hpp"
#include "fsm.hpp"

using namespace smtmbt;

#ifdef SMTMBT_USE_BOOLECTOR
void test_btor_smgr()
{
  btor::BtorSolverManager smgr;

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
test_btor_fsm()
{
  btor::BtorSolverManager smgr;
  smgr.set_solver(boolector_new());
  smgr.run();
}
#endif

#ifdef SMTMBT_USE_CVC4
void test_cvc4_smgr()
{
  cvc4::CVC4SolverManager smgr;

  smgr.set_solver(new CVC4::api::Solver());
  CVC4::api::Solver* cvc4 = smgr.get_solver();

  CVC4::api::Sort bv32 = cvc4->mkBitVectorSort(32);
  CVC4::api::Sort bv31 = cvc4->mkBitVectorSort(31);
  CVC4::api::Term x = cvc4->mkVar("x", bv32);
  CVC4::api::Term y = cvc4->mkVar("y", bv32);

#if 1
  smgr.add_sort(bv32, THEORY_BV);
  smgr.add_sort(bv31, THEORY_BV);

  smgr.add_term(x, THEORY_BV);
  smgr.add_term(y, THEORY_BV);
#endif
}

void
test_cvc4_fsm()
{
  cvc4::CVC4SolverManager smgr;
  smgr.set_solver(new CVC4::api::Solver());
  smgr.run();
}
#endif

int
main(int argc, char* argv[])
{
#ifdef SMTMBT_USE_BOOLECTOR
  test_btor_smgr();
  test_btor_fsm();
#endif
#ifdef SMTMBT_USE_CVC4
  test_cvc4_smgr();
  test_cvc4_fsm();
#endif
  return 0;
}
