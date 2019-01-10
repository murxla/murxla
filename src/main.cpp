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

  smgr.add_sort(bv32);
  smgr.add_sort(bv31);

  smgr.add_term(x);
  smgr.add_term(y);

  boolector_release_sort(btor, bv32);
  boolector_release_sort(btor, bv31);
  boolector_release(btor, x);
  boolector_release(btor, y);
}

void
test_btor_fsm()
{
  btor::BtorSolverManager smgr;
  smgr.set_solver(boolector_new());

  FSM fsm;
  State* snew    = fsm.new_state("new");
  State* sdelete = fsm.new_state("delete");
  fsm.set_init_state(snew);

#if 0
  btor::BtorActionNew* a_new       = smgr.new_action<btor::BtorActionNew>();
  btor::BtorActionDelete* a_delete = smgr.new_action<btor::BtorActionDelete>();
  snew->add_action(a_new, 10, sdelete);
  sdelete->add_action(a_delete, 10);
  sdelete->add_action(a_new, 10);
  fsm.check_states();
  fsm.run();
#endif
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

  smgr.add_sort(bv32);
  smgr.add_sort(bv31);

  smgr.add_term(x);
  smgr.add_term(y);
}

void
test_cvc4_fsm()
{
  cvc4::CVC4SolverManager smgr;
  smgr.set_solver(new CVC4::api::Solver());

  FSM fsm;
  State* snew    = fsm.new_state();
  State* sdelete = fsm.new_state();
  fsm.set_init_state(snew);

#if 0
  cvc4::CVC4ActionNew* a_new       = smgr.new_action<cvc4::CVC4ActionNew>();
  cvc4::CVC4ActionDelete* a_delete = smgr.new_action<cvc4::CVC4ActionDelete>();
  snew->add_action(a_new, 10, sdelete);
  sdelete->add_action(a_delete, 10);
  snew->add_action(a_new, 10);
  fsm.run();
#endif
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
