#include "btor_solver_manager.hpp"

#include <cassert>
#include <functional>
#include <iostream>

#include "util.hpp"

namespace smtmbt {
namespace btor {

/* -------------------------------------------------------------------------- */

class BtorAction : public Action
{
 public:
  BtorAction(BtorSolverManagerBase* smgr, const std::string& id)
      : Action(id), d_smgr(static_cast<BtorSolverManager*>(smgr))
  {
  }

 protected:
  BtorSolverManager* d_smgr;
};

/* -------------------------------------------------------------------------- */

class BtorActionNew : public BtorAction
{
 public:
  BtorActionNew(BtorSolverManagerBase* smgr) : BtorAction(smgr, "new") {}

  void run() override
  {
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    if (btor != nullptr) boolector_delete(btor);
    d_smgr->set_solver(boolector_new());
  }
  // void untrace(const char* s) override;
};

class BtorActionDelete : public BtorAction
{
 public:
  BtorActionDelete(BtorSolverManagerBase* smgr) : BtorAction(smgr, "delete") {}

  void run() override
  {
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    boolector_delete(btor);
    d_smgr->set_solver(nullptr);
  }
  // void untrace(const char* s) override;
};

/* -------------------------------------------------------------------------- */

size_t BoolectorNodeHashFunc::operator()(const BoolectorNode* n) const
{
  Btor* btor = boolector_get_btor(const_cast<BoolectorNode*>(n));
  int32_t id = boolector_get_id(btor, const_cast<BoolectorNode*>(n));
  return std::hash<int32_t>{}(id);
}

size_t BoolectorSortHashFunc::operator()(const BoolectorSort s) const
{
  return std::hash<BoolectorSort>{}(s);
}

/* -------------------------------------------------------------------------- */

BtorSolverManager::~BtorSolverManager()
{
  BoolectorSort sort;
  BtorSolverManager::TermMap tmap;
  for (auto& p : d_terms)
  {
    std::tie(sort, tmap) = p;
    boolector_release_sort(d_solver, sort);

    for (auto& p : tmap)
    {
      boolector_release(d_solver, p.first);
    }
  }
  if (d_solver != nullptr)
  {
    boolector_delete(d_solver);
  }
}

BoolectorNode* BtorSolverManager::copy_term(BoolectorNode* term)
{
  return boolector_copy(d_solver, term);
}

BoolectorSort BtorSolverManager::copy_sort(BoolectorSort sort)
{
  return boolector_copy_sort(d_solver, sort);
}

BoolectorSort BtorSolverManager::get_sort(BoolectorNode* term)
{
  return boolector_get_sort(d_solver, term);
}

void
BtorSolverManager::configure()
{
  /* Actions ................................................................ */
  auto anew    = new_action<BtorActionNew>();
  auto adelete = new_action<BtorActionDelete>();

  /* States ................................................................. */
  auto snew    = d_fsm.new_state("new");
  auto sdelete = d_fsm.new_state("delete");

  /* Transitions ............................................................ */
  snew->add_action(anew, 10, sdelete);
  sdelete->add_action(adelete, 10);

  /* Initial State .......................................................... */
  d_fsm.set_init_state(snew);
}

/* -------------------------------------------------------------------------- */

}  // namespace btor
}  // namespace smtmbt
