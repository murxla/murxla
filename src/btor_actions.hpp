#ifndef __SMTMBT__BTOR_ACTIONS_HPP_INCLUDED
#define __SMTMBT__BTOR_ACTIONS_HPP_INCLUDED

#ifdef SMTMBT_USE_BOOLECTOR

#include "btor_solver_manager.hpp"
#include "fsm.hpp"

namespace smtmbt {
namespace btor {

class BtorAction : public Action
{
 public:
  explicit BtorAction(BtorSolverManager* smgr, const char* id)
      : Action(id), d_smgr(smgr)
  {
  }

 protected:
  BtorSolverManager* d_smgr;
};

class BtorActionNew : public BtorAction
{
 public:
  explicit BtorActionNew(BtorSolverManager* smgr, const char* id)
      : BtorAction(smgr, id)
  {
  }
  void run() override;
  // void untrace(const char* s) override;
};

class BtorActionDelete : public BtorAction
{
 public:
  explicit BtorActionDelete(BtorSolverManager* smgr, const char* id)
      : BtorAction(smgr, id)
  {
  }
  void run() override;
  // void untrace(const char* s) override;
};

}  // namespace btor
}  // namespace smtmbt

#endif
#endif
