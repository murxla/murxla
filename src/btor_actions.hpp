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
  BtorAction(BtorSolverManager* smgr, const std::string& id)
      : Action(id), d_smgr(smgr)
  {
  }

 protected:
  BtorSolverManager* d_smgr;
};

class BtorActionNew : public BtorAction
{
 public:
  BtorActionNew(BtorSolverManager* smgr, const std::string& id)
      : BtorAction(smgr, id)
  {
  }
  void run() override;
  // void untrace(const char* s) override;
};

class BtorActionDelete : public BtorAction
{
 public:
  BtorActionDelete(BtorSolverManager* smgr, const std::string& id)
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
