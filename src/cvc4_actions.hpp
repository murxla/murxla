#ifndef __SMTMBT__CVC4_ACTIONS_HPP_INCLUDED
#define __SMTMBT__CVC4_ACTIONS_HPP_INCLUDED

#ifdef SMTMBT_USE_CVC4

#include "cvc4_solver_manager.hpp"
#include "fsm.hpp"

namespace smtmbt {
namespace cvc4 {

class CVC4Action : public Action
{
 public:
  CVC4Action(CVC4SolverManager* smgr, const std::string& id)
      : Action(id), d_smgr(smgr)
  {
  }

 protected:
  CVC4SolverManager* d_smgr;
};

class CVC4ActionNew : public CVC4Action
{
 public:
  CVC4ActionNew(CVC4SolverManager* smgr, const std::string& id)
      : CVC4Action(smgr, id)
  {
  }
  void run() override;
  // void untrace(const char* s) override;
};

class CVC4ActionDelete : public CVC4Action
{
 public:
  CVC4ActionDelete(CVC4SolverManager* smgr, const std::string& id)
      : CVC4Action(smgr, id)
  {
  }
  void run() override;
  // void untrace(const char* s) override;
};

}  // namespace cvc4
}  // namespace smtmbt

#endif
#endif
