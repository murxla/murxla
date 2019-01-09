#ifndef __SMTMBT__CVC4_ACTIONS_HPP_INCLUDED
#define __SMTMBT__CVC4_ACTIONS_HPP_INCLUDED

#ifdef SMTMBT_USE_CVC4

#include "cvc4_solver_manager.hpp"

namespace smtmbt {
namespace cvc4 {

class CVC4Action : public Action
{
 public:
  CVC4Action(SolverManager<CVC4::api::Solver*,
                           CVC4::api::Term,
                           CVC4::api::Sort,
                           CVC4::api::TermHashFunction,
                           CVC4::api::SortHashFunction>* smgr,
             const std::string& id)
      : Action(id), d_smgr(static_cast<CVC4SolverManager*>(smgr))
  {
  }

 protected:
  CVC4SolverManager* d_smgr;
};

class CVC4ActionNew : public CVC4Action
{
 public:
  CVC4ActionNew(SolverManager<CVC4::api::Solver*,
                              CVC4::api::Term,
                              CVC4::api::Sort,
                              CVC4::api::TermHashFunction,
                              CVC4::api::SortHashFunction>* smgr)
      : CVC4Action(smgr, "new")
  {
  }
  void run() override;
  // void untrace(const char* s) override;
};

class CVC4ActionDelete : public CVC4Action
{
 public:
  CVC4ActionDelete(SolverManager<CVC4::api::Solver*,
                                 CVC4::api::Term,
                                 CVC4::api::Sort,
                                 CVC4::api::TermHashFunction,
                                 CVC4::api::SortHashFunction>* smgr)
      : CVC4Action(smgr, "delete")
  {
  }
  void run() override;
  // void untrace(const char* s) override;
};

}  // namespace cvc4
}  // namespace smtmbt

#endif
#endif
