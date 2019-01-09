#ifndef __SMTMBT__BTOR_ACTIONS_HPP_INCLUDED
#define __SMTMBT__BTOR_ACTIONS_HPP_INCLUDED

#ifdef SMTMBT_USE_BOOLECTOR

#include "btor_solver_manager.hpp"

namespace smtmbt {
namespace btor {

class BtorAction : public Action
{
 public:
  BtorAction(SolverManager<Btor*,
                           BoolectorNode*,
                           BoolectorSort,
                           BoolectorNodeHashFunc,
                           BoolectorSortHashFunc>* smgr,
             const std::string& id)
      : Action(id), d_smgr(static_cast<BtorSolverManager*>(smgr))
  {
  }

 protected:
  BtorSolverManager* d_smgr;
};

class BtorActionNew : public BtorAction
{
 public:
  BtorActionNew(SolverManager<Btor*,
                              BoolectorNode*,
                              BoolectorSort,
                              BoolectorNodeHashFunc,
                              BoolectorSortHashFunc>* smgr)
      : BtorAction(smgr, "new")
  {
  }
  void run() override;
  // void untrace(const char* s) override;
};

class BtorActionDelete : public BtorAction
{
 public:
  BtorActionDelete(SolverManager<Btor*,
                                 BoolectorNode*,
                                 BoolectorSort,
                                 BoolectorNodeHashFunc,
                                 BoolectorSortHashFunc>* smgr)
      : BtorAction(smgr, "delete")
  {
  }
  void run() override;
  // void untrace(const char* s) override;
};

}  // namespace btor
}  // namespace smtmbt

#endif
#endif
