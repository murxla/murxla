#include "cvc4_solver_manager.hpp"

#include <cassert>

#include "util.hpp"

namespace smtmbt {
namespace cvc4 {

/* -------------------------------------------------------------------------- */

class CVC4Action : public Action
{
 public:
  CVC4Action(CVC4SolverManagerBase* smgr, const std::string& id)
      : Action(id), d_smgr(static_cast<CVC4SolverManager*>(smgr))
  {
  }

 protected:
  CVC4SolverManager* d_smgr;
};

/* -------------------------------------------------------------------------- */

class CVC4ActionNew : public CVC4Action
{
 public:
  CVC4ActionNew(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "new") {}

  void run() override
  {
    SMTMBT_TRACE << get_id();
    CVC4::api::Solver* cvc4 = d_smgr->get_solver();
    if (cvc4 != nullptr) delete (cvc4);
    d_smgr->set_solver(new CVC4::api::Solver());
  }
  // void untrace(const char* s) override;
};

class CVC4ActionDelete : public CVC4Action
{
 public:
  CVC4ActionDelete(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "delete") {}

  void run() override
  {
    SMTMBT_TRACE << get_id();
    CVC4::api::Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    delete (cvc4);
    d_smgr->set_solver(nullptr);
  }
  // void untrace(const char* s) override;
};

/* -------------------------------------------------------------------------- */

CVC4SolverManager::~CVC4SolverManager()
{
  d_terms.clear();
  delete d_solver;
}

CVC4::api::Sort
CVC4SolverManager::get_sort(CVC4::api::Term term)
{
  return term.getSort();
}

/* -------------------------------------------------------------------------- */

}  // namespace cvc4
}  // namespace smtmbt
