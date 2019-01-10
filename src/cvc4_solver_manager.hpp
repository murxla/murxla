#ifdef SMTMBT_USE_CVC4

#ifndef __SMTMBT__CVC4_SOLVER_MANAGER_H
#define __SMTMBT__CVC4_SOLVER_MANAGER_H

#include "solver_manager.hpp"

#include "api/cvc4cpp.h"

namespace smtmbt {
namespace cvc4 {

/* -------------------------------------------------------------------------- */

using CVC4SolverManagerBase = SolverManager<CVC4::api::Solver*,
                                            CVC4::api::Term,
                                            CVC4::api::Sort,
                                            CVC4::api::TermHashFunction,
                                            CVC4::api::SortHashFunction>;

/* -------------------------------------------------------------------------- */

class CVC4SolverManager : public SolverManager<CVC4::api::Solver*,
                                               CVC4::api::Term,
                                               CVC4::api::Sort,
                                               CVC4::api::TermHashFunction,
                                               CVC4::api::SortHashFunction>
{
 public:
  CVC4SolverManager() = default;
  ~CVC4SolverManager();

 protected:
  CVC4::api::Sort get_sort(CVC4::api::Term term) override;
};

/* -------------------------------------------------------------------------- */

}  // namespace cvc4
}  // namespace smtmbt

#endif

#endif
