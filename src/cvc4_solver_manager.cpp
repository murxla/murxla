#include "cvc4_solver_manager.hpp"

namespace smtmbt {
namespace cvc4 {

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

}  // namespace cvc4
}  // namespace smtmbt
