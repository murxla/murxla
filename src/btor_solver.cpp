#include "btor_solver.hpp"

#include <cassert>

#include "boolector/boolector.h"

namespace smtmbt {
namespace btor {

void
BtorSolver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = boolector_new();
}

void
BtorSolver::delete_solver()
{
  assert(d_solver != nullptr);
  boolector_delete(d_solver);
  d_solver = nullptr;
}

bool
BtorSolver::is_initialized() const
{
  return d_solver != nullptr;
}

}  // namespace btor
}  // namespace smtmbt
