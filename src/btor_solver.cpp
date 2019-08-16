#include "btor_solver.hpp"

#include <cassert>

#include "theory.hpp"

namespace smtmbt {
namespace btor {

/* -------------------------------------------------------------------------- */
/* BtorSort                                                                   */
/* -------------------------------------------------------------------------- */

BtorSort::BtorSort(Btor* btor, BoolectorSort sort)
    : d_solver(btor), d_sort(sort)
{
}

BtorSort::~BtorSort() { boolector_release_sort(d_solver, d_sort); }

std::size_t
BtorSort::hash() const
{
  return std::hash<BoolectorSort>{}(d_sort);
}

/* -------------------------------------------------------------------------- */
/* BtorSolver                                                                 */
/* -------------------------------------------------------------------------- */

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

TheoryIdVector
BtorSolver::get_supported_theories() const
{
  return {THEORY_BV, THEORY_BOOL};
}

Sort
BtorSolver::mk_sort(SortKind kind) const
{
  assert(kind == SortKind::BOOLEAN);
  BoolectorSort res = boolector_bool_sort(d_solver);
  return std::shared_ptr<BtorSort>(new BtorSort(d_solver, res));
}

Sort
BtorSolver::mk_sort(SortKind kind, uint32_t size) const
{
  assert(kind == SortKind::BIT_VECTOR);
  BoolectorSort res = boolector_bitvec_sort(d_solver, size);
  return std::shared_ptr<BtorSort>(new BtorSort(d_solver, res));
}
}  // namespace btor
}  // namespace smtmbt
