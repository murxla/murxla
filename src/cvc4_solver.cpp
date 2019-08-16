#include "cvc4_solver.hpp"

#include <cassert>

#include "cvc4/api/cvc4cpp.h"

using namespace CVC4;

namespace smtmbt {
namespace cvc4 {

/* -------------------------------------------------------------------------- */
/* CVC4Term                                                                   */
/* -------------------------------------------------------------------------- */

CVC4Term::~CVC4Term()
{
  // TODO: release sort?
}

std::size_t
CVC4Term::hash() const
{
  // TODO
  return 0;
}

CVC4Term *
CVC4Term::copy() const
{
  // TODO
  return nullptr;
}

/* -------------------------------------------------------------------------- */
/* CVC4Sort                                                                   */
/* -------------------------------------------------------------------------- */

CVC4Sort::CVC4Sort(CVC4::api::Solver* cvc4, CVC4::api::Sort sort)
    : d_solver(cvc4), d_sort(sort)
{
}

CVC4Sort::~CVC4Sort()
{
  // TODO: release sort?
}

std::size_t
CVC4Sort::hash() const
{
  return CVC4::api::SortHashFunction()(d_sort);
}

/* -------------------------------------------------------------------------- */
/* CVC4Solver                                                                 */
/* -------------------------------------------------------------------------- */

void
CVC4Solver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = new api::Solver();
}

void
CVC4Solver::delete_solver()
{
  assert(d_solver != nullptr);
  delete d_solver;
  d_solver = nullptr;
}

bool
CVC4Solver::is_initialized() const
{
  return d_solver != nullptr;
}

Sort
CVC4Solver::mk_sort(SortKind kind) const
{
  CVC4::api::Sort res;
  switch (kind)
  {
    case SortKind::BOOLEAN: res = d_solver->getBooleanSort(); break;

    default: assert(false);
  }
  return std::shared_ptr<CVC4Sort>(new CVC4Sort(d_solver, res));
}

Sort
CVC4Solver::mk_sort(SortKind kind, uint32_t size) const
{
  Sort res = nullptr;
  switch (kind)
  {
    case BIT_VECTOR:
      res = std::shared_ptr<CVC4Sort>(
          new CVC4Sort(d_solver, d_solver->mkBitVectorSort(size)));
      break;

    default: assert(false);
  }
  return res;
}

}  // namespace btor
}  // namespace smtmbt
