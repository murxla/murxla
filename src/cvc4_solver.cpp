#include "cvc4_solver.hpp"

#include <cassert>

#include "cvc4/api/cvc4cpp.h"

using namespace CVC4;

namespace smtmbt {
namespace cvc4 {

/* CVC4Term */

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


/* CVC4Sort */

CVC4Sort::~CVC4Sort()
{
  // TODO: release sort?
}

std::size_t
CVC4Sort::hash() const
{
  // TODO
  return 0;
}

CVC4Sort *
CVC4Sort::copy() const
{
  // TODO
  return nullptr;
}

/* CVC4Solver */

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
CVC4Solver::mk_sort(SortKind kind, uint32_t size) const
{
  Sort res = nullptr;
  switch (kind)
  {
    case BIT_VECTOR:
      res = new CVC4Sort(d_solver->mkBitVectorSort(size));
      break;

    default:
      break;
  }
  return res;
}

}  // namespace btor
}  // namespace smtmbt
