#include "solver.hpp"
#include "theory.hpp"

namespace smtmbt {

#define SMTMBT_ADD_SORT_KIND(kind, arity, theory) \
  d_sort_kinds.emplace(kind, SortKindData(kind, arity, theory));

Solver::Solver(RNGenerator& rng) : d_rng(rng)
{
  SMTMBT_ADD_SORT_KIND(BIT_VECTOR, 0, THEORY_BV);
  SMTMBT_ADD_SORT_KIND(BOOLEAN, 0, THEORY_BOOL);
}

TheoryIdVector
Solver::get_supported_theories() const
{
  TheoryIdVector res;
  for (int32_t t = 0; t < THEORY_ALL; ++t)
    res.push_back(static_cast<TheoryId>(t));
  return res;
}

OpKindMap&
Solver::get_op_kinds()
{
  return d_op_kinds;
}

SortKindMap&
Solver::get_sort_kinds()
{
  return d_sort_kinds;
}

SortKind
Solver::pick_sort_kind(SortKindVector& kinds)
{
  return pick_kind<SortKind, SortKindData, SortKindMap, SortKindVector>(
             d_sort_kinds, &kinds)
      .d_kind;
}
}  // namespace smtmbt
