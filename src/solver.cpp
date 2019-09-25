#include "solver.hpp"
#include "theory.hpp"

/* -------------------------------------------------------------------------- */

namespace smtmbt {

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

void
AbsSort::set_kind(SortKind sort_kind)
{
  d_kind = sort_kind;
}

SortKind
AbsSort::get_kind()
{
  return d_kind;
}

bool
operator==(const Sort& a, const Sort& b)
{
  return a->equals(b);
}

size_t
HashSort::operator()(const Sort s) const
{
  return s->hash();
}

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

bool
operator==(const Term& a, const Term& b)
{
  return a->equals(b);
}

size_t
HashTerm::operator()(const Term t) const
{
  return t->hash();
}

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

Solver::Solver(RNGenerator& rng) : d_rng(rng)
{
}

TheoryIdVector
Solver::get_supported_theories() const
{
  TheoryIdVector res;
  for (int32_t t = 0; t < THEORY_ALL; ++t)
    res.push_back(static_cast<TheoryId>(t));
  return res;
}

const std::vector<Solver::Base>&
Solver::get_bases() const
{
  return d_bases;
}

const std::vector<Solver::SpecialValueBV>&
Solver::get_special_values_bv() const
{
  return d_special_values_bv;
}

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt
