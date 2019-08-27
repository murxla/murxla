#include "solver.hpp"
#include "theory.hpp"

namespace smtmbt {

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

bool
operator==(const Sort& a, const Sort& b)
{
  return a->equals(b);
}

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

bool
operator==(const Term& a, const Term& b)
{
  return a->equals(b);
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
}  // namespace smtmbt
