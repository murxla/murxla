#include "solver_manager.hpp"
#include <algorithm>

namespace smtmbt {

/* -------------------------------------------------------------------------- */

#define SMTMBT_ADD_SORT_KIND(kind, arity, theory) \
  d_sort_kinds.emplace(kind, SortKindData(kind, arity, theory));

void
SolverManager::add_enabled_theories()
{
  /* Get theories supported by enabled solver. */
  TheoryIdVector solver_theories = d_solver->get_supported_theories();

  /* Get all theories supported by MBT. */
  TheoryIdVector all_theories;
  for (int32_t t = 0; t < THEORY_ALL; ++t)
    all_theories.push_back(static_cast<TheoryId>(t));

  // TODO filter out based on enabled theories enabled via CLI

  /* We need to sort these for intersection. */
  std::sort(all_theories.begin(), all_theories.end());
  std::sort(solver_theories.begin(), solver_theories.end());
  /* Filter out theories not supported by solver. */
  d_enabled_theories = TheoryIdVector(all_theories.size());
  auto it = std::set_intersection(all_theories.begin(),
                                  all_theories.end(),
                                  solver_theories.begin(),
                                  solver_theories.end(),
                                  d_enabled_theories.begin());
  /* Resize to intersection size. */
  d_enabled_theories.resize(it - d_enabled_theories.begin());
}

void
SolverManager::add_sort_kinds()
{
  assert(d_enabled_theories.size());

  for (TheoryId theory : d_enabled_theories)
  {
    switch (theory)
    {
      case THEORY_BV: SMTMBT_ADD_SORT_KIND(BIT_VECTOR, 0, THEORY_BV); break;
      case THEORY_BOOL: SMTMBT_ADD_SORT_KIND(BOOLEAN, 0, THEORY_BOOL); break;
      default: assert(false);
    }
  }
}

template <typename TKind,
          typename TKindData,
          typename TKindMap,
          typename TKindVector>
TKindData&
SolverManager::pick_kind(TKindMap& map,
                         TKindVector* kinds1,
                         TKindVector* kinds2)
{
  assert(kinds1 || kinds2);
  size_t sz1 = kinds1 ? kinds1->size() : 0;
  size_t sz2 = kinds2 ? kinds2->size() : 0;
  uint32_t n = d_rng.pick_uint32() % (sz1 + sz2);
  typename TKindVector::iterator it;

  assert(sz1 || sz2);
  if (sz2 == 0 || n < sz1)
  {
    assert(kinds1);
    it = kinds1->begin();
  }
  else
  {
    assert(kinds2);
    n -= sz1;
    it = kinds2->begin();
  }
  std::advance(it, n);
  TKind kind = *it;
  assert(map.find(kind) != map.end());
  return map[kind];
}

/* -------------------------------------------------------------------------- */

SolverManager::SolverManager(Solver* solver, RNGenerator& rng)
    : d_solver(solver), d_rng(rng)
{
  add_enabled_theories();
  add_sort_kinds();
}

/* -------------------------------------------------------------------------- */

void
SolverManager::clear()
{
  d_theory_to_sorts.clear();
  d_sorts_to_theory.clear();
  d_terms.clear();
}

/* -------------------------------------------------------------------------- */

Solver&
SolverManager::get_solver()
{
  return *d_solver.get();
}

OpKindMap&
SolverManager::get_op_kinds()
{
  return d_op_kinds;
}

SortKindMap&
SolverManager::get_sort_kinds()
{
  return d_sort_kinds;
}

/* -------------------------------------------------------------------------- */

void
SolverManager::set_rng(RNGenerator& rng)
{
  d_rng = rng;
}

RNGenerator&
SolverManager::get_rng()
{
  return d_rng;
}

/* -------------------------------------------------------------------------- */

void
SolverManager::add_input(Term term, TheoryId theory)
{
  d_stats.inputs += 1;
  add_term(term, theory);
}

void
SolverManager::add_term(Term term, TheoryId theory)
{
  d_stats.terms += 1;

  Sort sort = d_solver->get_sort(term);
  add_sort(sort, theory);

  if (d_terms.find(theory) == d_terms.end())
  {
    d_terms.emplace(theory, SortMap());
  }

  assert(d_terms.find(theory) != d_terms.end());

  SortMap& map = d_terms[theory];
  map.emplace(sort, TermMap());

  assert(map.find(sort) != map.end());
  if (map[sort].find(term) == map[sort].end())
  {
    map[sort].emplace(term->copy(), 0);
  }
  else
  {
    map[sort][term] += 1;
  }
}

void
SolverManager::add_sort(Sort sort, TheoryId theory)
{
  if (d_sorts_to_theory.find(sort) == d_sorts_to_theory.end())
  {
    d_sorts_to_theory.emplace(sort, theory);
  }

  if (d_theory_to_sorts.find(theory) == d_theory_to_sorts.end())
  {
    d_theory_to_sorts.emplace(theory, std::unordered_set<Sort, HashSort>());
  }
  d_theory_to_sorts[theory].emplace(sort);
}

/* -------------------------------------------------------------------------- */

SortKind
SolverManager::pick_sort_kind(SortKindVector& kinds)
{
  return pick_kind<SortKind, SortKindData, SortKindMap, SortKindVector>(
             d_sort_kinds, &kinds)
      .d_kind;
}

/* -------------------------------------------------------------------------- */

TheoryId
SolverManager::pick_theory()
{
  assert(d_enabled_theories.size());
  auto it = d_enabled_theories.begin();
  std::advance(it, d_rng.pick_uint32() % d_enabled_theories.size());
  return *it;
}

TheoryId
SolverManager::pick_theory_with_sorts()
{
  assert(d_theory_to_sorts.size());
  auto it = d_theory_to_sorts.begin();
  std::advance(it, d_rng.pick_uint32() % d_theory_to_sorts.size());
  return it->first;
}

TheoryId
SolverManager::pick_theory_with_terms()
{
  assert(d_terms.size());
  auto it = d_terms.begin();
  std::advance(it, d_rng.pick_uint32() % d_terms.size());
  assert(!it->second.empty());
  return it->first;
}

TheoryId
SolverManager::get_theory(Sort sort)
{
  assert(has_sort(sort));
  return d_sorts_to_theory[sort];
}

/* -------------------------------------------------------------------------- */

Term
SolverManager::pick_term()
{
  TheoryId theory;
  theory = pick_theory_with_terms();
  return pick_term(theory);
}

Term
SolverManager::pick_term(TheoryId theory)
{
  assert(d_terms.find(theory) != d_terms.end());
  if (theory == THEORY_ALL)
  {
    theory = pick_theory_with_terms();
  }
  Sort sort;
  sort = pick_sort_with_terms(theory);
  assert(get_theory(sort) == theory);
  Term res = pick_term(sort);
  assert(d_solver->get_sort(res) == sort);
  assert(get_theory(d_solver->get_sort(res)) == theory);
  return res;
}

Term
SolverManager::pick_term(Term term)
{
  Sort sort = d_solver->get_sort(term);
  return pick_term(sort);
}

Term
SolverManager::pick_term(Sort sort)
{
  TheoryId theory = get_theory(sort);
  assert(d_terms.find(theory) != d_terms.end());
  assert(d_terms[theory].find(sort) != d_terms[theory].end());
  TermMap& map = d_terms[theory][sort];
  assert(!map.empty());
  auto it = map.begin();
  if (map.size() > 1)
  {
    std::advance(it, d_rng.pick_uint32() % map.size());
  }
  // TODO: increment ref counter
  return it->first;
}

bool
SolverManager::has_term()
{
  for (const auto t : d_terms)
  {
    for (const auto s : t.second)
    {
      if (!s.second.empty()) return true;
    }
  }
  return false;
}

bool
SolverManager::has_term(TheoryId theory)
{
  if (theory == THEORY_ALL) return has_term();

  if (d_terms.find(theory) == d_terms.end()) return false;

  for (const auto s : d_terms[theory])
  {
    if (!s.second.empty()) return true;
  }
  return false;
}

bool
SolverManager::has_term(Sort sort)
{
  return !d_terms[get_theory(sort)][sort].empty();
}

/* -------------------------------------------------------------------------- */

Sort
SolverManager::pick_sort()
{
  TheoryId theory = pick_theory_with_sorts();
  return pick_sort(theory);
}

Sort
SolverManager::pick_sort(TheoryId theory)
{
  assert(d_theory_to_sorts.find(theory) != d_theory_to_sorts.end());
  assert(!d_theory_to_sorts[theory].empty());

  SortSet& set = d_theory_to_sorts[theory];
  auto it      = set.begin();
  std::advance(it, d_rng.pick_uint32() % set.size());
  return *it;
}

Sort
SolverManager::pick_sort_with_terms()
{
  TheoryId theory = pick_theory_with_terms();
  return pick_sort_with_terms(theory);
}

Sort
SolverManager::pick_sort_with_terms(TheoryId theory)
{
  if (theory == THEORY_ALL) theory = pick_theory_with_terms();

  SortMap& map = d_terms[theory];
  assert(!map.empty());

  auto it = map.begin();
  if (map.size() > 1)
  {
    std::advance(it, d_rng.pick_uint32() % map.size());
  }
  return it->first;
}

bool
SolverManager::has_sort()
{
  return !d_sorts_to_theory.empty();
}

bool
SolverManager::has_sort(Sort sort)
{
  return d_sorts_to_theory.find(sort) != d_sorts_to_theory.end();
}

bool
SolverManager::has_sort(TheoryId theory)
{
  if (d_theory_to_sorts.find(theory) == d_theory_to_sorts.end()) return false;
  return !d_theory_to_sorts[theory].empty();
}

}  // namespace smtmbt
