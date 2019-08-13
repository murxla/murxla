#include "solver_manager.hpp"

namespace smtmbt {

Solver&
SolverManager::get_solver()
{
  return *d_solver.get();
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
  if (d_sorts2theory.find(sort) == d_sorts2theory.end())
  {
    d_sorts2theory.emplace(sort->copy(), theory);
  }

  if (d_theory2sorts.find(theory) == d_theory2sorts.end())
  {
    d_theory2sorts.emplace(theory, std::unordered_set<Sort, HashSort>());
  }
  d_theory2sorts[theory].emplace(sort);
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
  TheoryId theory = pick_theory();
  return pick_sort(theory);
}

Sort
SolverManager::pick_sort(TheoryId theory)
{
  assert(d_theory2sorts.find(theory) != d_theory2sorts.end());
  assert(!d_theory2sorts[theory].empty());

  SortSet& set = d_theory2sorts[theory];
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
  SortMap& map = d_terms[theory];
  assert(!map.empty());

  if (theory == THEORY_ALL) theory = pick_theory_with_terms();

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
  return !d_sorts2theory.empty();
}

bool
SolverManager::has_sort(Sort sort)
{
  return d_sorts2theory.find(sort) != d_sorts2theory.end();
}

bool
SolverManager::has_sort(TheoryId theory)
{
  if (d_theory2sorts.find(theory) == d_theory2sorts.end()) return false;
  return !d_theory2sorts[theory].empty();
}

/* -------------------------------------------------------------------------- */

TheoryId
SolverManager::pick_theory()
{
  assert(d_theory2sorts.size());
  auto it = d_theory2sorts.begin();
  std::advance(it, d_rng.pick_uint32() % d_theory2sorts.size());
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
  return d_sorts2theory[sort];
}

}  // namespace smtmbt
