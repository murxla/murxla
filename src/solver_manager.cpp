#include "solver_manager.hpp"
#include "util.hpp"
#include <algorithm>

namespace smtmbt {

/* -------------------------------------------------------------------------- */

SolverManager::SolverManager(Solver* solver,
                             RNGenerator& rng,
                             std::ostream& trace)
    : d_solver(solver), d_rng(rng), d_trace(trace)
{
  add_enabled_theories();
  add_sort_kinds();  // adds only sort kinds of enabled theories
  add_op_kinds();    // adds only op kinds where both term and argument sorts
                     // are enabled

  TheoryIdSet enabled_theories = d_enabled_theories;
}

/* -------------------------------------------------------------------------- */

void
SolverManager::clear()
{
  d_sorts.clear();
  d_terms.clear();
}

/* -------------------------------------------------------------------------- */

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
SolverManager::get_rng() const
{
  return d_rng;
}

/* -------------------------------------------------------------------------- */

std::ostream&
SolverManager::get_trace()
{
  return d_trace;
}

/* -------------------------------------------------------------------------- */

const TheoryIdSet&
SolverManager::get_enabled_theories() const
{
  return d_enabled_theories;
}

/* -------------------------------------------------------------------------- */

void
SolverManager::add_input(Term term, Sort sort, SortKind sort_kind)
{
  assert(term.get());

  d_stats.inputs += 1;
  add_term(term, sort, sort_kind);
}

void
SolverManager::add_term(Term term, Sort sort, SortKind sort_kind)
{
  assert(term.get());
  assert(term->get_sort() == nullptr);
  assert(sort.get());
  assert(sort_kind != SORT_ANY);
  assert(sort_kind != SORT_BV || sort->get_bv_size() <= SMTMBT_BW_MAX);

  if (sort->get_kind() == SORT_ANY) sort->set_kind(sort_kind);
  assert(!has_sort(sort) || sort->get_kind() == sort_kind);

  d_stats.terms += 1;

  add_sort(sort, sort_kind);

  term->set_sort(sort);

  /* add term to d_terms */
  if (d_terms.find(sort_kind) == d_terms.end())
  {
    d_terms.emplace(sort_kind, SortMap());
  }

  SortMap& map = d_terms.at(sort_kind);
  if (map.find(sort) == map.end())
  {
    map.emplace(sort, TermMap());
  }
  if (map.at(sort).find(term) == map.at(sort).end())
  {
    term->set_id(++d_n_terms);
    map.at(sort).emplace(term, 0);
  }
  else
  {
    term->set_id(map.at(sort).find(term)->first->get_id());
  }
  map.at(sort).at(term) += 1;
}

void
SolverManager::add_sort(Sort sort, SortKind sort_kind)
{
  assert(sort.get());
  assert(sort_kind != SORT_ANY);

  if (sort->get_kind() == SORT_ANY) sort->set_kind(sort_kind);

  auto it = d_sorts.find(sort);
  if (it == d_sorts.end())
  {
    sort->set_id(++d_n_sorts);
    d_sorts.insert(sort);
  }
  else
  {
    assert((*it)->get_kind() == sort_kind);
    sort->set_id((*it)->get_id());
  }

  if (d_sort_kind_to_sorts.find(sort_kind) == d_sort_kind_to_sorts.end())
  {
    d_sort_kind_to_sorts.emplace(sort_kind, SortSet());
  }
  if (d_sort_kind_to_sorts.at(sort_kind).find(sort)
      != d_sort_kind_to_sorts.at(sort_kind).end())
  {
    d_sort_kind_to_sorts.at(sort_kind).insert(sort);
  }
}

/* -------------------------------------------------------------------------- */

SortKind
SolverManager::pick_sort_kind(bool with_terms)
{
  assert(!d_sort_kind_to_sorts.empty());
  if (with_terms)
  {
    assert(has_term());
    return d_rng.pick_from_map<std::unordered_map<SortKind, SortMap>, SortKind>(
        d_terms);
  }
  return d_rng.pick_from_map<std::unordered_map<SortKind, SortSet>, SortKind>(
      d_sort_kind_to_sorts);
}

SortKindData&
SolverManager::pick_sort_kind_data()
{
  return pick_kind<SortKind, SortKindData, SortKindMap>(d_sort_kinds);
}

OpKindData&
SolverManager::pick_op_kind_data()
{
  return pick_kind<OpKind, OpKindData, OpKindMap>(d_op_kinds);
}

/* -------------------------------------------------------------------------- */

TheoryId
SolverManager::pick_theory()
{
  return d_rng.pick_from_set<TheoryIdSet, TheoryId>(d_enabled_theories);
}

/* -------------------------------------------------------------------------- */

Term
SolverManager::pick_term(Sort sort)
{
  assert(has_sort(sort));
  assert(has_term(sort));
  SortKind sort_kind = sort->get_kind();
  assert(d_sort_kind_to_sorts.find(sort_kind) != d_sort_kind_to_sorts.end());
  return d_rng.pick_from_map<TermMap, Term>(d_terms.at(sort_kind).at(sort));
  // TODO: increment ref counter
}

Term
SolverManager::pick_term(SortKind sort_kind)
{
  assert(has_term(sort_kind));
  Sort sort = pick_sort(sort_kind);
  return pick_term(sort);
}

bool
SolverManager::has_term() const
{
  for (const auto& sort_kind : d_terms)
  {
    for (const auto& sort_set : sort_kind.second)
    {
      assert(!sort_set.second.empty());
    }
  }
  return !d_terms.empty();
}

bool
SolverManager::has_term(SortKind sort_kind) const
{
  if (sort_kind == SORT_ANY) return has_term();
  assert(d_terms.find(sort_kind) == d_terms.end()
         || !d_terms.at(sort_kind).empty());
  return d_terms.find(sort_kind) != d_terms.end();
}

bool
SolverManager::has_term(Sort sort) const
{
  SortKind sort_kind = sort->get_kind();
  if (d_terms.find(sort_kind) == d_terms.end()) return false;
  assert(d_terms.at(sort_kind).find(sort) == d_terms.at(sort_kind).end()
         || !d_terms.at(sort_kind).at(sort).empty());
  return d_terms.at(sort_kind).find(sort) != d_terms.at(sort_kind).end();
}

bool
SolverManager::has_term(Term term) const
{
  Sort sort          = term->get_sort();
  SortKind sort_kind = sort->get_kind();
  if (d_terms.find(sort_kind) == d_terms.end())
  {
    return false;
  }
  if (d_terms.at(sort_kind).find(sort) == d_terms.at(sort_kind).end())
  {
    return false;
  }
  return d_terms.at(sort_kind).at(sort).find(term)
         != d_terms.at(sort_kind).at(sort).end();
}

/* -------------------------------------------------------------------------- */

Sort
SolverManager::pick_sort()
{
  return d_rng.pick_from_set<SortSet, Sort>(d_sorts);
}

Sort
SolverManager::pick_sort(SortKind sort_kind, bool with_terms)
{
  assert(!with_terms || has_term(sort_kind));
  if (sort_kind == SORT_ANY) sort_kind = pick_sort_kind(with_terms);

  if (with_terms)
  {
    return d_rng.pick_from_map<SortMap, Sort>(d_terms.at(sort_kind));
  }
  assert(d_sort_kinds.find(sort_kind) != d_sort_kinds.end());
  assert(d_sort_kind_to_sorts.find(sort_kind) != d_sort_kind_to_sorts.end());
  return d_rng.pick_from_set<SortSet, Sort>(d_sort_kind_to_sorts.at(sort_kind));
}

Sort
SolverManager::pick_sort_bv(uint32_t bw_max, bool with_terms)
{
  assert(has_sort_bv(bw_max, with_terms));
  std::vector<Sort> sorts;
  if (with_terms)
  {
    for (const auto& p : d_terms.at(SORT_BV))
    {
      if (p.first->is_bv() && p.first->get_bv_size() <= bw_max)
      {
        sorts.push_back(p.first);
      }
    }
  }
  else
  {
    for (const Sort sort : d_sorts)
    {
      if (sort->is_bv() && sort->get_bv_size() <= bw_max)
      {
        sorts.push_back(sort);
      }
    }
  }
  return d_rng.pick_from_set<std::vector<Sort>, Sort>(sorts);
}

bool
SolverManager::has_sort() const
{
  return !d_sorts.empty();
}

bool
SolverManager::has_sort(Sort sort) const
{
  return d_sorts.find(sort) != d_sorts.end();
}

bool
SolverManager::has_sort_bv(uint32_t bw_max, bool with_terms) const
{
  if (with_terms)
  {
    if (d_terms.find(SORT_BV) == d_terms.end()) return false;
    for (const auto& p : d_terms.at(SORT_BV))
    {
      if (p.first->is_bv() && p.first->get_bv_size() <= bw_max) return true;
    }
    return false;
  }
  for (const Sort sort : d_sorts)
  {
    if (sort->is_bv() && sort->get_bv_size() <= bw_max) return true;
  }
  return false;
}

/* -------------------------------------------------------------------------- */

#define SMTMBT_ADD_SORT_KIND(kind, arity, theory) \
  d_sort_kinds.emplace(kind, SortKindData(kind, arity, theory));

#define SMTMBT_ADD_OP_KIND(kind, arity, nparams, theory_term, theory_args) \
  d_op_kinds.emplace(                                                      \
      kind, OpKindData(kind, arity, nparams, theory_term, theory_args));

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
  TheoryIdVector tmp(all_theories.size());
  auto it = std::set_intersection(all_theories.begin(),
                                  all_theories.end(),
                                  solver_theories.begin(),
                                  solver_theories.end(),
                                  tmp.begin());
  /* Resize to intersection size. */
  tmp.resize(it - tmp.begin());
  d_enabled_theories = TheoryIdSet(tmp.begin(), tmp.end());
}

void
SolverManager::add_sort_kinds()
{
  assert(d_enabled_theories.size());

  for (TheoryId theory : d_enabled_theories)
  {
    switch (theory)
    {
      case THEORY_BV: SMTMBT_ADD_SORT_KIND(SORT_BV, 0, THEORY_BV); break;
      case THEORY_BOOL: SMTMBT_ADD_SORT_KIND(SORT_BOOL, 0, THEORY_BOOL); break;
      default: assert(false);
    }
  }
}

void
SolverManager::add_op_kinds()
{
  assert(d_sort_kinds.size());

  uint32_t n = SMTMBT_MK_TERM_N_ARGS;

  SMTMBT_ADD_OP_KIND(ITE, 3, 0, SORT_ANY, SORT_ANY);

  for (const auto& s : d_sort_kinds)
  {
    SortKind sort_kind = s.first;
    /* Only enable operator kinds where both argument and term theories
     * (and thus argument and term sort kinds) are enabled. */
    switch (sort_kind)
    {
      case SORT_BOOL:
        SMTMBT_ADD_OP_KIND(DISTINCT, n, 0, SORT_BOOL, SORT_ANY);
        SMTMBT_ADD_OP_KIND(EQUAL, 2, 0, SORT_BOOL, SORT_ANY);
        SMTMBT_ADD_OP_KIND(AND, n, 0, SORT_BOOL, SORT_BOOL);
        SMTMBT_ADD_OP_KIND(OR, n, 0, SORT_BOOL, SORT_BOOL);
        SMTMBT_ADD_OP_KIND(NOT, 1, 0, SORT_BOOL, SORT_BOOL);
        SMTMBT_ADD_OP_KIND(XOR, 2, 0, SORT_BOOL, SORT_BOOL);
        SMTMBT_ADD_OP_KIND(IMPLIES, 2, 0, SORT_BOOL, SORT_BOOL);
        break;

      case SORT_BV:
        SMTMBT_ADD_OP_KIND(BV_CONCAT, n, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_AND, n, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_OR, n, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_XOR, n, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_MULT, n, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_ADD, n, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_NOT, 1, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_NEG, 1, 0, SORT_BV, SORT_BV);
#if 0
  // TODO not in SMT-LIB and CVC4 and Boolector disagree on return type
  // CVC4: Bool
  // Boolector: BV
  // >> should be BV
        SMTMBT_ADD_OP_KIND(BV_REDOR, 1, 0, SORT_BOOL, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_REDAND, 1, 0, SORT_BOOL, SORT_BV);
#endif
        SMTMBT_ADD_OP_KIND(BV_NAND, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_NOR, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_XNOR, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_COMP, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_SUB, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_UDIV, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_UREM, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_SDIV, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_SREM, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_SMOD, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_SHL, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_LSHR, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_ASHR, 2, 0, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_ULT, 2, 0, SORT_BOOL, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_ULE, 2, 0, SORT_BOOL, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_UGT, 2, 0, SORT_BOOL, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_UGE, 2, 0, SORT_BOOL, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_SLT, 2, 0, SORT_BOOL, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_SLE, 2, 0, SORT_BOOL, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_SGT, 2, 0, SORT_BOOL, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_SGE, 2, 0, SORT_BOOL, SORT_BV);
        /* indexed */
        SMTMBT_ADD_OP_KIND(BV_EXTRACT, 1, 2, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_REPEAT, 1, 1, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_ROTATE_LEFT, 1, 1, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_ROTATE_RIGHT, 1, 1, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_SIGN_EXTEND, 1, 1, SORT_BV, SORT_BV);
        SMTMBT_ADD_OP_KIND(BV_ZERO_EXTEND, 1, 1, SORT_BV, SORT_BV);
        break;

      default: assert(false);
    }
  }
}

template <typename TKind, typename TKindData, typename TKindMap>
TKindData&
SolverManager::pick_kind(TKindMap& map)
{
  assert(!map.empty());
  typename TKindMap::iterator it = map.begin();
  std::advance(it, d_rng.pick_uint32() % map.size());
  return it->second;
}

#if 0
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
  return map.at(kind);
}
#endif

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt
