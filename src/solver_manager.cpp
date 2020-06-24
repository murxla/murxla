#include "solver_manager.hpp"

#include <algorithm>
#include <iterator>
#include <sstream>

#include "util.hpp"

namespace smtmbt {

#define SMTMBT_LEN_SYMBOL_MAX 128

/* -------------------------------------------------------------------------- */

SolverManager::SolverManager(Solver* solver,
                             RNGenerator& rng,
                             std::ostream& trace,
                             SolverOptions& options,
                             bool trace_seeds,
                             statistics::Statistics* stats)
    : d_mbt_stats(stats),
      d_trace_seeds(trace_seeds),
      d_solver(solver),
      d_rng(rng),
      d_trace(trace),
      d_options(options),
      d_used_options()
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
  d_n_sort_terms.clear();
  d_sorts.clear();
  d_sort_kind_to_sorts.clear();
  d_terms.clear();
  d_assumptions.clear();
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

std::string
SolverManager::trace_seed() const
{
  std::stringstream ss;
  ss << "set-seed " << d_rng.get_engine() << std::endl;
  return ss.str();
}

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

uint64_t
SolverManager::get_n_terms() const
{
  return d_n_terms;
}

uint64_t
SolverManager::get_n_terms(SortKind sort_kind)
{
  if (d_n_sort_terms.find(sort_kind) == d_n_sort_terms.end()) return 0;
  return d_n_sort_terms.at(sort_kind);
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
  assert(term->get_id() == 0);
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
    assert(d_n_sort_terms.find(sort_kind) == d_n_sort_terms.end());
    d_n_sort_terms.emplace(sort_kind, 1);
  }
  else
  {
    d_n_sort_terms.at(sort_kind) += 1;
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

  ++d_stats.sorts;
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
}

Term
SolverManager::pick_term(SortKind sort_kind)
{
  assert(has_term(sort_kind));
  Sort sort = pick_sort(sort_kind);
  return pick_term(sort);
}

Term
SolverManager::pick_term()
{
  assert(has_sort());
  SortKind sort_kind = pick_sort_kind();
  return pick_term(sort_kind);
}

Term
SolverManager::pick_assumption()
{
  assert(has_term(SORT_BOOL));
  Sort sort = pick_sort(SORT_BOOL);
  Term res  = pick_term(sort);
  d_assumptions.insert(res);
  return res;
}

Term
SolverManager::pick_assumed_assumption()
{
  assert(has_assumed());
  return d_rng.pick_from_set<std::unordered_set<Term, HashTerm>, Term>(
      d_assumptions);
}

void
SolverManager::clear_assumptions()
{
  d_assumptions.clear();
}

void
SolverManager::reset_sat()
{
  clear_assumptions();
  d_sat_called = false;
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

bool
SolverManager::has_assumed() const
{
  return !d_assumptions.empty();
}

bool
SolverManager::is_assumed(Term term) const
{
  return d_assumptions.find(term) != d_assumptions.end();
}

Term
SolverManager::find_term(Term term, Sort sort, SortKind sort_kind)
{
  assert(term.get());
  assert(term->get_id() == 0);
  assert(term->get_sort() == nullptr);
  assert(sort.get());
  assert(sort_kind != SORT_ANY);
  assert(sort_kind != SORT_BV || sort->get_bv_size() <= SMTMBT_BW_MAX);

  if (sort->get_kind() == SORT_ANY) sort->set_kind(sort_kind);
  assert(sort->get_kind() == sort_kind);
  assert(has_sort(sort));
  term->set_sort(sort);
  SortMap& map = d_terms.at(sort_kind);
  if (map.find(sort) != map.end())
  {
    auto it = map.at(sort).find(term);
    if (it != map.at(sort).end()) return it->first;
  }
  return nullptr;
}

Term
SolverManager::get_term(uint32_t id) const
{
  for (const auto& p : d_terms)
  {
    const SortMap& sort_map = p.second;
    for (const auto& q : sort_map)
    {
      const TermMap& term_map = q.second;
      for (const auto& t : term_map)
      {
        const Term& term = t.first;
        if (term->get_id() == id)
        {
          return term;
        }
      }
    }
  }
  return nullptr;
}

/* -------------------------------------------------------------------------- */

std::string
SolverManager::pick_symbol()
{
  uint32_t len = d_rng.pick<uint32_t>(0, SMTMBT_LEN_SYMBOL_MAX);
  /* Pick piped vs simple symbol with 50% probability. */
  return len && d_rng.flip_coin() ? d_rng.pick_piped_symbol(len)
                                  : d_rng.pick_simple_symbol(len);
}

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

Sort
SolverManager::get_sort(uint32_t id) const
{
  for (const Sort& sort : d_sorts)
  {
    if (sort->get_id() == id) return sort;
  }
  return nullptr;
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

std::pair<std::string, std::string>
SolverManager::pick_option()
{
  if (d_options.empty()) return std::make_pair("", "");

  SolverOption* option;

  std::vector<SolverOption*> available;

  bool skip;
  for (auto const& opt : d_options)
  {
    option = opt.get();

    /* Filter out conflicting options */
    skip = false;
    for (auto conflict : option->get_conflicts())
    {
      if (d_used_options.find(conflict) != d_used_options.end())
      {
        skip = true;
        break;
      }
    }
    if (skip) continue;

    /* Filter out options that depend on each other */
    for (auto depend : option->get_depends())
    {
      if (d_used_options.find(depend) == d_used_options.end())
      {
        skip = true;
        break;
      }
    }
    if (skip) continue;

    available.push_back(option);
  }

  option           = available[d_rng.pick<uint32_t>() % available.size()];
  std::string name = option->get_name();

  if (d_used_options.find(name) == d_used_options.end())
    d_used_options.insert(name);

  return std::make_pair(name, option->pick_value(d_rng));
}

/* -------------------------------------------------------------------------- */

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
      case THEORY_ARRAY:
        d_sort_kinds.emplace(SORT_ARRAY,
                             SortKindData(SORT_ARRAY, 2, THEORY_ARRAY));
        break;
      case THEORY_BV:
        d_sort_kinds.emplace(SORT_BV, SortKindData(SORT_BV, 0, THEORY_BV));
        break;
      case THEORY_BOOL:
        d_sort_kinds.emplace(SORT_BOOL,
                             SortKindData(SORT_BOOL, 0, THEORY_BOOL));
        break;
      default: assert(false);
    }
  }
}

void
SolverManager::add_op_kinds()
{
  assert(d_sort_kinds.size());

  uint32_t n    = SMTMBT_MK_TERM_N_ARGS;
  OpKindSet ops = d_solver->get_supported_op_kinds();

  add_op_kind(ops, OP_ITE, 3, 0, SORT_ANY, {SORT_BOOL, SORT_ANY, SORT_ANY});

  for (const auto& s : d_sort_kinds)
  {
    SortKind sort_kind = s.first;
    /* Only enable operator kinds where both argument and term theories
     * (and thus argument and term sort kinds) are enabled. */
    switch (sort_kind)
    {
      case SORT_ARRAY:
        add_op_kind(
            ops, OP_ARRAY_SELECT, 2, 0, SORT_ANY, {SORT_ARRAY, SORT_ANY});
        add_op_kind(ops,
                    OP_ARRAY_STORE,
                    3,
                    0,
                    SORT_ARRAY,
                    {SORT_ARRAY, SORT_ANY, SORT_ANY});
        break;

      case SORT_BOOL:
        add_op_kind(ops, OP_DISTINCT, n, 0, SORT_BOOL, {SORT_ANY});
        add_op_kind(ops, OP_EQUAL, 2, 0, SORT_BOOL, {SORT_ANY});
        add_op_kind(ops, OP_AND, n, 0, SORT_BOOL, {SORT_BOOL});
        add_op_kind(ops, OP_OR, n, 0, SORT_BOOL, {SORT_BOOL});
        add_op_kind(ops, OP_NOT, 1, 0, SORT_BOOL, {SORT_BOOL});
        add_op_kind(ops, OP_XOR, 2, 0, SORT_BOOL, {SORT_BOOL});
        add_op_kind(ops, OP_IMPLIES, 2, 0, SORT_BOOL, {SORT_BOOL});
        break;

      case SORT_BV:
        add_op_kind(ops, OP_BV_CONCAT, n, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_AND, n, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_OR, n, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_XOR, n, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_MULT, n, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_ADD, n, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_NOT, 1, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_NEG, 1, 0, SORT_BV, {SORT_BV});
#if 0
  // TODO not in SMT-LIB and CVC4 and Boolector disagree on return type
  // CVC4: Bool
  // Boolector: BV
  // >> should be BV
        add_op_kind(ops, OP_BV_REDOR, 1, 0, SORT_BOOL, SORT_BV);
        add_op_kind(ops, OP_BV_REDAND, 1, 0, SORT_BOOL, SORT_BV);
#endif
        add_op_kind(ops, OP_BV_NAND, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_NOR, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_XNOR, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_COMP, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_SUB, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_UDIV, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_UREM, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_SDIV, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_SREM, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_SMOD, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_SHL, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_LSHR, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_ASHR, 2, 0, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_ULT, 2, 0, SORT_BOOL, {SORT_BV});
        add_op_kind(ops, OP_BV_ULE, 2, 0, SORT_BOOL, {SORT_BV});
        add_op_kind(ops, OP_BV_UGT, 2, 0, SORT_BOOL, {SORT_BV});
        add_op_kind(ops, OP_BV_UGE, 2, 0, SORT_BOOL, {SORT_BV});
        add_op_kind(ops, OP_BV_SLT, 2, 0, SORT_BOOL, {SORT_BV});
        add_op_kind(ops, OP_BV_SLE, 2, 0, SORT_BOOL, {SORT_BV});
        add_op_kind(ops, OP_BV_SGT, 2, 0, SORT_BOOL, {SORT_BV});
        add_op_kind(ops, OP_BV_SGE, 2, 0, SORT_BOOL, {SORT_BV});
        /* indexed */
        add_op_kind(ops, OP_BV_EXTRACT, 1, 2, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_REPEAT, 1, 1, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_ROTATE_LEFT, 1, 1, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_ROTATE_RIGHT, 1, 1, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_SIGN_EXTEND, 1, 1, SORT_BV, {SORT_BV});
        add_op_kind(ops, OP_BV_ZERO_EXTEND, 1, 1, SORT_BV, {SORT_BV});
        break;

      default: assert(false);
    }
  }
}

void
SolverManager::add_op_kind(const OpKindSet& supported_kinds,
                           OpKind kind,
                           int32_t arity,
                           uint32_t nparams,
                           SortKind sort_kind,
                           const std::vector<SortKind>& sort_kind_args)
{
  if (supported_kinds.find(kind) != supported_kinds.end())
  {
    d_op_kinds.emplace(
        kind, OpKindData(kind, arity, nparams, sort_kind, sort_kind_args));
  }
}

template <typename TKind, typename TKindData, typename TKindMap>
TKindData&
SolverManager::pick_kind(TKindMap& map)
{
  assert(!map.empty());
  typename TKindMap::iterator it = map.begin();
  std::advance(it, d_rng.pick<uint32_t>() % map.size());
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
  uint32_t n = d_rng.pick<uint32_t>() % (sz1 + sz2);
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
