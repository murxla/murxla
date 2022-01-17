#include "term_db.hpp"

#include <algorithm>
#include <set>

#include "config.hpp"
#include "solver_manager.hpp"

namespace murxla {

const static size_t MURXLA_PICK_MAX_WEIGHT = std::numeric_limits<size_t>::max();

TermRefs::TermRefs(size_t level)
{
  for (size_t i = 0; i < level; ++i)
  {
    d_levels.push_back(0);
  }
}

void
TermRefs::add(const Term& t, size_t level)
{
  assert(level < d_levels.size());

  if (d_idx.find(t) == d_idx.end())
  {
    d_idx.emplace(t, d_refs.size());

    size_t end = get_level_end(level);

    ++d_levels[level];
    d_terms.insert(d_terms.begin() + end, t);
    d_refs.insert(d_refs.begin() + end, 0);

    /* Initialize weight to maximum weight for new terms. Will be recomputed as
     * soon as term is picked once. This ensures that new terms are picked with
     * a very high probability. */
    d_weights.insert(d_weights.begin() + end, MURXLA_PICK_MAX_WEIGHT);
  }
}

bool
TermRefs::contains(const Term& t) const
{
  return d_idx.find(t) != d_idx.end();
}

Term
TermRefs::get(const Term& t) const
{
  auto it = d_idx.find(t);
  if (it == d_idx.end())
  {
    return nullptr;
  }
  return it->first;
}

Term
TermRefs::pick(RNGenerator& rng, size_t level)
{
  assert(!d_terms.empty());

  /* Terms with higher reference count have lower probability to be picked. */
  if (d_refs_sum % 100 == 25)
  {
    assert(d_weights.size() == d_refs.size());
    for (size_t i = 0; i < d_weights.size(); ++i)
    {
      d_weights[i] = d_refs_sum - d_refs[i] + 1;
    }
  }

  size_t idx;
  /* No specifc level requested, pick from any level. */
  if (level == MAX_LEVEL)
  {
    idx = rng.pick_weighted(d_weights);
  }
  /* Pick from specified level only. */
  else
  {
    size_t begin = get_level_begin(level);
    size_t end   = get_level_end(level);
    assert(end - begin > 0);
    auto it = d_weights.begin();
    idx     = rng.pick_weighted<size_t>(it + begin, it + end);
    idx += begin;
    assert(begin <= idx);
    assert(idx < end);
  }

  Term t     = d_terms[idx];
  d_refs[idx] += 1;  // increment reference count
  d_refs_sum += 1;

  /* d_terms[idx] was freshly added before, now compute new weight. */
  if (d_weights[idx] == MURXLA_PICK_MAX_WEIGHT)
  {
    d_weights[idx] = d_refs_sum - d_refs[idx] + 1;
  }

  return t;
}

size_t
TermRefs::size() const
{
  return d_idx.size();
}

void
TermRefs::push()
{
  d_levels.push_back(0);
}

void
TermRefs::pop()
{
  assert(d_levels.size() > 1);

  /* Find start of current level. */
  size_t begin = get_level_begin(d_levels.size() - 1);

  /* Erase all terms from current level. */
  std::vector<Term> removed;
  for (auto it = d_terms.begin() + begin; it != d_terms.end(); ++it)
  {
    d_idx.erase(*it);
    removed.push_back(*it);
  }
  d_terms.erase(d_terms.begin() + begin, d_terms.end());
  d_refs.erase(d_refs.begin() + begin, d_refs.end());
  d_weights.erase(d_weights.begin() + begin, d_weights.end());
  assert(d_idx.size() == d_terms.size());
  assert(d_terms.size() == d_refs.size());
  assert(d_refs.size() == d_weights.size());

  d_levels.pop_back();
  // TODO: restore d_refs_sum
}

size_t
TermRefs::get_num_terms(size_t level) const
{
  assert(level < d_levels.size());
  return d_levels[level];
}

size_t
TermRefs::get_level_begin(size_t level)
{
  assert(level < d_levels.size());

  size_t offset = 0;
  for (size_t i = 0; i < level; ++i)
  {
    offset += d_levels[i];
  }
  return offset;
}

size_t
TermRefs::get_level_end(size_t level)
{
  assert(level < d_levels.size());

  size_t offset = 0;
  for (size_t i = 0; i <= level; ++i)
  {
    offset += d_levels[i];
  }
  return offset;
}

/* -------------------------------------------------------------------------- */

TermDb::TermDb(SolverManager& smgr, RNGenerator& rng) : d_smgr(smgr), d_rng(rng)
{
  d_vars.emplace_back();
}

void
TermDb::clear()
{
  d_term_db.clear();
  d_terms.clear();
  d_terms_intermediate.clear();
  d_term_sorts.clear();
  d_funs.clear();
  d_vars.clear();
}

void
TermDb::reset()
{
  clear();
  d_vars.emplace_back();
}

size_t
TermDb::max_level() const
{
  return d_vars.size() - 1;
}

uint32_t
TermDb::get_num_vars() const
{
  return d_vars.size() - 1;
}

void
TermDb::add_term(Term& term,
                 Sort& sort,
                 SortKind sort_kind,
                 const std::vector<Term>& args)
{
  assert(term.get());
  assert(sort.get());
  assert(sort_kind != SORT_ANY);
  assert(sort_kind != SORT_BV || sort->get_bv_size() <= MURXLA_BW_MAX);

  if (term->get_id() != 0)
  {
    assert(get_term(term->get_id()) != nullptr);
    return;
  }

  assert(term->get_sort() == nullptr || term->get_sort() == sort);

  /* Determine scope level of term. */
  std::vector<uint64_t> levels = term->get_levels();
  if (levels.empty())
  {
    std::set<uint64_t> clevels;
    for (const auto& child : args)
    {
      const auto& cl = child->get_levels();
      clevels.insert(cl.begin(), cl.end());
    }
    levels.insert(levels.end(), clevels.begin(), clevels.end());
  }

  /* This should only occur when a new binder (e.g., quantifier) was created. */
  while (levels.size() > 0 && levels.back() >= d_vars.size())
  {
    levels.pop_back();
  }
  uint64_t level = levels.empty() ? 0 : levels.back();
  assert(levels.size() < d_vars.size());

  d_smgr.add_sort(sort, sort_kind);
  assert(sort->get_id());
  assert(sort->get_kind() != SORT_ANY);

  /* Sort may not be set since term is a fresh term. */
  term->set_sort(sort);

  /* We only store regular terms in d_term_db, intermediate terms are only
   * added to d_terms_intermediate. */
  if (d_intermediate_op_kinds.find(term->get_kind())
      != d_intermediate_op_kinds.end())
  {
    term->set_id(d_terms.size() + d_terms_intermediate.size() + 1);
    term->set_levels(levels);
    // no need to wrap into Trefs since we may not pick these terms
    d_terms_intermediate.emplace(term->get_id(), term);
    // no need to add to d_term_sorts for the same reason
  }
  else
  {
    SortMap& map = d_term_db[sort_kind];
    auto it      = map.find(sort);

    if (it == map.end())
    {
      map.emplace(sort, d_vars.size());
    }
    TermRefs& trefs = map.at(sort);

    if (!trefs.contains(term))
    {
      term->set_id(d_terms.size() + d_terms_intermediate.size() + 1);
      term->set_levels(levels);
      trefs.add(term, level);

      d_terms.emplace(term->get_id(), term);
      d_term_sorts.insert(sort);

      if (sort_kind == SORT_FUN)
      {
        // last sort in get_sorts() is codomain sort
        uint32_t arity = term->get_sort()->get_sorts().size() - 1;
        d_funs[arity].insert(term);
      }

      /* If subtyping is enabled, we additionally store SORT_INT terms in
       * SORT_REAL. */
      if (d_smgr.d_arith_subtyping && sort_kind == SORT_INT
          && d_smgr.has_sort(SORT_REAL))
      {
        SortMap& map = d_term_db[SORT_REAL];
        /* It is guaranteed that this sort exists when subtyping is enabled. */
        Sort s = d_smgr.pick_sort(SORT_REAL, false);

        auto it = map.find(sort);
        if (it == map.end())
        {
          map.emplace(s, d_vars.size());
        }
        TermRefs& trefs = map.at(s);

        if (!trefs.contains(term))
        {
          trefs.add(term, level);
          d_term_sorts.insert(s);
        }
      }
    }
    else
    {
      term = trefs.get(term);
      assert(term->get_id());
    }
  }
  assert(term->get_sort()->get_id());
  assert(term->get_sort()->get_kind() != SORT_ANY);
}

void
TermDb::add_input(Term& input, Sort& sort, SortKind sort_kind)
{
  assert(input.get());
  add_term(input, sort, sort_kind);
}

void
TermDb::add_var(Term& var, Sort& sort, SortKind sort_kind)
{
  assert(var.get());
  push(var);
  add_term(var, sort, sort_kind);
}

Term
TermDb::find(Term term, Sort sort, SortKind sort_kind) const
{
  assert(term.get());
  assert(term->get_id() == 0);
  assert(term->get_sort() == nullptr);
  assert(sort.get());
  assert(sort_kind != SORT_ANY);
  assert(sort_kind != SORT_BV || sort->get_bv_size() <= MURXLA_BW_MAX);

  if (sort->get_kind() == SORT_ANY) sort->set_kind(sort_kind);
  assert(sort->get_kind() == sort_kind);
  assert(d_smgr.has_sort(sort));
  term->set_sort(sort);

  if (d_term_db.find(sort_kind) != d_term_db.end())
  {
    const SortMap& map = d_term_db.at(sort_kind);
    if (map.find(sort) != map.end())
    {
      auto t = map.at(sort).get(term);
      if (t != nullptr) return t;
    }
  }
  return nullptr;
}

Term
TermDb::get_term(uint64_t id) const
{
  auto it = d_terms.find(id);
  if (it != d_terms.end()) return it->second;
  it = d_terms_intermediate.find(id);
  if (it != d_terms_intermediate.end()) return it->second;
  return nullptr;
}

const TermDb::SortSet
TermDb::get_sorts() const
{
  return d_term_sorts;
}

bool
TermDb::has_value() const
{
  for (const auto& p : d_term_db)
  {
    for (const auto& pp : p.second)
    {
      for (const auto& t : pp.second)
      {
        if (t->is_value())
        {
          return true;
        }
      }
    }
  }
  return false;
}

bool
TermDb::has_value(Sort sort) const
{
  assert(sort != nullptr);
  if (has_term(sort))
  {
    SortKind s_kind = sort->get_kind();
    assert(d_term_db.find(s_kind) != d_term_db.end());
    assert(d_term_db.at(s_kind).find(sort) != d_term_db.at(s_kind).end());
    const TermRefs& terms = d_term_db.at(s_kind).at(sort);
    for (const auto& t : terms)
    {
      if (t->get_leaf_kind() == AbsTerm::LeafKind::VALUE)
      {
        return true;
      }
    }
  }
  return false;
}

bool
TermDb::has_term(SortKind kind) const
{
  if (kind == SORT_ANY) return has_term();
  return d_term_db.find(kind) != d_term_db.end();
}

bool
TermDb::has_term(SortKind kind, size_t level) const
{
  if (d_term_db.empty()) return false;
  if (kind == SORT_ANY)
  {
    for (const auto& p : d_term_db)
    {
      for (const auto& pp : p.second)
      {
        if (pp.second.get_num_terms(level) > 0)
        {
          return true;
        }
      }
    }
  }

  auto it = d_term_db.find(kind);
  if (it != d_term_db.end())
  {
    for (const auto& p : it->second)
    {
      if (p.second.get_num_terms(level) > 0)
      {
        return true;
      }
    }
  }
  return false;
}

bool
TermDb::has_term(const SortKindSet& kinds) const
{
  SortKindSet sk;
  for (const SortKind& k : kinds)
  {
    if (d_term_db.find(k) != d_term_db.end())
    {
      return true;
    }
  }
  return false;
}

bool
TermDb::has_term(Sort sort) const
{
  assert(sort != nullptr);
  return d_term_sorts.find(sort) != d_term_sorts.end();
}

bool
TermDb::has_term(Sort sort, size_t level) const
{
  assert(sort != nullptr);
  SortKind sort_kind = sort->get_kind();
  if (!has_term(sort_kind, level)) return false;
  const auto& smap = d_term_db.at(sort_kind);
  if (smap.find(sort) == smap.end())
  {
    return false;
  }
  return smap.at(sort).get_num_terms(level) > 0;
}

bool
TermDb::has_term(size_t level) const
{
  for (const auto& t : d_term_db)
  {
    const auto& smap = t.second;
    for (const auto& s : smap)
    {
      if (smap.at(s.first).get_num_terms(level) > 0) return true;
      ;
    }
  }
  return false;
}

bool
TermDb::has_term() const
{
  return d_terms.size() > 0;
}

bool
TermDb::has_fun(const std::vector<Sort>& domain_sorts) const
{
  uint32_t arity = domain_sorts.size();
  if (d_funs.find(arity) == d_funs.end()) return false;
  for (const auto& t : d_funs.at(arity))
  {
    const auto& dsorts = t->get_sort()->get_sorts();
    // Last sort in dsorts is codomain sort
    assert(domain_sorts.size() == dsorts.size() - 1);
    bool match = true;
    for (size_t i = 0, n = domain_sorts.size(); i < n; ++i)
    {
      if (dsorts[i] != domain_sorts[i])
      {
        match = false;
        break;
      }
    }
    if (match) return true;
  }
  return false;
}

bool
TermDb::has_var() const
{
  return d_vars.size() > 1;
}

bool
TermDb::has_quant_body() const
{
  if (!has_var()) return false;
  return has_term(SORT_BOOL, max_level());
}

bool
TermDb::has_quant_term(SortKind sort_kind) const
{
  if (!has_var()) return false;
  return has_term(sort_kind, max_level());
}

bool
TermDb::has_quant_term(Sort sort) const
{
  if (!has_var()) return false;
  return has_term(sort, max_level());
}

Term
TermDb::pick_value() const
{
  assert(has_value());
  std::vector<Term> values;
  for (const auto& p : d_term_db)
  {
    for (const auto& pp : p.second)
    {
      for (const auto& t : pp.second)
      {
        if (t->is_value())
        {
          values.push_back(t);
        }
      }
    }
  }
  assert(!values.empty());
  return d_rng.pick_from_set<std::vector<Term>, Term>(values);
}

Term
TermDb::pick_value(Sort sort) const
{
  assert(has_value(sort));
  assert(d_smgr.has_sort(sort));

  std::vector<Term> values;
  SortKind s_kind = sort->get_kind();
  assert(d_term_db.find(s_kind) != d_term_db.end());
  assert(d_term_db.at(s_kind).find(sort) != d_term_db.at(s_kind).end());
  const TermRefs& terms = d_term_db.at(s_kind).at(sort);
  for (auto& t : terms)
  {
    if (t->get_leaf_kind() == AbsTerm::LeafKind::VALUE)
    {
      values.push_back(t);
    }
  }
  assert(!values.empty());
  return d_rng.pick_from_set<std::vector<Term>, Term>(values);
}

size_t
TermDb::get_num_terms(SortKind sort_kind, size_t level) const
{
  assert(sort_kind != SORT_ANY);
  size_t res = 0;
  if (d_term_db.find(sort_kind) != d_term_db.end())
  {
    for (const auto& p : d_term_db.at(sort_kind))
    {
      res += p.second.get_num_terms(level);
    }
  }
  return res;
}

size_t
TermDb::get_num_terms(size_t level) const
{
  size_t res = 0;
  for (const auto& s : d_term_db)
  {
    for (const auto& t : s.second)
    {
      res += t.second.get_num_terms(level);
    }
  }
  return res;
}

size_t
TermDb::get_num_terms(SortKind sort_kind) const
{
  return get_num_terms(sort_kind, d_vars.size() - 1);
}

Term
TermDb::pick_term(Sort sort, size_t level)
{
  assert(has_term(sort, level));
  assert(d_smgr.has_sort(sort));
  SortKind sort_kind = sort->get_kind();
  auto it            = d_term_db.find(sort_kind);
  assert(it != d_term_db.end());
  SortMap& smap = it->second;
  assert(smap.find(sort) != smap.end());
  assert(smap.at(sort).get_num_terms(level) > 0);
  return smap.at(sort).pick(d_rng, level);
}

Term
TermDb::pick_term(Sort sort)
{
  assert(has_term(sort));
  assert(d_smgr.has_sort(sort));
  return d_term_db.at(sort->get_kind()).at(sort).pick(d_rng);
}

Term
TermDb::pick_term(SortKind sort_kind, size_t level)
{
  assert(sort_kind != SORT_ANY);
  assert(has_term(sort_kind, level));
  assert(level < d_vars.size());
  assert(d_term_db.find(sort_kind) != d_term_db.end());

  SortMap& smap = d_term_db.at(sort_kind);
  /* Collect sorts with terms in given level. */
  std::vector<Sort> sorts_with_terms;
  for (const auto& [sort, tref] : smap)
  {
    if (tref.get_num_terms(level) > 0)
    {
      sorts_with_terms.push_back(sort);
    }
  }
  assert(!sorts_with_terms.empty());
  Sort sort = d_rng.pick_from_set<std::vector<Sort>, Sort>(sorts_with_terms);
  return smap.at(sort).pick(d_rng, level);
}

Term
TermDb::pick_term(SortKind sort_kind)
{
  assert(sort_kind != SORT_ANY);
  assert(has_term(sort_kind));
  return pick_term(pick_sort(sort_kind));
}

Term
TermDb::pick_term()
{
  assert(has_term());
  return pick_term(pick_sort_kind());
}

Term
TermDb::pick_term(size_t level)
{
  assert(has_term(level));
  return pick_term(pick_sort_kind(level), level);
}

Term
TermDb::pick_fun(const std::vector<Sort>& domain_sorts)
{
  assert(has_fun(domain_sorts));
  uint32_t arity = domain_sorts.size();
  std::vector<Term> funs;
  for (const auto& t : d_funs.at(arity))
  {
    const auto& dsorts = t->get_sort()->get_sorts();
    // Last sort in dsorts is codomain sort
    bool match = true;
    for (size_t i = 0, n = domain_sorts.size(); i < n; ++i)
    {
      if (dsorts[i] != domain_sorts[i])
      {
        match = false;
        break;
      }
    }
    if (match) funs.push_back(t);
  }
  return d_rng.pick_from_set<std::vector<Term>, Term>(funs);
}

SortKind
TermDb::pick_sort_kind() const
{
  assert(has_term());
  auto it = d_term_db.begin();
  std::advance(it, d_rng.pick<size_t>(0, d_term_db.size() - 1));
  return it->first;
}

SortKind
TermDb::pick_sort_kind(size_t level,
                       const SortKindSet& exclude_sort_kinds) const
{
  assert(has_term());

  std::unordered_set<SortKind> kinds;
  for (const auto& p : d_term_db)
  {
    if (exclude_sort_kinds.find(p.first) == exclude_sort_kinds.end())
    {
      for (const auto& pp : p.second)
      {
        if (pp.second.get_num_terms(level) > 0)
        {
          kinds.insert(p.first);
          break;
        }
      }
    }
  }
  return d_rng.pick_from_set<SortKindSet, SortKind>(kinds);
}

SortKind
TermDb::pick_sort_kind(const SortKindSet& sort_kinds) const
{
  assert(has_term());

  std::unordered_set<SortKind> kinds;
  for (const auto& p : d_term_db)
  {
    if (sort_kinds.find(p.first) != sort_kinds.end()) kinds.insert(p.first);
  }
  return d_rng.pick_from_set<SortKindSet, SortKind>(kinds);
}

SortKind
TermDb::pick_sort_kind_excluding(const SortKindSet& exclude_sort_kinds) const
{
  assert(has_term());

  std::unordered_set<SortKind> kinds;
  for (const auto& p : d_term_db)
  {
    if (exclude_sort_kinds.find(p.first) == exclude_sort_kinds.end())
    {
      kinds.insert(p.first);
    }
  }
  return d_rng.pick_from_set<SortKindSet, SortKind>(kinds);
}

Sort
TermDb::pick_sort(SortKind sort_kind) const
{
  assert(sort_kind != SORT_ANY);
  assert(has_term(sort_kind));

  assert(d_term_db.find(sort_kind) != d_term_db.end());
  Sort res = d_rng.pick_from_map<SortMap, Sort>(d_term_db.at(sort_kind));
  assert(res->get_id());
  assert(res->get_kind() != SORT_ANY);
  return res;
}

Sort
TermDb::pick_sort(const SortKindSet& sort_kinds) const
{
  assert(has_term(sort_kinds));
  return pick_sort(pick_sort_kind(sort_kinds));
}

Term
TermDb::pick_var() const
{
  assert(has_var());
  assert(d_vars.size() > 1);
  return d_vars[max_level()];
}

std::vector<Term>
TermDb::pick_vars(uint32_t num_vars) const
{
  assert(d_vars.size() > num_vars);
  std::vector<Term> res;
  size_t level = max_level();
  for (size_t i = 0; i < level; ++i)
  {
    res.push_back(d_vars[level - i]);
  }
  return res;
}

void
TermDb::remove_var(const Term& var)
{
  pop(var);
}

Term
TermDb::pick_quant_body()
{
  assert(has_quant_body());
  return pick_term(SORT_BOOL, max_level());
}

Term
TermDb::pick_quant_term(SortKind sort_kind)
{
  assert(has_quant_term(sort_kind));
  size_t level = max_level();
  if (sort_kind == SORT_ANY) sort_kind = pick_sort_kind(level);
  return pick_term(sort_kind, level);
}

Term
TermDb::pick_quant_term(Sort sort)
{
  assert(has_quant_term(sort));
  return pick_term(sort, max_level());
}

void
TermDb::push(Term& var)
{
  var->set_levels({d_vars.size()});
  d_vars.push_back(var);

  for (auto& p : d_term_db)
  {
    for (auto& q : p.second)
    {
      q.second.push();
    }
  }
}

void
TermDb::pop(const Term& var)
{
  const std::vector<uint64_t>& levels = var->get_levels();
  assert(levels.size() == 1);
  size_t level = levels.back();
  assert(level == d_vars.size() - 1);
  assert(d_vars[level] == var);

  d_vars.pop_back();

  /* Pop current level from d_term_db and cleanup. */
  for (auto it = d_term_db.begin(); it != d_term_db.end();)
  {
    auto& skind = it->first;
    auto& skmap = it->second;
    ++it;

    for (auto iit = skmap.begin(); iit != skmap.end();)
    {
      auto& tref       = iit->second;
      const auto& sort = iit->first;
      ++iit;

      tref.pop();

      /* Remove sorts without terms. */
      if (tref.size() == 0)
      {
        skmap.erase(sort);
      }
    }

    /* Remove sort kinds without terms. */
    if (skmap.empty())
    {
      d_term_db.erase(skind);
    }
  }

  /* Recompute d_term_sorts */
  d_term_sorts.clear();
  for (const auto& p : d_term_db)
  {
    assert(!p.second.empty());
    for (const auto& pp : p.second)
    {
      assert(pp.second.size() > 0);
      d_term_sorts.insert(pp.first);
    }
  }
}

}  // namespace murxla
