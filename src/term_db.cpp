#include "term_db.hpp"

#include <algorithm>

#include "config.hpp"
#include "solver_manager.hpp"

namespace murxla {

void
TermRefs::add(const Term& t)
{
  if (d_idx.find(t) == d_idx.end())
  {
    d_idx.emplace(t, d_refs.size());
    d_terms.push_back(t);
    d_refs.push_back(0);
    /* Weight must be at least 1. Weight 0 corresponds to preventing the term
     * from being picked, and when all have weight 0, always the first one will
     * be picked.  This is due to how RNGenerator::pick_weighted is implemented
     * via std::discrete_distribution. */
    d_weights.push_back(1);
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
TermRefs::pick(RNGenerator& rng)
{
  /* Terms with higher reference count have lower probability to be picked. */
  if (d_refs_sum % 100 == 25)
  {
    assert(d_weights.size() == d_refs.size());
    for (size_t i = 0; i < d_weights.size(); ++i)
    {
      d_weights[i] = d_refs_sum - d_refs[i] + 1;
    }
  }

  size_t idx = rng.pick_weighted(d_weights);
  Term t     = d_terms[idx];
  d_refs[idx] += 1;  // increment reference count
  d_refs_sum += 1;
  return t;
}

size_t
TermRefs::size() const
{
  return d_idx.size();
}

TermDb::TermDb(SolverManager& smgr, RNGenerator& rng) : d_smgr(smgr), d_rng(rng)
{
  d_term_db.emplace_back();
  d_vars.emplace_back();
}

void
TermDb::clear()
{
  d_term_db.clear();
  d_terms.clear();
  d_term_sorts.clear();
  d_funs.clear();
  d_vars.clear();
}

void
TermDb::reset()
{
  clear();
  d_term_db.emplace_back();
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
    std::unordered_set<uint64_t> clevels;
    for (const auto& child : args)
    {
      auto cl = child->get_levels();
      clevels.insert(cl.begin(), cl.end());
    }
    levels.insert(levels.end(), clevels.begin(), clevels.end());
    std::sort(levels.begin(), levels.end());
  }

  /* This should only occur when a new binder (e.g., quantifier) was created. */
  while (levels.size() > 0 && levels.back() >= d_vars.size())
  {
    levels.pop_back();
  }
  uint64_t level = levels.empty() ? 0 : levels.back();
  assert(levels.size() < d_vars.size());

  /* If sort_kind is SORT_REAL, given sort can only be an Int sort when the
   * solver identifies it as an Int sort (since Int may be a subtype of Real).
   * We don't infer this based on the arguments but delegate this inference
   * to the solver. We always store terms of sort Int under sort kind SORT_INT,
   * even if they were created from a Real operator (and thus, the expected
   * sort kind sort_kind = SORT_REAL).  */
  if (sort_kind == SORT_REAL && sort->is_int())
  {
    sort_kind = SORT_INT;
  }

  SortMap& map  = d_term_db[level][sort_kind];
  d_smgr.add_sort(sort, sort_kind);
  assert(sort->get_id());
  assert(sort->get_kind() != SORT_ANY);
  TermRefs& trefs = map[sort];

  /* Sort may not be set since term is a fresh term. */
  term->set_sort(sort);

  if (!trefs.contains(term))
  {
    term->set_id(d_terms.size() + 1);
    term->set_levels(levels);
    trefs.add(term);

    d_terms.emplace(term->get_id(), term);
    d_term_sorts.insert(sort);
  }
  else
  {
    term = trefs.get(term);
    assert(term->get_id());
    assert(term->get_levels().empty() || term->get_levels().back() == level);
    assert(!term->get_levels().empty() || level == 0);
  }
  assert(term->get_sort()->get_id());
  assert(term->get_sort()->get_kind() != SORT_ANY);

  if (sort_kind == SORT_FUN)
  {
    // last sort in get_sorts() is codomain sort
    uint32_t arity = term->get_sort()->get_sorts().size() - 1;
    d_funs[arity].insert(term);
  }
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

  //  d_stats.inputs += 1;
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

  for (const auto& stmap : d_term_db)
  {
    if (stmap.find(sort_kind) != stmap.end())
    {
      const SortMap& map = stmap.at(sort_kind);
      if (map.find(sort) != map.end())
      {
        auto t = map.at(sort).get(term);
        if (t != nullptr) return t;
      }
    }
  }
  return nullptr;
}

Term
TermDb::get_term(uint64_t id) const
{
  auto it = d_terms.find(id);
  if (it != d_terms.end()) return it->second;
  return nullptr;
}

const TermDb::SortSet
TermDb::get_sorts() const
{
  return d_term_sorts;
}

bool
TermDb::has_value(Sort sort) const
{
  assert(sort != nullptr);
  std::vector<Sort> sorts = {sort};
  if (d_smgr.d_arith_subtyping && sort->get_kind() == SORT_REAL
      && has_term(SORT_INT))
  {
    sorts.push_back(pick_sort(SORT_INT));
  }
  for (const Sort& s : sorts)
  {
    if (!has_term(s)) continue;
    SortKind s_kind = s->get_kind();
    for (const auto& level : d_term_db)
    {
      assert(level.find(s_kind) != level.end());
      assert(level.at(s_kind).find(s) != level.at(s_kind).end());
      const TermRefs& terms = level.at(s_kind).at(s);
      for (const auto& t : terms)
      {
        if (t->get_leaf_kind() == AbsTerm::LeafKind::VALUE)
        {
          return true;
        }
      }
    }
  }
  return false;
}

bool
TermDb::has_term(SortKind kind) const
{
  if (kind == SORT_ANY) return has_term();
  std::vector<SortKind> sort_kinds = {kind};
  if (d_smgr.d_arith_subtyping && kind == SORT_REAL)
  {
    sort_kinds.push_back(SORT_INT);
  }
  for (const SortKind& k : sort_kinds)
  {
    for (const auto& tmap : d_term_db)
    {
      if (tmap.find(k) != tmap.end())
      {
        return true;
      }
    }
  }
  return false;
}

bool
TermDb::has_term(SortKind kind, size_t level) const
{
  if (d_term_db.empty()) return false;
  if (kind == SORT_ANY) return !d_term_db[level].empty();
  std::vector<SortKind> sort_kinds = {kind};
  if (d_smgr.d_arith_subtyping && kind == SORT_REAL)
  {
    sort_kinds.push_back(SORT_INT);
  }
  for (const SortKind& k : sort_kinds)
  {
    if (d_term_db[level].find(k) != d_term_db[level].end()) return true;
  }
  return false;
}

bool
TermDb::has_term(const SortKindSet& kinds) const
{
  SortKindSet sk;
  const SortKindSet* sort_kinds = &kinds;
  if (d_smgr.d_arith_subtyping && kinds.find(SORT_REAL) != kinds.end()
      && kinds.find(SORT_INT) == kinds.end())
  {
    sk = kinds;
    sk.insert(SORT_INT);
    sort_kinds = &sk;
  }
  for (const SortKind& k : *sort_kinds)
  {
    for (const auto& tmap : d_term_db)
    {
      if (tmap.find(k) != tmap.end())
      {
        return true;
      }
    }
  }
  return false;
}

bool
TermDb::has_term(Sort sort) const
{
  assert(sort != nullptr);
  std::vector<Sort> sorts = {sort};
  if (d_smgr.d_arith_subtyping && sort->get_kind() == SORT_REAL
      && has_term(SORT_INT))
  {
    sorts.push_back(pick_sort(SORT_INT));
  }
  for (const Sort& s : sorts)
  {
    if (d_term_sorts.find(s) != d_term_sorts.end()) return true;
  }
  return false;
}

bool
TermDb::has_term(Sort sort, size_t level) const
{
  assert(sort != nullptr);
  SortKind sort_kind = sort->get_kind();
  if (sort_kind == SORT_REAL)
  {
    return has_term(sort_kind, level);
  }
  if (d_term_db[level].find(sort_kind) == d_term_db[level].end()) return false;
  const auto& smap = d_term_db[level].at(sort_kind);
  return smap.find(sort) != smap.end();
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
TermDb::pick_value(Sort sort) const
{
  assert(has_value(sort));
  assert(d_smgr.has_sort(sort));

  std::vector<Sort> sorts = {sort};
  if (d_smgr.d_arith_subtyping && sort->get_kind() == SORT_REAL
      && has_term(SORT_INT))
  {
    sorts.push_back(pick_sort(SORT_INT));
  }

  std::vector<Term> values;
  for (const Sort& s : sorts)
  {
    SortKind s_kind = s->get_kind();
    for (auto& level : d_term_db)
    {
      assert(level.find(s_kind) != level.end());
      assert(level.at(s_kind).find(s) != level.at(s_kind).end());
      const TermRefs& terms = level.at(s_kind).at(s);
      for (auto& t : terms)
      {
        if (t->get_leaf_kind() == AbsTerm::LeafKind::VALUE)
        {
          values.push_back(t);
        }
      }
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
  for (size_t i = 0; i <= level; ++i)
  {
    if (d_term_db[i].find(sort_kind) != d_term_db[i].end())
    {
      for (const auto& p : d_term_db[i].at(sort_kind))
      {
        res += p.second.size();
      }
    }
  }
  return res;
}

size_t
TermDb::get_num_terms(size_t level) const
{
  size_t res = 0;
  for (const auto& s : d_term_db[level])
  {
    for (const auto& t : s.second)
    {
      res += t.second.size();
    }
  }
  return res;
}

size_t
TermDb::get_num_terms(SortKind sort_kind) const
{
  return get_num_terms(sort_kind, d_term_db.size() - 1);
}

Term
TermDb::pick_term(Sort sort, size_t level)
{
  SortKind sort_kind = sort->get_kind();
  if (sort_kind == SORT_REAL)
  {
    return pick_term(sort_kind, level);
  }

  assert(has_term(sort, level));
  assert(d_smgr.has_sort(sort));

  assert(d_term_db[level].find(sort_kind) != d_term_db[level].end());
  SortMap& smap = d_term_db[level].at(sort_kind);
  assert(smap.find(sort) != smap.end());
  return smap.at(sort).pick(d_rng);
}

Term
TermDb::pick_term(Sort sort)
{
  assert(has_term(sort));
  assert(d_smgr.has_sort(sort));

  Sort s = sort;
  if (d_smgr.d_arith_subtyping && sort->get_kind() == SORT_REAL
      && has_term(SORT_INT))
  {
    size_t n_reals = get_num_terms(SORT_REAL);
    size_t n_ints  = get_num_terms(SORT_INT);
    assert(n_reals || n_ints);
    std::vector<size_t> weights = {n_reals, n_ints};
    size_t p                    = d_rng.pick_weighted<size_t>(weights);
    if (p) s = pick_sort(SORT_INT);
  }

  return pick_term(s, pick_level(s));
}

Term
TermDb::pick_term(SortKind sort_kind, size_t level)
{
  assert(sort_kind != SORT_ANY);
  assert(has_term(sort_kind, level));
  assert(level < d_term_db.size());
  if (d_smgr.d_arith_subtyping && sort_kind == SORT_REAL
      && has_term(SORT_INT, level))
  {
    size_t n_reals = get_num_terms(SORT_REAL, level);
    size_t n_ints  = get_num_terms(SORT_INT, level);
    assert(n_reals || n_ints);
    std::vector<size_t> weights = {n_reals, n_ints};
    if (d_rng.pick_weighted<size_t>(weights)) sort_kind = SORT_INT;
  }
  assert(d_term_db[level].find(sort_kind) != d_term_db[level].end());

  SortMap& smap = d_term_db[level].at(sort_kind);
  Sort sort     = d_rng.pick_from_map<SortMap, Sort>(smap);
  return smap.at(sort).pick(d_rng);
}

Term
TermDb::pick_term(SortKind sort_kind)
{
  assert(sort_kind != SORT_ANY);
  assert(has_term(sort_kind));

  size_t level = pick_level(sort_kind);
  return pick_term(sort_kind, level);
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
  assert(has_term());
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

  std::unordered_set<SortKind> kinds;
  for (const auto& tmap : d_term_db)
  {
    for (const auto& p : tmap)
    {
      kinds.insert(p.first);
    }
  }
  return d_rng.pick_from_set<SortKindSet, SortKind>(kinds);
}

SortKind
TermDb::pick_sort_kind(size_t level,
                       const SortKindSet& exclude_sort_kinds) const
{
  assert(has_term());

  std::unordered_set<SortKind> kinds;
  for (const auto& p : d_term_db[level])
  {
    if (exclude_sort_kinds.find(p.first) == exclude_sort_kinds.end())
    {
      kinds.insert(p.first);
    }
  }
  return d_rng.pick_from_set<SortKindSet, SortKind>(kinds);
}

SortKind
TermDb::pick_sort_kind(const SortKindSet& sort_kinds) const
{
  assert(has_term());

  std::unordered_set<SortKind> kinds;
  for (const auto& tmap : d_term_db)
  {
    for (const auto& p : tmap)
    {
      if (sort_kinds.find(p.first) != sort_kinds.end()) kinds.insert(p.first);
    }
  }
  return d_rng.pick_from_set<SortKindSet, SortKind>(kinds);
}

Sort
TermDb::pick_sort(SortKind sort_kind) const
{
  assert(sort_kind != SORT_ANY);
  assert(has_term(sort_kind));
  size_t level = pick_level(sort_kind);
  assert(d_term_db[level].find(sort_kind) != d_term_db[level].end());
  Sort res = d_rng.pick_from_map<SortMap, Sort>(d_term_db[level].at(sort_kind));
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
TermDb::remove_var(Term& var)
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

size_t
TermDb::pick_level() const
{
  assert(has_term());

  std::vector<size_t> levels;
  for (size_t i = 0; i < d_term_db.size(); ++i)
  {
    levels.push_back(i + 1);
  }
  return d_rng.pick_weighted<size_t>(levels);
}

size_t
TermDb::pick_level(SortKind& kind) const
{
  assert(kind != SORT_ANY);
  assert(has_term(kind));

  if (d_smgr.d_arith_subtyping && kind == SORT_REAL && has_term(SORT_INT))
  {
    size_t n_reals = get_num_terms(SORT_REAL);
    size_t n_ints  = get_num_terms(SORT_INT);
    assert(n_reals || n_ints);
    std::vector<size_t> weights = {n_reals, n_ints};
    if (d_rng.pick_weighted<size_t>(weights)) kind = SORT_INT;
  }

  std::vector<size_t> levels(d_term_db.size(), 0);
  for (size_t i = 0; i < d_term_db.size(); ++i)
  {
    if (d_term_db[i].find(kind) != d_term_db[i].end())
    {
      levels[i] = i + 1;
    }
  }
  return d_rng.pick_weighted<size_t>(levels);
}

size_t
TermDb::pick_level(Sort sort) const
{
  assert(has_term(sort));

  std::vector<size_t> levels(d_term_db.size(), 0);
  SortKind kind = sort->get_kind();
  for (size_t i = 0; i < d_term_db.size(); ++i)
  {
    if (d_term_db[i].find(kind) == d_term_db[i].end()) continue;
    if (d_term_db[i].at(kind).find(sort) != d_term_db[i].at(kind).end())
    {
      levels[i] = i + 1;
    }
  }
  return d_rng.pick_weighted<size_t>(levels);
}

void
TermDb::push(Term& var)
{
  var->set_levels({d_vars.size()});
  d_term_db.emplace_back();
  d_vars.push_back(var);
}

void
TermDb::pop(Term& var)
{
  std::vector<uint64_t> levels = var->get_levels();
  assert(levels.size() == 1);
  size_t level = levels.back();
  assert(level == d_vars.size() - 1);
  assert(d_vars[level] == var);

  d_vars.pop_back();
  d_term_db.pop_back();

  /* Recompute d_term_sorts */
  d_term_sorts.clear();
  for (const auto& tmap : d_term_db)
  {
    for (const auto& p : tmap)
    {
      for (const auto& pp : p.second)
      {
        d_term_sorts.insert(pp.first);
      }
    }
  }
}

}  // namespace murxla
