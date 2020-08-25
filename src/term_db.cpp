#include "term_db.hpp"

#include <algorithm>

#include "config.hpp"
#include "solver_manager.hpp"

namespace smtmbt {

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
  d_vars.clear();
}

void
TermDb::add_term(Term& term,
                 Sort& sort,
                 SortKind sort_kind,
                 const std::vector<Term>& args)
{
  assert(term.get());
  assert(term->get_id() == 0);
  assert(term->get_sort() == nullptr);
  assert(sort.get());
  assert(sort_kind != SORT_ANY);
  assert(sort_kind != SORT_BV || sort->get_bv_size() <= SMTMBT_BW_MAX);

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

  uint64_t level = levels.empty() ? 0 : levels.back();

  /* This should only occur when a new quantifier was created. */
  if (level >= d_vars.size())
  {
    assert(level == levels.back());
    levels.pop_back();
    level = levels.empty() ? 0 : levels.back();
  }
  assert(levels.size() < d_vars.size());

  // TODO: check if still needed
  /* add term to terms */
  //  if (terms.find(sort_kind) == terms.end())
  //  {
  //    assert(d_n_sort_terms.find(sort_kind) == d_n_sort_terms.end());
  //    d_n_sort_terms.emplace(sort_kind, 1);
  //  }
  //  else
  //  {
  //    d_n_sort_terms.at(sort_kind) += 1;
  //  }

  SortMap& map  = d_term_db[level][sort_kind];
  TermMap& tmap = map[sort];

  d_smgr.add_sort(sort, sort_kind);
  /* Sort may not be set since term is a fresh term. */
  term->set_sort(sort);

  if (tmap.find(term) == tmap.end())
  {
    term->set_id(d_terms.size() + 1);
    term->set_levels(levels);
    tmap.emplace(term, 0);

    // TODO:
    // d_stats.terms += 1;
    d_terms.emplace(term->get_id(), term);
    d_term_sorts.insert(sort);
  }
  else
  {
    term = tmap.find(term)->first;
    assert(term->get_id());
    assert(term->get_levels().empty() || term->get_levels().back() == level);
    assert(!term->get_levels().empty() || level == 0);
  }
  // TODO: increment reference count of args
  tmap.at(term) += 1;
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
  assert(sort_kind != SORT_BV || sort->get_bv_size() <= SMTMBT_BW_MAX);

  if (sort->get_kind() == SORT_ANY) sort->set_kind(sort_kind);
  assert(sort->get_kind() == sort_kind);
  assert(d_smgr.has_sort(sort));
  term->set_sort(sort);

  for (const auto& stmap : d_term_db)
  {
    const SortMap& map = stmap.at(sort_kind);
    if (map.find(sort) != map.end())
    {
      auto it = map.at(sort).find(term);
      if (it != map.at(sort).end()) return it->first;
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
  if (d_term_sorts.find(sort) == d_term_sorts.end()) return false;
  SortKind sort_kind = sort->get_kind();
  for (const auto& level : d_term_db)
  {
    assert(level.find(sort_kind) != level.end());
    assert(level.at(sort_kind).find(sort) != level.at(sort_kind).end());
    const TermMap& terms = level.at(sort_kind).at(sort);
    for (const auto& p : terms)
    {
      if (p.first->is_value()) return true;
    }
  }
  return false;
}

bool
TermDb::has_term(SortKind kind) const
{
  if (kind == SORT_ANY) return has_term();
  for (const auto& tmap : d_term_db)
  {
    if (tmap.find(kind) != tmap.end())
    {
      return true;
    }
  }
  return false;
}

bool
TermDb::has_term(SortKind kind, size_t level) const
{
  if (d_term_db.empty()) return false;
  if (kind == SORT_ANY) return has_term();
  return d_term_db[level].find(kind) != d_term_db[level].end();
}

bool
TermDb::has_term(Sort sort) const
{
  return d_term_sorts.find(sort) != d_term_sorts.end();
}

bool
TermDb::has_term() const
{
  return d_terms.size() > 0;
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
  size_t max_level = d_vars.size() - 1;
  return has_term(SORT_BOOL, max_level);
}

Term
TermDb::pick_value(Sort sort)
{
  assert(has_value(sort));
  assert(d_smgr.has_sort(sort));

  SortKind sort_kind = sort->get_kind();
  std::vector<Term> values;
  for (auto& level : d_term_db)
  {
    assert(level.find(sort_kind) != level.end());
    assert(level.at(sort_kind).find(sort) != level.at(sort_kind).end());
    TermMap& terms = level.at(sort_kind).at(sort);
    for (auto& p : terms)
    {
      if (p.first->is_value()) values.push_back(p.first);
    }
  }
  assert(!values.empty());
  return d_rng.pick_from_set<std::vector<Term>, Term>(values);
}

Term
TermDb::pick_term(Sort sort)
{
  assert(has_term(sort));
  assert(d_smgr.has_sort(sort));

  size_t level       = pick_level(sort);
  SortKind sort_kind = sort->get_kind();
  assert(d_term_db[level].find(sort_kind) != d_term_db[level].end());
  SortMap& smap = d_term_db[level].at(sort_kind);
  assert(smap.find(sort) != smap.end());
  return d_rng.pick_from_map<TermMap, Term>(smap.at(sort));
}

Term
TermDb::pick_term(SortKind sort_kind, size_t level)
{
  assert(sort_kind != SORT_ANY);
  assert(has_term(sort_kind));
  assert(level < d_term_db.size());
  assert(d_term_db[level].find(sort_kind) != d_term_db[level].end());

  SortMap& smap = d_term_db[level].at(sort_kind);
  Sort sort     = d_rng.pick_from_map<SortMap, Sort>(smap);
  return d_rng.pick_from_map<TermMap, Term>(smap.at(sort));
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

SortKind
TermDb::pick_sort_kind()
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

Sort
TermDb::pick_sort(SortKind sort_kind)
{
  assert(sort_kind != SORT_ANY);
  assert(has_term(sort_kind));
  size_t level = pick_level(sort_kind);
  assert(d_term_db[level].find(sort_kind) != d_term_db[level].end());
  return d_rng.pick_from_map<SortMap, Sort>(d_term_db[level].at(sort_kind));
}

Term
TermDb::pick_var()
{
  assert(has_var());
  assert(d_vars.size() > 1);
  size_t max_level = d_vars.size() - 1;

  return d_vars[max_level];
}

void
TermDb::remove_var(Term& var)
{
  pop(var);
}

Term
TermDb::pick_quant_body()
{
  assert(has_var());
  assert(d_term_db.size() > 1);
  size_t max_level = d_vars.size() - 1;
  assert(has_term(SORT_BOOL, max_level));
  return pick_term(SORT_BOOL, max_level);
}

//  void remove_vars(const std::vector<Term>& vars);
//

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
TermDb::pick_level(SortKind kind) const
{
  assert(kind != SORT_ANY);
  assert(has_term(kind));

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

}  // namespace smtmbt
