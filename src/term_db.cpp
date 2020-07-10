#include "term_db.hpp"

#include "solver_manager.hpp"

namespace smtmbt {

TermDb::TermDb(SolverManager& smgr, RNGenerator& rng) : d_smgr(smgr), d_rng(rng)
{
  d_term_db.emplace_back();
}

void
TermDb::clear()
{
  d_term_db.clear();
  d_terms.clear();
  d_term_sorts.clear();
  d_term_sort_kinds.clear();
  d_n_terms = 0;
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

  uint64_t level = term->get_level();
  if (level == 0)
  {
    uint64_t clevel;
    for (const auto& child : args)
    {
      clevel = child->get_level();
      if (clevel > level)
      {
        level = clevel;
      }
    }
  }

  assert(level < d_term_db.size());

  // TODO: check
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
    term->set_id(++d_n_terms);
    term->set_level(level);
    tmap.emplace(term, 0);

    // TODO:
    // d_stats.terms += 1;
    d_terms.emplace(term->get_id(), term);
    d_term_sort_kinds.insert(sort_kind);
    d_term_sorts.insert(sort);
  }
  else
  {
    term = tmap.find(term)->first;
    assert(term->get_id());
    assert(term->get_level() == level);
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
TermDb::add_var(Term var)
{
  assert(var.get());

  /* Add variable to current scope or open new scope. */
  uint64_t level;
  if (d_rng.flip_coin())
  {
    level = d_term_db.size();
    d_term_db.emplace_back();
  }
  else
  {
    level = d_term_db.size() - 1;
  }
  var->set_level(level);

  //  d_stats.inputs += 1;
  Sort sort = var->get_sort();
  add_term(var, sort, sort->get_kind());
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
TermDb::get_term(uint32_t id) const
{
  auto it = d_terms.find(id);
  if (it != d_terms.end()) return it->second;
  return nullptr;
}

const TermDb::SortKindSet
TermDb::get_sort_kinds() const
{
  return d_term_sort_kinds;
}

const TermDb::SortSet
TermDb::get_sorts() const
{
  return d_term_sorts;
}

bool
TermDb::has_term(SortKind kind) const
{
  if (kind == SORT_ANY) return has_term();
  return d_term_sort_kinds.find(kind) != d_term_sort_kinds.end();
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

Term
TermDb::pick_term(Sort sort)
{
  assert(has_term(sort));
  assert(d_smgr.has_sort(sort));

  SortKind sort_kind = sort->get_kind();
  size_t level       = pick_level(sort_kind);
  SortMap& smap      = d_term_db[level].at(sort_kind);
  return d_rng.pick_from_map<TermMap, Term>(smap.at(sort));
}

Term
TermDb::pick_term(SortKind sort_kind)
{
  assert(sort_kind != SORT_ANY);
  assert(has_term(sort_kind));

  size_t level = pick_level(sort_kind);
  assert(level < d_term_db.size());
  assert(d_term_db[level].find(sort_kind) != d_term_db[level].end());
  SortMap& smap = d_term_db[level].at(sort_kind);
  Sort sort     = d_rng.pick_from_map<SortMap, Sort>(smap);
  return d_rng.pick_from_map<TermMap, Term>(smap.at(sort));
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
  return d_rng.pick_from_set<SortKindSet, SortKind>(d_term_sort_kinds);
}

Sort
TermDb::pick_sort(SortKind sort_kind)
{
  assert(sort_kind != SORT_ANY);
  size_t level = pick_level(sort_kind);
  return d_rng.pick_from_map<SortMap, Sort>(d_term_db[level].at(sort_kind));
}

//  Term pick_free_vars();
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

  std::vector<size_t> levels;
  for (size_t i = 0; i < d_term_db.size(); ++i)
  {
    if (d_term_db[i].find(kind) != d_term_db[i].end())
    {
      levels.push_back(i + 1);
    }
  }
  assert(!levels.empty());
  return d_rng.pick_weighted<size_t>(levels);
}

size_t
TermDb::pick_level(Sort sort) const
{
  assert(has_term(sort));

  std::vector<size_t> levels;
  SortKind kind = sort->get_kind();
  for (size_t i = 0; i < d_term_db.size(); ++i)
  {
    if (d_term_db[i].find(kind) == d_term_db[i].end()) continue;
    if (d_term_db[i].at(kind).find(sort) != d_term_db[i].at(kind).end())
    {
      levels.push_back(i + 1);
    }
  }
  assert(!levels.empty());
  return d_rng.pick_weighted<size_t>(levels);
}

}  // namespace smtmbt
