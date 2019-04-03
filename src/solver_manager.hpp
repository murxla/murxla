#ifndef __SMTMBT__SOLVER_MANAGER_H
#define __SMTMBT__SOLVER_MANAGER_H

#include <cassert>
#include <iostream>
#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "fsm.hpp"

namespace smtmbt {

enum TheoryId
{
  THEORY_BOOL,
  THEORY_BV,
  THEORY_ALL,
};

/* -------------------------------------------------------------------------- */

class Action
{
 public:
  Action() = delete;
  Action(RNGenerator& rng, const std::string& id) : d_rng(rng), d_id(id) {}
  virtual ~Action() = default;
  virtual bool run() = 0;
  // virtual void untrace(const char* s) {}
  const std::string& get_id() const { return d_id; }

 protected:
  RNGenerator& d_rng;

 private:
  std::string d_id;
};

/* -------------------------------------------------------------------------- */

template <typename TSolver,
          typename TTerm,
          typename TSort,
          typename THashTerm,
          typename THashSort>
class SolverManager
{
 public:
  using TermMap = std::unordered_map<TTerm, size_t, THashTerm>;
  using SortMap = std::unordered_map<TSort, TermMap, THashSort>;
  using SortSet = std::unordered_set<TSort, THashSort>;

  /* Statistics. */
  struct Stats
  {
    uint32_t inputs = 0;  /* constants, variables */
    uint32_t terms  = 0;   /* all terms, including inputs */
  };

  SolverManager(RNGenerator& rng) : d_fsm(rng), d_solver(nullptr), d_rng(rng) {}
  // TODO: copy/assignment constructors?
  ~SolverManager() = default;

  void set_solver(TSolver s) { d_solver = s; }

  TSolver get_solver() { return d_solver; }

  void set_rng(RNGenerator& rng) { d_rng = rng; }

  RNGenerator& get_rng() { return d_rng; }

  void run() { d_fsm.run(); }

  void add_input(TTerm term, TheoryId theory)
  {
    d_stats.inputs += 1;
    add_term (term, theory);
  }

  void add_term(TTerm term, TheoryId theory)
  {
    d_stats.terms += 1;

    TSort sort = get_sort(term);
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
      map[sort].emplace(copy_term(term), 0);
    }
    else
    {
      map[sort][term] += 1;
    }
  }

  void add_sort(TSort sort, TheoryId theory)
  {
    if (d_sorts2theory.find(sort) == d_sorts2theory.end())
    {
      d_sorts2theory.emplace(copy_sort(sort), theory);
    }

    if (d_theory2sorts.find(theory) == d_theory2sorts.end())
    {
      d_theory2sorts.emplace(theory, std::unordered_set<TSort, THashSort>());
    }
    d_theory2sorts[theory].emplace(sort);
  }

  TTerm pick_term()
  {
    TheoryId theory;
    theory = pick_theory_with_terms();
    return pick_term(theory);
  }

  TTerm pick_term(TheoryId theory)
  {
    assert(d_terms.find(theory) != d_terms.end());
    if (theory == THEORY_ALL)
    {
      theory = pick_theory_with_terms();
    }
    TSort sort;
    sort = pick_sort_with_terms(theory);
    assert(get_theory(sort) == theory);
    TTerm res = pick_term(sort);
    assert(get_sort(res) == sort);
    assert(get_theory(get_sort(res)) == theory);
    return res;
  }

  TTerm pick_term(TTerm term)
  {
    TSort sort = get_sort(term);
    return pick_term(sort);
  }

  TTerm pick_term(TSort sort)
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

  bool has_term()
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

  bool has_term(TheoryId theory)
  {
    if (theory == THEORY_ALL) return has_term();

    if (d_terms.find(theory) == d_terms.end()) return false;

    for (const auto s : d_terms[theory])
    {
      if (!s.second.empty()) return true;
    }
    return false;
  }

  bool has_term(TSort sort) { return !d_terms[get_theory(sort)][sort].empty(); }

  TSort pick_sort()
  {
    TheoryId theory = pick_theory();
    pick_sort(theory);
  }

  TSort pick_sort(TheoryId theory)
  {
    assert(d_theory2sorts.find(theory) != d_theory2sorts.end());
    assert(!d_theory2sorts[theory].empty());

    SortSet& set = d_theory2sorts[theory];
    auto it      = set.begin();
    std::advance(it, d_rng.pick_uint32() % set.size());
    return *it;
  }

  TSort pick_sort_with_terms()
  {
    TheoryId theory = pick_theory_with_terms();
    pick_sort_with_terms(theory);
  }

  TSort pick_sort_with_terms(TheoryId theory)
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

  bool has_sort() { return !d_sorts2theory.empty(); }

  bool has_sort(TheoryId theory)
  {
    if (d_theory2sorts.find(theory) == d_theory2sorts.end()) return false;
    return !d_theory2sorts[theory].empty();
  }

  TheoryId pick_theory()
  {
    assert(d_theory2sorts.size());
    auto it = d_theory2sorts.begin();
    std::advance(it, d_rng.pick_uint32() % d_theory2sorts.size());
    return it->first;
  }

  TheoryId pick_theory_with_terms()
  {
    assert(d_terms.size());
    auto it = d_terms.begin();
    std::advance(it, d_rng.pick_uint32() % d_terms.size());
    assert(!it->second.empty());
    return it->first;
  }

  TheoryId get_theory(TSort sort)
  {
    assert(d_sorts2theory.find(sort) != d_sorts2theory.end());
    return d_sorts2theory[sort];
  }

  virtual TSort get_sort(TTerm term) = 0;

  Stats d_stats;

 protected:
  virtual void configure() = 0;

  template <class T>
  T* new_action()
  {
    static_assert(std::is_base_of<Action, T>::value,
                  "expected class (derived from) Action");
    T* action             = new T(this);
    const std::string& id = action->get_id();
    if (d_actions.find(id) == d_actions.end())
    {
      d_actions[id].reset(action);
    }
    else
    {
      delete action;
    }
    return static_cast<T*>(d_actions[id].get());
  }

  /* Solver specific implementations. */
  virtual TTerm copy_term(TTerm term) { return term; }
  virtual TSort copy_sort(TSort sort) { return sort; }

  FSM d_fsm;
  TSolver d_solver;
  RNGenerator& d_rng;

  /* Map theory -> sorts. */
  std::unordered_map<TheoryId, SortSet> d_theory2sorts;
  /* Map sort -> theory. */
  std::unordered_map<TSort, TheoryId, THashSort> d_sorts2theory;
  /* Map theory -> (sort -> terms). */
  std::unordered_map<TheoryId, SortMap> d_terms;

 private:
  std::unordered_map<std::string, std::unique_ptr<Action>> d_actions;
};

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt
#endif
