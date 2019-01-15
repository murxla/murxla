#ifndef __SMTMBT__SOLVER_MANAGER_H
#define __SMTMBT__SOLVER_MANAGER_H

#include <cassert>
#include <memory>
#include <unordered_map>

#include "fsm.hpp"

namespace smtmbt {

enum TheoryId
{
  THEORY_BOOL,
  THEORY_BV,
};

/* -------------------------------------------------------------------------- */

class Action
{
 public:
  Action() = delete;
  Action(const std::string& id) : d_id(id) {}
  virtual ~Action() = default;
  virtual bool run() = 0;
  // virtual void untrace(const char* s) {}
  const std::string& get_id() const { return d_id; }

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

  /* Statistics. */
  struct Stats
  {
    uint32_t inputs = 0;  /* constants, variables */
    uint32_t terms  = 0;   /* all terms, including inputs */
  };

  SolverManager() : d_solver(nullptr) {}
  // TODO: copy/assignment constructors?
  ~SolverManager() = default;

  void set_solver(TSolver s) { d_solver = s; }

  TSolver get_solver() { return d_solver; }

  void run() { d_fsm.run(); }

  void add_input(TTerm term, TheoryId theory)
  {
    d_stats.inputs += 1;
    add_term (term, theory);
  }

  void add_term(TTerm term, TheoryId theory)
  {
    TSort sort = get_sort(term);
    add_sort(sort, theory);

    assert(d_terms.find(theory) != d_terms.end());

    SortMap& smap = d_terms[theory];
    assert(smap.find(sort) != smap.end());
    if (smap[sort].find(term) == smap[sort].end())
    {
      smap[sort].emplace(copy_term(term), 0);
    }
    else
    {
      smap[sort][term] += 1;
    }
  }

  void add_sort(TSort sort, TheoryId theory)
  {
    if (d_terms.find(theory) == d_terms.end())
    {
      d_terms.emplace(theory, SortMap());
    }

    SortMap& map = d_terms[theory];
    if (map.find(sort) == map.end())
    {
      map.emplace(copy_sort(sort), TermMap());
      d_sorts.emplace(sort, theory);
    }
  }

  TTerm pick_term()
  {
    TheoryId theory = pick_theory();
    return pick_term(theory);
  }

  TTerm pick_term(TheoryId theory)
  {
    assert(d_terms.find(theory) != d_terms.end());
    TSort sort = pick_sort(theory);
    return pick_term(sort);
  }

  TTerm pick_term(TTerm term)
  {
    TSort sort = get_sort(term);
    return pick_term(sort);
  }

  TTerm pick_term(TSort sort)
  {
    TheoryId theory = get_theory(sort);
    TermMap& map    = d_terms[theory][sort];
    assert(!map.empty());
    auto it = map.begin();
    if (map.size() > 1)
    {
      std::advance(it, d_rng.next_uint32() % map.size());
    }
    // TODO: increment ref counter
    return it->first;
  }

  TSort pick_sort()
  {
    TheoryId theory = pick_theory();
    pick_sort(theory);
  }

  TSort pick_sort(TheoryId theory)
  {
    SortMap& map = d_terms[theory];
    assert(!map.empty());

    auto it = map.begin();
    if (map.size() > 1)
    {
      std::advance(it, d_rng.next_uint32() % map.size());
    }
    return it->first;
  }

  TheoryId get_theory(TSort sort)
  {
    assert(d_sorts.find(sort) != d_sorts.end());
    return d_sorts[sort];
  }

  void set_rng(RNGenerator rng) { d_rng = rng; }

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
  virtual TSort get_sort(TTerm term) = 0;

  FSM d_fsm;
  TSolver d_solver;
  std::unordered_map<TSort, TheoryId, THashSort> d_sorts;
  std::unordered_map<TheoryId, SortMap> d_terms;

 private:
  RNGenerator d_rng;
  std::unordered_map<std::string, std::unique_ptr<Action>> d_actions;

  TheoryId pick_theory()
  {
    assert(d_terms.size());
    auto it = d_terms.begin();
    std::advance(it, d_rng.next_uint32() % d_terms.size());
    return it->first;
  }
};

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt
#endif
