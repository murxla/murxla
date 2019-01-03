#ifndef __SMTMBT__SOLVER_MANAGER_H
#define __SMTMBT__SOLVER_MANAGER_H

#include <memory>
#include <unordered_map>

namespace smtmbt {

template <typename TSolver,
          typename TTerm,
          typename TSort,
          typename THashTerm,
          typename THashSort>
class SolverManager
{
 public:
  using TermMap = std::unordered_map<TTerm, size_t, THashTerm>;

  SolverManager() : d_solver(nullptr), d_terms(){};
  // TODO: copy/assignment constructors?
  ~SolverManager() = default;

  void set_solver(TSolver s) { d_solver = s; }

  TSolver get_solver() { return d_solver; }

  void add_term(TTerm term)
  {
    TSort sort = get_sort(term);
    add_sort(sort);
    if (d_terms[sort].find(term) == d_terms[sort].end())
    {
      d_terms[sort].emplace(copy_term(term), 0);
    }
  }

  TTerm pick_term(/* TODO: TheoryId */) {}

  void add_sort(TSort sort)
  {
    if (d_terms.find(sort) == d_terms.end())
    {
      d_terms.emplace(copy_sort(sort), TermMap());
    }
  }

  TSort pick_sort(/* TODO: TheoryId */) {}

 protected:
  /* Solver specific implementations. */
  virtual TTerm copy_term(TTerm term) { return term; }
  virtual TSort copy_sort(TSort sort) { return sort; }
  virtual TSort get_sort(TTerm term) = 0;

  std::unordered_map<TSort, TermMap, THashSort> d_terms;
  TSolver d_solver;
};

}  // namespace smtmbt
#endif
