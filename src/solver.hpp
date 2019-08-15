#ifndef __SMTMBT__SOLVER_H
#define __SMTMBT__SOLVER_H

#include <cstddef>
#include <string>
#include <unordered_map>
#include <vector>
#include <cassert>

#include "op.hpp"
#include "sort.hpp"
#include "util.hpp"

namespace smtmbt {

class AbsTerm
{
 public:
  AbsTerm(){};
  virtual ~AbsTerm(){};
  virtual std::size_t hash() const = 0;
  virtual AbsTerm* copy() const = 0;
};

using Term = AbsTerm*;

struct HashTerm
{
  std::size_t operator()(const Term t) const { return t->hash(); }
};

class AbsSort
{
 public:
  AbsSort(){};
  virtual ~AbsSort(){};
  virtual std::size_t hash() const = 0;
  virtual AbsSort* copy() const = 0;
};

using Sort = AbsSort*;

struct HashSort
{
  std::size_t operator()(const Sort s) const { return s->hash(); }
};

class Solver
{
 public:

  enum Result
  {
    UNKNOWN,
    SAT,
    UNSAT,
  };

  Solver(RNGenerator& rng);
  Solver() = delete;
  ~Solver() = default;

  virtual void new_solver() = 0;
  virtual void delete_solver() = 0;
  virtual bool is_initialized() const = 0;

  virtual void set_opt(const std::string& opt, bool value) const = 0;

  virtual Term mk_var(Sort sort, const std::string name) const   = 0;
  virtual Term mk_const(Sort sort, const std::string name) const = 0;
  virtual Term mk_fun(Sort sort, const std::string name) const   = 0;

  virtual Term mk_value(Sort sort, uint32_t value) const = 0;
  // TODO: more

  virtual Sort mk_sort(const std::string name, uint32_t arity) const = 0;
  virtual Sort mk_sort(SortKind kind) const                          = 0;
  virtual Sort mk_sort(SortKind kind, uint32_t size) const           = 0;
  virtual Sort mk_sort(SortKind kind,
                       std::vector<Sort>& sorts,
                       Sort sort) const                              = 0;

  virtual Sort get_sort(Term term) const = 0;

  virtual Op mk_op(OpKind kind) const                                 = 0;
  virtual Op mk_op(OpKind kind, std::vector<uint32_t>& indices) const = 0;

  virtual Term apply(Op op, std::vector<Term>& children) const     = 0;
  virtual Term apply(Term term, std::vector<Term>& children) const = 0;

  virtual void assert_formula(const Term& t) const = 0;

  virtual Result check_sat() const = 0;

  OpKindMap& get_op_kinds();
  SortKindMap& get_sort_kinds();
  SortKindData& pick_sort_kind(SortKindVector& kinds);

  //
  // get_model()
  // get_value()
  // get_proof()
  // get_unsat_core()
  //
  //
 protected:
  RNGenerator& d_rng;

 private:
  // RNG
  template <typename TKind,
            typename TKindData,
            typename TKindMap,
            typename TKindVector>
  TKindData& pick_kind(TKindMap& map,
                       TKindVector* kinds1,
                       TKindVector* kinds2 = nullptr);

  OpKindMap d_op_kinds;
  SortKindMap d_sort_kinds;
};

template <typename TKind,
          typename TKindData,
          typename TKindMap,
          typename TKindVector>
TKindData&
Solver::pick_kind(TKindMap& map, TKindVector* kinds1, TKindVector* kinds2)
{
  assert(kinds1 || kinds2);
  size_t sz1 = kinds1 ? kinds1->size() : 0;
  size_t sz2 = kinds2 ? kinds2->size() : 0;
  uint32_t n = d_rng.pick_uint32() % (sz1 + sz2);
  typename TKindVector::iterator it;

  assert (sz1 || sz2);
  if (sz2 == 0 || n < sz1)
  {
    assert (kinds1);
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
  return map[kind];
}

}  // namespace smtmbt

#endif
