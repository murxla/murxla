#ifndef __SMTMBT__SOLVER_H
#define __SMTMBT__SOLVER_H

#include <cassert>
#include <cstddef>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

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
};

using Sort = std::shared_ptr<AbsSort>;

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

  virtual TheoryIdVector get_supported_theories() const;

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

  //
  // get_model()
  // get_value()
  // get_proof()
  // get_unsat_core()
  //
  //
 protected:
  RNGenerator& d_rng;
};

}  // namespace smtmbt

#endif
