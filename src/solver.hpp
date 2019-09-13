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

/* -------------------------------------------------------------------------- */

#define SMTMBT_MK_TERM_N_ARGS -1
#define SMTMBT_MK_TERM_N_ARGS_MIN 2
#define SMTMBT_MK_TERM_N_ARGS_MAX 11

/* -------------------------------------------------------------------------- */

namespace smtmbt {

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

class AbsSort
{
 public:
  virtual ~AbsSort(){};
  virtual size_t hash() const                                      = 0;
  virtual bool equals(const std::shared_ptr<AbsSort>& other) const = 0;

  virtual bool is_bv() const           = 0;
  virtual uint32_t get_bv_size() const = 0;

  void set_kind(SortKind sort_kind);
  SortKind get_kind();

 protected:
  SortKind d_kind = SORT_ANY;
};

using Sort = std::shared_ptr<AbsSort>;

bool operator==(const Sort& a, const Sort& b);

struct HashSort
{
  std::size_t operator()(const Sort s) const;
};

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

class AbsTerm
{
 public:
  AbsTerm(){};
  virtual ~AbsTerm(){};
  virtual size_t hash() const                                      = 0;
  virtual bool equals(const std::shared_ptr<AbsTerm>& other) const = 0;
};

using Term = std::shared_ptr<AbsTerm>;

bool operator==(const Term& a, const Term& b);

struct HashTerm
{
  size_t operator()(const Term t) const;
};

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

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

  virtual Term mk_term(const OpKind& kind,
                       std::vector<Term>& args,
                       std::vector<uint32_t>& params) const = 0;

  virtual Sort get_sort(Term term) const = 0;

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

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt

#endif
