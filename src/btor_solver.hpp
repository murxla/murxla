#ifdef SMTMBT_USE_BOOLECTOR

#ifndef __SMTMBT__BTOR_SOLVER_H
#define __SMTMBT__BTOR_SOLVER_H

#include "solver.hpp"
#include "theory.hpp"

#include "boolector/boolector.h"

extern "C" {
struct Btor;
}

namespace smtmbt {
namespace btor {

/* -------------------------------------------------------------------------- */
/* BtorSort                                                                   */
/* -------------------------------------------------------------------------- */

class BtorSort : public AbsSort
{
  friend class BtorSolver;

 public:
  BtorSort(Btor* btor, BoolectorSort sort);
  ~BtorSort() override;
  size_t hash() const override;
  bool equals(const Sort& other) const override;

 private:
  Btor* d_solver;
  BoolectorSort d_sort;
};

/* -------------------------------------------------------------------------- */
/* BtorTerm                                                                   */
/* -------------------------------------------------------------------------- */

class BtorTerm : public AbsTerm
{
  friend class BtorSolver;

 public:
  BtorTerm(Btor* btor, BoolectorNode* term);
  ~BtorTerm() override;
  size_t hash() const override;
  bool equals(const Term& other) const override;

 private:
  Btor* d_solver;
  BoolectorNode* d_term;
};

/* -------------------------------------------------------------------------- */
/* BtorSolver                                                                 */
/* -------------------------------------------------------------------------- */

class BtorSolver : public Solver
{
 public:
  BtorSolver(RNGenerator& rng) : Solver(rng), d_solver(nullptr) {}

  void new_solver() override;

  void delete_solver() override;

  bool is_initialized() const override;

  TheoryIdVector get_supported_theories() const override;

  void set_opt(const std::string& opt, bool value) const
  {  // TODO:
  }

  Term mk_var(Sort sort, const std::string name) const
  {  // TODO:
    return nullptr;
  }

  Term mk_const(Sort sort, const std::string name) const;

  Term mk_fun(Sort sort, const std::string name) const
  {  // TODO:
    return nullptr;
  }

  Term mk_value(Sort sort, uint32_t value) const
  {  // TODO:
    return nullptr;
  }
  // TODO: more

  Sort mk_sort(const std::string name, uint32_t arity) const
  {  // TODO:
    return nullptr;
  }

  Sort mk_sort(SortKind kind) const override;
  Sort mk_sort(SortKind kind, uint32_t size) const override;

  Sort mk_sort(SortKind kind, std::vector<Sort>& sorts, Sort sort) const
  {  // TODO:
    return nullptr;
  }

  Term mk_term(const OpKindData& kind,
               std::vector<Term>& arguments) const override;

  Sort get_sort(Term term) const;

  void assert_formula(const Term& t) const
  {  // TODO:
  }

  Result check_sat() const
  {  // TODO:
    return Result::UNKNOWN;
  }

  //
  // get_model()
  // get_value()
  // get_proof()
  // get_unsat_core()
  //
  //
 private:
  BoolectorSort get_sort(Sort sort) const;
  BoolectorNode* get_term(Term term) const;
  BoolectorNode* mk_term_left_assoc(
      std::vector<Term>& args,
      BoolectorNode* (*fun)(Btor*, BoolectorNode*, BoolectorNode*) ) const;
  BoolectorNode* mk_term_pairwise(std::vector<Term>& args,
                                  BoolectorNode* (*fun)(Btor*,
                                                        BoolectorNode*,
                                                        BoolectorNode*) ) const;
  Btor* d_solver;
};

}  // namespace btor
}  // namespace smtmbt

#endif

#endif
