#ifdef SMTMBT_USE_BOOLECTOR

#ifndef __SMTMBT__BTOR_SOLVER_H
#define __SMTMBT__BTOR_SOLVER_H

#include "boolector/boolector.h"
#include "fsm.hpp"
#include "solver.hpp"
#include "theory.hpp"

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
  bool is_bool() const override;
  bool is_bv() const override;
  uint32_t get_bv_size() const override;

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
  Btor* d_solver        = nullptr;
  BoolectorNode* d_term = nullptr;
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

  Btor* get_solver();

  bool is_initialized() const override;

  TheoryIdVector get_supported_theories() const override;
  OpKindSet get_unsupported_op_kinds() const override;

  void configure_fsm(FSM* fsm) const override;

  void set_opt(const std::string& opt, const std::string& value) const override;

  std::vector<std::string> get_supported_sat_solvers();

  bool check_failed_assumption(const Term& t) const;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  bool option_incremental_enabled() const;
  bool option_model_gen_enabled() const;
  std::string get_option_value_enable_incremental() const override;
  std::string get_option_value_enable_model_gen() const override;

  BoolectorNode* get_btor_term(Term term) const;

  Term mk_var(Sort sort, const std::string name) const override
  {  // TODO:
    return nullptr;
  }

  Term mk_const(Sort sort, const std::string name) const override;

  Term mk_fun(Sort sort, const std::string name) const override
  {  // TODO:
    return nullptr;
  }

  Term mk_value(Sort sort, bool value) const override;
  Term mk_value(Sort sort, uint64_t value) const override;
  Term mk_value(Sort sort, std::string value, Base base) const override;

  Sort mk_sort(const std::string name, uint32_t arity) const override
  {  // TODO:
    return nullptr;
  }

  Sort mk_sort(SortKind kind) const override;
  Sort mk_sort(SortKind kind, uint32_t size) const override;

  Sort mk_sort(SortKind kind,
               std::vector<Sort>& sorts,
               Sort sort) const override
  {  // TODO:
    return nullptr;
  }

  Term mk_term(const OpKind& kind,
               std::vector<Term>& args,
               std::vector<uint32_t>& params) const override;

  Sort get_sort(Term term) const override;

  void assert_formula(const Term& t) const override;

  Result check_sat() const override;
  Result check_sat_assuming(std::vector<Term>& assumptions) const override;

  std::vector<Term> get_unsat_assumptions() const;

  void push(uint32_t n_levels) const override;
  void pop(uint32_t n_levels) const override;

  void print_model() const override;

  void reset_assertions() const override;

  //
  // get_model()
  // get_value()
  // get_proof()
  // get_unsat_core()
  //
  //
 private:
  using BtorFunBoolUnary       = std::function<bool(Btor*, BoolectorNode*)>;
  using BtorFunBoolUnaryVector = std::vector<BtorFunBoolUnary>;

  BtorFunBoolUnary pick_fun_bool_unary(BtorFunBoolUnaryVector& funs) const;
  BtorFunBoolUnary pick_fun_is_bv_const() const;
  void check_is_bv_const(SpecialValueBV kind, BoolectorNode* node) const;

  BoolectorSort get_btor_sort(Sort sort) const;
  BoolectorNode* mk_term_left_assoc(
      std::vector<Term>& args,
      BoolectorNode* (*fun)(Btor*, BoolectorNode*, BoolectorNode*) ) const;
  BoolectorNode* mk_term_pairwise(std::vector<Term>& args,
                                  BoolectorNode* (*fun)(Btor*,
                                                        BoolectorNode*,
                                                        BoolectorNode*) ) const;
  Btor* d_solver;
  std::unordered_map<std::string, BtorOption> d_option_name_to_enum;
};

}  // namespace btor
}  // namespace smtmbt

#endif

#endif
