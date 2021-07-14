#ifdef MURXLA_USE_BOOLECTOR

#ifndef __MURXLA__BTOR_SOLVER_H
#define __MURXLA__BTOR_SOLVER_H

#include "boolector/boolector.h"
#include "fsm.hpp"
#include "solver.hpp"
#include "theory.hpp"

namespace murxla {
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
  bool is_array() const override;
  bool is_bool() const override;
  bool is_bv() const override;
  bool is_fp() const override;
  bool is_fun() const override;
  bool is_int() const override;
  bool is_real() const override;
  bool is_rm() const override;
  bool is_string() const override;
  bool is_reglan() const override;
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
  bool is_array() const override;
  bool is_bool() const override;
  bool is_bv() const override;
  bool is_fp() const override;
  bool is_fun() const override;
  bool is_int() const override;
  bool is_real() const override;
  bool is_rm() const override;
  bool is_string() const override;
  bool is_reglan() const override;

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
  /** Solver-specific actions. */
  static const OpKind ACTION_OPT_ITERATOR;
  static const OpKind ACTION_BV_ASSIGNMENT;
  static const OpKind ACTION_CLONE;
  static const OpKind ACTION_FAILED;
  static const OpKind ACTION_FIXATE_ASSUMPTIONS;
  static const OpKind ACTION_RESET_ASSUMPTIONS;
  static const OpKind ACTION_RELEASE_ALL;
  static const OpKind ACTION_SIMPLIFY;
  static const OpKind ACTION_SET_SAT_SOLVER;
  static const OpKind ACTION_SET_SYMBOL;
  /** Solver-specific operators. */
  static const OpKind OP_DEC;
  static const OpKind OP_INC;
  static const OpKind OP_REDAND;
  static const OpKind OP_REDOR;
  static const OpKind OP_REDXOR;
  static const OpKind OP_UADDO;
  static const OpKind OP_UMULO;
  static const OpKind OP_USUBO;
  static const OpKind OP_SADDO;
  static const OpKind OP_SDIVO;
  static const OpKind OP_SMULO;
  static const OpKind OP_SSUBO;
  /* Solver-specific states. */
  static const OpKind STATE_FIX_RESET_ASSUMPTIONS;

  /** Constructor. */
  BtorSolver(RNGenerator& rng) : Solver(rng), d_solver(nullptr) {}
  /** Destructor. */
  ~BtorSolver() override;

  void new_solver() override;

  void delete_solver() override;

  Btor* get_solver();

  bool is_initialized() const override;

  TheoryIdVector get_supported_theories() const override;
  TheoryIdVector get_unsupported_quant_theories() const override;
  OpKindSet get_unsupported_op_kinds() const override;
  SortKindSet get_unsupported_var_sort_kinds() const override;
  SortKindSet get_unsupported_array_index_sort_kinds() const override;
  SortKindSet get_unsupported_array_element_sort_kinds() const override;
  SortKindSet get_unsupported_fun_domain_sort_kinds() const override;

  void configure_fsm(FSM* fsm) const override;
  void configure_opmgr(OpKindManager* opmgr) const override;

  void set_opt(const std::string& opt, const std::string& value) override;

  std::vector<std::string> get_supported_sat_solvers();

  bool check_unsat_assumption(const Term& t) const override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;

  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;

  BoolectorNode* get_btor_term(Term term) const;

  Term mk_var(Sort sort, const std::string& name) override;

  Term mk_const(Sort sort, const std::string& name) override;

  Term mk_fun(Sort sort, const std::string& name) override
  {  // TODO:
    return nullptr;
  }

  Term mk_value(Sort sort, bool value) override;
  Term mk_value(Sort sort, std::string value, Base base) override;

  Term mk_special_value(Sort sort, const SpecialValueKind& value) override;

  Sort mk_sort(const std::string name, uint32_t arity) override
  {  // TODO:
    return nullptr;
  }

  Sort mk_sort(SortKind kind) override;
  Sort mk_sort(SortKind kind, uint32_t size) override;

  Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) override;

  Term mk_term(const OpKind& kind,
               std::vector<Term>& args,
               std::vector<uint32_t>& params) override;

  Sort get_sort(Term term, SortKind sort_kind) const override;

  void assert_formula(const Term& t) override;

  Result check_sat() override;
  Result check_sat_assuming(std::vector<Term>& assumptions) override;

  std::vector<Term> get_unsat_assumptions() override;

  std::vector<Term> get_value(std::vector<Term>& terms) override;

  void push(uint32_t n_levels) override;
  void pop(uint32_t n_levels) override;

  void print_model() override;

  void reset_assertions() override;

  //
  // get_model()
  // get_proof()
  // get_unsat_core()
  //
  //
 private:
  using BtorFunBoolUnary       = std::function<bool(Btor*, BoolectorNode*)>;
  using BtorFunBoolUnaryVector = std::vector<BtorFunBoolUnary>;

  std::vector<Term> btor_terms_to_terms(
      std::vector<BoolectorNode*>& terms) const;
  std::vector<BoolectorNode*> terms_to_btor_terms(
      std::vector<Term>& terms) const;

  BtorFunBoolUnary pick_fun_bool_unary(BtorFunBoolUnaryVector& funs) const;
  BtorFunBoolUnary pick_fun_is_bv_const() const;
  void check_is_bv_const(const SpecialValueKind& kind,
                         BoolectorNode* node) const;

  BoolectorSort get_btor_sort(Sort sort) const;
  BoolectorNode* mk_value_bv_uint64 (Sort sort, uint64_t value);
  BoolectorNode* mk_term_left_assoc(
      std::vector<BoolectorNode*>& args,
      BoolectorNode* (*fun)(Btor*, BoolectorNode*, BoolectorNode*) ) const;
  BoolectorNode* mk_term_right_assoc(
      std::vector<BoolectorNode*>& args,
      BoolectorNode* (*fun)(Btor*, BoolectorNode*, BoolectorNode*) ) const;
  BoolectorNode* mk_term_pairwise(std::vector<BoolectorNode*>& args,
                                  BoolectorNode* (*fun)(Btor*,
                                                        BoolectorNode*,
                                                        BoolectorNode*) ) const;
  BoolectorNode* mk_term_chained(std::vector<BoolectorNode*>& args,
                                 BoolectorNode* (*fun)(Btor*,
                                                       BoolectorNode*,
                                                       BoolectorNode*) ) const;
  Btor* d_solver;
  std::unordered_map<std::string, BtorOption> d_option_name_to_enum;

  uint64_t d_num_symbols;
};

}  // namespace btor
}  // namespace murxla

#endif

#endif
