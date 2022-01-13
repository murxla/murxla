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
  /** Get wrapped Boolector sort from Murxla Sort. */
  static BoolectorSort get_btor_sort(Sort sort);

  BtorSort(Btor* btor,
           BoolectorSort sort,
           const std::vector<BoolectorSort>& domain = {});
  ~BtorSort() override;
  size_t hash() const override;
  bool equals(const Sort& other) const override;
  std::string to_string() const override;
  bool is_array() const override;
  bool is_bool() const override;
  bool is_bv() const override;
  bool is_fun() const override;
  uint32_t get_bv_size() const override;
  Sort get_array_index_sort() const override;
  Sort get_array_element_sort() const override;
  uint32_t get_fun_arity() const override;
  Sort get_fun_codomain_sort() const override;

 private:
  /** Return a string representation of a bit-vector sort. */
  std::string bv_sort_to_string(BoolectorSort sort) const;
  /**
   * Return the current count of temp nodes and increase the counter.
   * This is only used for generating unique symbols for temp nodes.
   */
  uint64_t get_next_tmp_id() { return d_tmp_cnt++; }

  /** The associated Boolector instance. */
  Btor* d_solver = nullptr;
  /** The wrapped Boolector sort. */
  BoolectorSort d_sort;
  /**
   * We have to cache the domain sorts for array and function sorts in order to
   * be able to print them in to_string(). Boolector does not provide functions
   * to retrieve the domain sorts from array and function sorts.
   */
  std::vector<BoolectorSort> d_domain;
  /** Counter for generating unique symbols for temp nodes. */
  uint64_t d_tmp_cnt = 0;
};

/* -------------------------------------------------------------------------- */
/* BtorTerm                                                                   */
/* -------------------------------------------------------------------------- */

class BtorTerm : public AbsTerm
{
  friend class BtorSolver;

 public:
  /** Get wrapped Boolector term from Murxla term. */
  static BoolectorNode* get_btor_term(Term term);

  BtorTerm(Btor* btor, BoolectorNode* term);
  ~BtorTerm() override;
  size_t hash() const override;
  bool equals(const Term& other) const override;
  std::string to_string() const override;
  bool is_array() const override;
  bool is_bool_value() const override;
  bool is_bv_value() const override;
  bool is_special_value(const SpecialValueKind& kind) const override;
  bool is_const() const override;
  bool is_var() const override;
  uint32_t get_bv_size() const override;
  Sort get_array_index_sort() const override;
  Sort get_array_element_sort() const override;
  uint32_t get_fun_arity() const override;
  Sort get_fun_codomain_sort() const override;

 private:
  /** The associated Boolector instance. */
  Btor* d_solver        = nullptr;
  /** The wrapped Boolector term. */
  BoolectorNode* d_term = nullptr;
};

/* -------------------------------------------------------------------------- */
/* BtorSolver                                                                 */
/* -------------------------------------------------------------------------- */

class BtorSolver : public Solver
{
 public:
  /** Solver-specific actions. */
  inline static const Action::Kind ACTION_OPT_ITERATOR  = "btor-opt-iterator";
  inline static const Action::Kind ACTION_ARRAY_ASSIGNMENT =
      "btor-array-assignment";
  inline static const Action::Kind ACTION_BV_ASSIGNMENT = "btor-bv-assignment";
  inline static const Action::Kind ACTION_CLONE         = "btor-clone";
  inline static const Action::Kind ACTION_FAILED        = "btor-failed";
  inline static const Action::Kind ACTION_FIXATE_ASSUMPTIONS =
      "btor-fixate-assumptions";
  inline static const Action::Kind ACTION_RESET_ASSUMPTIONS =
      "btor-reset-assumptions";
  inline static const Action::Kind ACTION_RELEASE_ALL = "btor-release-all";
  inline static const Action::Kind ACTION_SIMPLIFY    = "btor-simplify";
  inline static const Action::Kind ACTION_SET_SAT_SOLVER =
      "btor-set-sat-solver";
  inline static const Action::Kind ACTION_SET_SYMBOL = "btor-set-symbol";

  /** Solver-specific operators. */
  inline static const Op::Kind OP_DEC    = "btor-OP_DEC";
  inline static const Op::Kind OP_INC    = "btor-OP_INC";
  inline static const Op::Kind OP_REDAND = "btor-OP_REDAND";
  inline static const Op::Kind OP_REDOR  = "btor-OP_REDOR";
  inline static const Op::Kind OP_REDXOR = "btor-OP_REDXOR";
  inline static const Op::Kind OP_UADDO  = "btor-OP_UADDO";
  inline static const Op::Kind OP_UMULO  = "btor-OP_UMULO";
  inline static const Op::Kind OP_USUBO  = "btor-OP_USUBO";
  inline static const Op::Kind OP_SADDO  = "btor-OP_SADDO";
  inline static const Op::Kind OP_SDIVO  = "btor-OP_SDIVO";
  inline static const Op::Kind OP_SMULO  = "btor-OP_SMULO";
  inline static const Op::Kind OP_SSUBO  = "btor-OP_SSUBO";
  /* Solver-specific states. */
  inline static const State::Kind STATE_FIX_RESET_ASSUMPTIONS =
      "btor-fix-reset-assumptions";
  inline static const State::Kind STATE_UNKNOWN = "btor-unknown";

  /** Constructor. */
  BtorSolver(SolverSeedGenerator& sng) : Solver(sng), d_solver(nullptr) {}
  /** Destructor. */
  ~BtorSolver() override;

  void new_solver() override;

  void delete_solver() override;

  Btor* get_solver();

  bool is_initialized() const override;

  const std::string get_name() const override;

  TheoryIdVector get_supported_theories() const override;
  TheoryIdVector get_unsupported_quant_theories() const override;
  SortKindSet get_unsupported_sort_kinds() const override;
  SortKindSet get_unsupported_var_sort_kinds() const override;
  SortKindSet get_unsupported_array_index_sort_kinds() const override;
  SortKindSet get_unsupported_array_element_sort_kinds() const override;
  SortKindSet get_unsupported_fun_domain_sort_kinds() const override;
  SortKindSet get_unsupported_fun_codomain_sort_kinds() const override;

  void configure_fsm(FSM* fsm) const override;
  void disable_unsupported_actions(FSM* fsm) const override;
  void configure_opmgr(OpKindManager* opmgr) const override;
  void configure_options(SolverManager* smgr) const override;

  void set_opt(const std::string& opt, const std::string& value) override;

  std::vector<std::string> get_supported_sat_solvers();

  bool is_unsat_assumption(const Term& t) const override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;
  std::string get_option_name_unsat_cores() const override;

  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;
  bool option_unsat_cores_enabled() const override;

  Term mk_var(Sort sort, const std::string& name) override;

  Term mk_const(Sort sort, const std::string& name) override;

  Term mk_fun(Sort sort, const std::string& name) override
  {  // TODO:
    return nullptr;
  }

  Term mk_value(Sort sort, bool value) override;
  Term mk_value(Sort sort, const std::string& value, Base base) override;

  Term mk_special_value(Sort sort,
                        const AbsTerm::SpecialValueKind& value) override;

  Sort mk_sort(SortKind kind) override;
  Sort mk_sort(SortKind kind, uint32_t size) override;

  Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) override;

  Term mk_term(const Op::Kind& kind,
               const std::vector<Term>& args,
               const std::vector<uint32_t>& indices) override;

  Sort get_sort(Term term, SortKind sort_kind) const override;

  void assert_formula(const Term& t) override;

  Result check_sat() override;
  Result check_sat_assuming(const std::vector<Term>& assumptions) override;

  std::vector<Term> get_unsat_assumptions() override;

  std::vector<Term> get_value(const std::vector<Term>& terms) override;

  void push(uint32_t n_levels) override;
  void pop(uint32_t n_levels) override;

  void print_model() override;

  void reset() override;
  void reset_assertions() override;

  //
  // get_model()
  // get_proof()
  //
  //
 private:
  using BtorFunBoolUnary       = std::function<bool(Btor*, BoolectorNode*)>;
  using BtorFunBoolUnaryVector = std::vector<BtorFunBoolUnary>;

  std::vector<Term> btor_terms_to_terms(
      const std::vector<BoolectorNode*>& terms) const;
  std::vector<BoolectorNode*> terms_to_btor_terms(
      const std::vector<Term>& terms) const;

  BoolectorNode* mk_value_bv_uint32(Sort sort, uint32_t value);
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
