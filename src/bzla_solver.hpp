#ifdef MURXLA_USE_BITWUZLA

#ifndef __MURXLA__BITWUZLA_SOLVER_H
#define __MURXLA__BITWUZLA_SOLVER_H

#include "bitwuzla/bitwuzla.h"
#include "fsm.hpp"
#include "solver.hpp"
#include "theory.hpp"

namespace murxla {
namespace bzla {

/* -------------------------------------------------------------------------- */
/* BzlaSort                                                                  */
/* -------------------------------------------------------------------------- */

class BzlaSort : public AbsSort
{
  friend class BzlaSolver;

 public:
  BzlaSort(Bitwuzla* bzla, BitwuzlaSort* sort);
  ~BzlaSort() override;
  size_t hash() const override;
  bool equals(const Sort& other) const override;
  std::string to_string() const override;
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
  uint32_t get_fp_exp_size() const override;
  uint32_t get_fp_sig_size() const override;

 private:
  Bitwuzla* d_solver   = nullptr;
  BitwuzlaSort* d_sort = nullptr;
};

/* -------------------------------------------------------------------------- */
/* BzlaTerm                                                                  */
/* -------------------------------------------------------------------------- */

class BzlaTerm : public AbsTerm
{
  friend class BzlaSolver;

 public:
  BzlaTerm(BitwuzlaTerm* term);
  ~BzlaTerm() override;
  size_t hash() const override;
  std::string to_string() const override;
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
  BitwuzlaTerm* d_term = nullptr;
};

/* -------------------------------------------------------------------------- */
/* BzlaSolver                                                                */
/* -------------------------------------------------------------------------- */

class BzlaSolver : public Solver
{
 public:
  /** Solver-specific actions. */
  inline static const Action::Kind ACTION_GET_ARRAY_VALUE =
      "bzla-get-array-value";
  inline static const Action::Kind ACTION_GET_BV_VALUE = "bzla-get-bv-value";
  inline static const Action::Kind ACTION_GET_FP_VALUE = "bzla-get-fp-value";
  inline static const Action::Kind ACTION_GET_FUN_VALUE = "bzla-get-fun-value";
  inline static const Action::Kind ACTION_GET_RM_VALUE = "bzla-get-rm-value";
  inline static const Action::Kind ACTION_IS_UNSAT_ASSUMPTION =
      "bzla-is-unsat-assumption";
  inline static const Action::Kind ACTION_FIXATE_ASSUMPTIONS =
      "bzla-fixate-assumptions";
  inline static const Action::Kind ACTION_RESET_ASSUMPTIONS =
      "bzla-reset-assumptions";
  inline static const Action::Kind ACTION_SIMPLIFY = "bzla-simplify";
  inline static const Action::Kind ACTION_TERM_SET_SYMBOL =
      "bzla-term-set-symbol";
  /** Solver-specific operators. */
  inline static const Op::Kind OP_BV_DEC    = "bzla-OP_BV_DEC";
  inline static const Op::Kind OP_BV_INC    = "bzla-OP_BV_INC";
  inline static const Op::Kind OP_BV_REDAND = "bzla-OP_BV_REDAND";
  inline static const Op::Kind OP_BV_REDOR  = "bzla-OP_BV_REDOR";
  inline static const Op::Kind OP_BV_REDXOR = "bzla-OP_BV_REDXOR";
  inline static const Op::Kind OP_BV_ROL    = "bzla-OP_BV_ROL";
  inline static const Op::Kind OP_BV_ROR    = "bzla-OP_BV_ROR";
  inline static const Op::Kind OP_BV_SADDO  = "bzla-OP_BV_SADDO";
  inline static const Op::Kind OP_BV_SDIVO  = "bzla-OP_BV_SDIVO";
  inline static const Op::Kind OP_BV_SMULO  = "bzla-OP_BV_SMULO";
  inline static const Op::Kind OP_BV_SSUBO  = "bzla-OP_BV_SSUBO";
  inline static const Op::Kind OP_BV_UADDO  = "bzla-OP_BV_UADDO";
  inline static const Op::Kind OP_BV_UMULO  = "bzla-OP_BV_UMULO";
  inline static const Op::Kind OP_BV_USUBO  = "bzla-OP_BV_USUBO";
  inline static const Op::Kind OP_FP_TO_FP_FROM_REAL =
      "bzla-OP_FP_TO_FP_FROM_REAL";
  inline static const Op::Kind OP_IFF = "bzla-OP_IFF";
  /* Solver-specific states. */
  inline static const State::Kind STATE_FIX_RESET_ASSUMPTIONS =
      "bzla-fix-reset-assumptions";
  inline static const State::Kind STATE_UNKNOWN = "bzla-unknown";

  /** Constructor. */
  BzlaSolver(RNGenerator& rng) : Solver(rng), d_solver(nullptr) {}
  /** Destructor. */
  ~BzlaSolver() override;

  void new_solver() override;

  void delete_solver() override;

  Bitwuzla* get_solver();

  bool is_initialized() const override;

  TheoryIdVector get_supported_theories() const override;
  OpKindSet get_unsupported_op_kinds() const override;
  SortKindSet get_unsupported_var_sort_kinds() const override;
  SortKindSet get_unsupported_array_index_sort_kinds() const override;
  SortKindSet get_unsupported_array_element_sort_kinds() const override;
  SortKindSet get_unsupported_fun_domain_sort_kinds() const override;

  void configure_fsm(FSM* fsm) const override;
  void configure_opmgr(OpKindManager* opmgr) const override;

  void set_opt(const std::string& opt, const std::string& value) override;

  bool check_unsat_assumption(const Term& t) const override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;
  std::string get_option_name_unsat_cores() const override;

  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;
  bool option_unsat_cores_enabled() const override;

  BitwuzlaTerm* get_bzla_term(Term term) const;
  BitwuzlaSort* get_bzla_sort(Sort sort) const;

  Term mk_var(Sort sort, const std::string& name) override;

  Term mk_const(Sort sort, const std::string& name) override;

  Term mk_fun(Sort sort, const std::string& name) override
  {  // TODO:
    return nullptr;
  }

  Term mk_value(Sort sort, bool value) override;
  Term mk_value(Sort sort, std::string value) override;
  Term mk_value(Sort sort, std::string value, Base base) override;

  Term mk_special_value(Sort sort, const SpecialValueKind& value) override;

  Sort mk_sort(const std::string name, uint32_t arity) override
  {  // TODO:
    return nullptr;
  }

  Sort mk_sort(SortKind kind) override;
  Sort mk_sort(SortKind kind, uint32_t size) override;
  Sort mk_sort(SortKind kind, uint32_t esize, uint32_t ssize) override;
  Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) override;

  Term mk_term(const Op::Kind& kind,
               const std::vector<Term>& args,
               const std::vector<uint32_t>& params) override;

  Sort get_sort(Term term, SortKind sort_kind) const override;

  void assert_formula(const Term& t) override;

  Result check_sat() override;
  Result check_sat_assuming(std::vector<Term>& assumptions) override;

  std::vector<Term> get_unsat_assumptions() override;

  std::vector<Term> get_unsat_core() override;

  std::vector<Term> get_value(std::vector<Term>& terms) override;

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
  using BzlaTermFunBoolUnary       = std::function<bool(BitwuzlaTerm*)>;
  using BzlaTermFunBoolUnaryVector = std::vector<BzlaTermFunBoolUnary>;

  void init_op_kinds();

  std::vector<Term> bzla_terms_to_terms(
      const std::vector<BitwuzlaTerm*>& terms) const;
  std::vector<const BitwuzlaTerm*> terms_to_bzla_terms(
      const std::vector<Term>& terms) const;

  BzlaTermFunBoolUnary pick_fun_bool_unary(
      BzlaTermFunBoolUnaryVector& funs) const;
  BzlaTermFunBoolUnary pick_fun_is_bv_const() const;
  void check_is_bv_value(const SpecialValueKind& kind,
                         BitwuzlaTerm* node) const;

  BitwuzlaTerm* mk_value_bv_uint64(Sort sort, uint64_t value);

  Bitwuzla* d_solver;
  std::unordered_map<std::string, BitwuzlaOption> d_option_name_to_enum;
  std::unordered_map<std::string, BitwuzlaKind> d_op_kinds;

  uint64_t d_num_symbols;
};

}  // namespace bzla
}  // namespace murxla

#endif

#endif
