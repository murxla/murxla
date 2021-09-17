#ifdef MURXLA_USE_CVC5

#ifndef __MURXLA__CVC5_SOLVER_H
#define __MURXLA__CVC5_SOLVER_H

#include "cvc5/cvc5.h"
#include "fsm.hpp"
#include "solver.hpp"

namespace murxla {
namespace cvc5 {

/* -------------------------------------------------------------------------- */
/* Cvc5Sort                                                                   */
/* -------------------------------------------------------------------------- */

class Cvc5Sort : public AbsSort
{
  friend class Cvc5Solver;

 public:
  Cvc5Sort(::cvc5::api::Solver* cvc5, ::cvc5::api::Sort sort)
      : d_solver(cvc5), d_sort(sort)
  {
  }

  ~Cvc5Sort() override {}
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
  Sort get_array_index_sort() const override;
  Sort get_array_element_sort() const override;
  uint32_t get_fun_arity() const override;
  Sort get_fun_codomain_sort() const override;
  std::vector<Sort> get_fun_domain_sorts() const override;

 private:
  std::vector<Sort> cvc5_sorts_to_sorts(
      const std::vector<::cvc5::api::Sort>& sorts) const;
  ::cvc5::api::Solver* d_solver;
  ::cvc5::api::Sort d_sort;
};

/* -------------------------------------------------------------------------- */
/* Cvc5Term                                                                   */
/* -------------------------------------------------------------------------- */

class Cvc5Term : public AbsTerm
{
  friend class Cvc5Solver;

 public:
  /** Map operator kinds to Bitwuzla operator kinds. */
  static std::unordered_map<Op::Kind, ::cvc5::api::Kind> s_kinds_to_cvc5_kinds;
  /** Map Bitwuzla operator kinds to operator kinds. */
  static std::unordered_map<::cvc5::api::Kind, Op::Kind> s_cvc5_kinds_to_kinds;

  /** Solver-specific operators. */
  // BV
  inline static const Op::Kind OP_BV_REDAND = "cvc5-OP_BV_REDAND";
  inline static const Op::Kind OP_BV_REDOR  = "cvc5-OP_BV_REDOR";
  //  Strings
  inline static const Op::Kind OP_STRING_UPDATE  = "cvc5-OP_STRING_UPDATE";
  inline static const Op::Kind OP_STRING_TOLOWER = "cvc5-OP_STRING_TOLOWER";
  inline static const Op::Kind OP_STRING_TOUPPER = "cvc5-OP_STRING_TOUPPER";
  inline static const Op::Kind OP_STRING_REV     = "cvc5-OP_STRING_REV";

  Cvc5Term(::cvc5::api::Solver* cvc5, ::cvc5::api::Term term)
      : d_solver(cvc5), d_term(term)
  {
  }

  ~Cvc5Term() override {}
  size_t hash() const override;
  bool equals(const Term& other) const override;
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
  const Op::Kind& get_kind() const override;
  std::vector<Term> get_children() const override;

 private:
  ::cvc5::api::Solver* d_solver = nullptr;
  ::cvc5::api::Term d_term;
};

/* -------------------------------------------------------------------------- */
/* Cvc5Solver                                                                 */
/* -------------------------------------------------------------------------- */

class Cvc5Solver : public Solver
{
 public:
  /** Solver-specific actions. */
  inline static const Action::Kind ACTION_CHECK_ENTAILED =
      "cvc5-check-entailed";
  inline static const Action::Kind ACTION_SIMPLIFY = "cvc5-simplify";

  /** Solver-specific special values. */
  inline static const SpecialValueKind SPECIAL_VALUE_PI = "cvc5-pi";

  /** Constructor. */
  Cvc5Solver(RNGenerator& rng) : Solver(rng), d_solver(nullptr) {}
  /** Destructor. */
  ~Cvc5Solver() override;

  OpKindSet get_unsupported_op_kinds() const override;
  SortKindSet get_unsupported_array_index_sort_kinds() const override;
  SortKindSet get_unsupported_array_element_sort_kinds() const override;
  SortKindSet get_unsupported_fun_domain_sort_kinds() const override;

  void new_solver() override;

  void delete_solver() override;

  ::cvc5::api::Solver* get_solver();
  ::cvc5::api::Term& get_cvc5_term(Term term) const;

  bool is_initialized() const override;

  void configure_fsm(FSM* fsm) const override;
  void configure_opmgr(OpKindManager* opmgr) const override;

  bool is_unsat_assumption(const Term& t) const override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;
  std::string get_option_name_unsat_cores() const override;

  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;
  bool option_unsat_cores_enabled() const override;

  std::vector<::cvc5::api::Term> terms_to_cvc5_terms(
      const std::vector<Term>& terms) const;

  Term mk_var(Sort sort, const std::string& name) override;

  Term mk_fun(Sort sort, const std::string& name) override
  {  // TODO:
    return nullptr;
  }

  Term mk_value(Sort sort, bool value) override;
  Term mk_value(Sort sort, std::string value) override;
  Term mk_value(Sort sort, std::string num, std::string den) override;
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

  Term mk_const(Sort sort, const std::string& name) override;
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

  void set_opt(const std::string& opt, const std::string& value) override;

  //
  // get_model()
  // get_proof()
  //
  //
 private:
  ::cvc5::api::Sort& get_cvc5_sort(Sort sort) const;
  std::vector<Term> cvc5_terms_to_terms(
      const std::vector<::cvc5::api::Term>& terms) const;

  ::cvc5::api::Solver* d_solver;
};

}  // namespace cvc5
}  // namespace murxla

#endif

#endif

