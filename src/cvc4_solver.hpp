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
  Cvc5Term(::cvc5::api::Solver* cvc5, ::cvc5::api::Term term)
      : d_solver(cvc5), d_term(term)
  {
  }

  ~Cvc5Term() override {}
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
  static const ActionKind ACTION_CHECK_ENTAILED;
  static const ActionKind ACTION_SIMPLIFY;
  /** Solver-specific operators. */
  // BV
  static const OpKind OP_BV_REDAND;
  static const OpKind OP_BV_REDOR;
  //  Strings
  static const OpKind OP_STRING_UPDATE;
  static const OpKind OP_STRING_TOLOWER;
  static const OpKind OP_STRING_TOUPPER;
  static const OpKind OP_STRING_REV;
  /** Solver-specific special values. */
  static const SpecialValueKind SPECIAL_VALUE_PI;

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
  void configure_smgr(SolverManager* smgr) const override;

  bool check_unsat_assumption(const Term& t) const override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;

  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;

  std::vector<::cvc5::api::Term> terms_to_cvc5_terms(
      std::vector<Term>& terms) const;

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

  void set_opt(const std::string& opt, const std::string& value) override;

  //
  // get_model()
  // get_proof()
  // get_unsat_core()
  //
  //
 private:
  void init_op_kinds();
  ::cvc5::api::Sort& get_cvc5_sort(Sort sort) const;
  std::vector<Term> cvc5_terms_to_terms(
      std::vector<::cvc5::api::Term>& terms) const;

  ::cvc5::api::Solver* d_solver;
  std::unordered_map<std::string, ::cvc5::api::Kind> d_op_kinds;
};

}  // namespace cvc5
}  // namespace murxla

#endif

#endif

