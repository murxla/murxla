#ifndef __MURXLA__CROSS_CHECK_SOLVER_H
#define __MURXLA__CROSS_CHECK_SOLVER_H

#include "fsm.hpp"
#include "solver.hpp"
#include "theory.hpp"

namespace murxla {
namespace cross_check {

class CrossCheckSort : public AbsSort
{
  friend class CrossCheckTerm;

 public:
  CrossCheckSort(Sort sort_test, Sort sort_ref);
  ~CrossCheckSort() override;
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
  void set_kind(SortKind sort_kind) override;
  void set_sorts(const std::vector<Sort>& sorts) override;

  Sort get_sort_test() const;
  Sort get_sort_ref() const;

 private:
  Sort d_sort_test;
  Sort d_sort_ref;
};

class CrossCheckTerm : public AbsTerm
{
  friend class CrossCheckSolver;

 public:
  CrossCheckTerm(Term term_test, Term term_ref);
  ~CrossCheckTerm() override;
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
  void set_sort(Sort sort) override;

  Term get_term_test() const;
  Term get_term_ref() const;

 private:
  Term d_term_test;
  Term d_term_ref;
};

class CrossCheckSolver : public Solver
{
 public:
  CrossCheckSolver(RNGenerator& rng,
                   Solver* test_solver,
                   Solver* reference_solver);
  ~CrossCheckSolver() override;

  void new_solver() override;
  void delete_solver() override;
  bool is_initialized() const override;

  TheoryIdVector get_supported_theories() const override;
  TheoryIdVector get_unsupported_quant_theories() const override;
  OpKindSet get_unsupported_op_kinds() const override;
  SortKindSet get_unsupported_var_sort_kinds() const override;
  SortKindSet get_unsupported_fun_domain_sort_kinds() const override;
  SortKindSet get_unsupported_array_index_sort_kinds() const override;
  SortKindSet get_unsupported_array_element_sort_kinds() const override;

  Term mk_var(Sort sort, const std::string& name) override;
  Term mk_const(Sort sort, const std::string& name) override;
  Term mk_fun(Sort sort, const std::string& name) override;

  Term mk_value(Sort sort, bool value) override;
  Term mk_value(Sort sort, std::string value) override;
  Term mk_value(Sort sort, std::string num, std::string den) override;
  Term mk_value(Sort sort, std::string value, Base base) override;

  Term mk_special_value(Sort sort, const SpecialValueKind& value) override;

  Sort mk_sort(const std::string name, uint32_t arity) override;
  Sort mk_sort(SortKind kind) override;
  Sort mk_sort(SortKind kind, uint32_t size) override;
  Sort mk_sort(SortKind kind, uint32_t esize, uint32_t ssize) override;
  Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) override;

  Term mk_term(const Op::Kind& kind,
               std::vector<Term>& args,
               std::vector<uint32_t>& params) override;

  Sort get_sort(Term term, SortKind sort_kind) const override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;
  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;

  bool check_unsat_assumption(const Term& t) const override;

  void assert_formula(const Term& t) override;

  Result check_sat() override;
  Result check_sat_assuming(std::vector<Term>& assumptions) override;

  std::vector<Term> get_unsat_assumptions() override;

  void push(uint32_t n_levels) override;
  void pop(uint32_t n_levels) override;

  void print_model() override;

  void reset_assertions() override;

  void set_opt(const std::string& opt, const std::string& value) override;

  std::vector<Term> get_value(std::vector<Term>& terms) override;

  void configure_fsm(FSM* fsm) const override;

 private:
  /** The solver under test. */
  std::unique_ptr<Solver> d_test_solver;
  /** The reference solver. */
  std::unique_ptr<Solver> d_reference_solver;

  void get_terms_test(const std::vector<Term>& terms,
                      std::vector<Term>& terms_test) const;
  void get_terms_ref(const std::vector<Term>& terms,
                     std::vector<Term>& terms_ref) const;

  Sort get_sort_test(Sort s) const;
  Sort get_sort_ref(Sort s) const;
};

}  // namespace cross_check
}  // namespace murxla
#endif
