#ifndef __MURXLA__SHADOW_SOLVER_H
#define __MURXLA__SHADOW_SOLVER_H

#include "fsm.hpp"
#include "solver.hpp"
#include "theory.hpp"

namespace murxla {
namespace shadow {

class ShadowSort : public AbsSort
{
  friend class ShadowTerm;
  friend class ShadowSolver;

 public:
  ShadowSort(Sort sort, Sort sort_shadow);
  ~ShadowSort() override;
  size_t hash() const override;
  bool equals(const Sort& other) const override;
  std::string to_string() const override;
  bool is_array() const override;
  bool is_bag() const override;
  bool is_bool() const override;
  bool is_bv() const override;
  bool is_dt() const override;
  bool is_fp() const override;
  bool is_fun() const override;
  bool is_int() const override;
  bool is_real() const override;
  bool is_rm() const override;
  bool is_seq() const override;
  bool is_set() const override;
  bool is_string() const override;
  bool is_reglan() const override;
  uint32_t get_bv_size() const override;
  uint32_t get_fp_exp_size() const override;
  uint32_t get_fp_sig_size() const override;
  std::string get_dt_name() const override;
  uint32_t get_dt_num_cons() const override;
  std::vector<std::string> get_dt_cons_names() const override;
  uint32_t get_dt_cons_num_sels(const std::string& name) const override;
  std::vector<std::string> get_dt_cons_sel_names(
      const std::string& name) const override;
  Sort get_array_index_sort() const override;
  Sort get_array_element_sort() const override;
  Sort get_bag_element_sort() const override;
  uint32_t get_fun_arity() const override;
  Sort get_fun_codomain_sort() const override;
  std::vector<Sort> get_fun_domain_sorts() const override;
  Sort get_seq_element_sort() const override;
  Sort get_set_element_sort() const override;

  void set_kind(SortKind sort_kind) override;
  void set_sorts(const std::vector<Sort>& sorts) override;

  Sort get_sort() const { return d_sort; }
  Sort get_sort_shadow() const { return d_sort_shadow; }

 private:
  Sort d_sort;
  Sort d_sort_shadow;
};

class ShadowTerm : public AbsTerm
{
  friend class ShadowSolver;

 public:
  ShadowTerm(Term term, Term term_shadow);
  ~ShadowTerm() override;
  size_t hash() const override;
  bool equals(const Term& other) const override;
  std::string to_string() const override;
  const Op::Kind& get_kind() const override;
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
  bool is_bool_value() const override;
  bool is_bv_value() const override;
  bool is_fp_value() const override;
  bool is_int_value() const override;
  bool is_real_value() const override;
  bool is_reglan_value() const override;
  bool is_rm_value() const override;
  bool is_string_value() const override;
  bool is_special_value(const SpecialValueKind& kind) const override;
  bool is_const() const override;
  void set_sort(Sort sort) override;

  void set_special_value_kind(const SpecialValueKind& value_kind) override;
  void set_leaf_kind(LeafKind kind) override;

  Term get_term() const { return d_term; }
  Term get_term_shadow() const { return d_term_shadow; }

 private:
  Term d_term;
  Term d_term_shadow;
};

class ShadowSolver : public Solver
{
 public:
  ShadowSolver(SolverSeedGenerator& sng, Solver* solver, Solver* solver_shadow);
  ~ShadowSolver() override;

  void new_solver() override;
  void delete_solver() override;
  bool is_initialized() const override;
  const std::string get_name() const override;

  TheoryIdVector get_supported_theories() const override;
  TheoryIdVector get_unsupported_quant_theories() const override;
  OpKindSet get_unsupported_op_kinds() const override;
  OpKindSortKindMap get_unsupported_op_sort_kinds() const override;
  SortKindSet get_unsupported_var_sort_kinds() const override;
  SortKindSet get_unsupported_fun_domain_sort_kinds() const override;
  SortKindSet get_unsupported_fun_codomain_sort_kinds() const override;
  SortKindSet get_unsupported_array_index_sort_kinds() const override;
  SortKindSet get_unsupported_array_element_sort_kinds() const override;
  SortKindSet get_unsupported_bag_element_sort_kinds() const override;
  SortKindSet get_unsupported_seq_element_sort_kinds() const override;
  SortKindSet get_unsupported_set_element_sort_kinds() const override;

  Term mk_var(Sort sort, const std::string& name) override;
  Term mk_const(Sort sort, const std::string& name) override;
  Term mk_fun(Sort sort, const std::string& name) override;

  Term mk_value(Sort sort, bool value) override;
  Term mk_value(Sort sort, std::string value) override;
  Term mk_value(Sort sort, std::string num, std::string den) override;
  Term mk_value(Sort sort, std::string value, Base base) override;

  Term mk_special_value(Sort sort,
                        const AbsTerm::SpecialValueKind& value) override;

  Sort mk_sort(const std::string name, uint32_t arity) override;
  Sort mk_sort(SortKind kind) override;
  Sort mk_sort(SortKind kind, uint32_t size) override;
  Sort mk_sort(SortKind kind, uint32_t esize, uint32_t ssize) override;
  Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) override;
  Sort mk_sort(
      SortKind kind,
      const std::string& name,
      const std::unordered_map<std::string,
                               std::vector<std::pair<std::string, Sort>>>&
          ctors) override;

  Term mk_term(const Op::Kind& kind,
               const std::vector<Term>& args,
               const std::vector<uint32_t>& params) override;

  Sort get_sort(Term term, SortKind sort_kind) const override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;
  std::string get_option_name_unsat_cores() const override;

  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;
  bool option_unsat_cores_enabled() const override;

  bool is_unsat_assumption(const Term& t) const override;

  void assert_formula(const Term& t) override;

  Result check_sat() override;
  Result check_sat_assuming(std::vector<Term>& assumptions) override;

  std::vector<Term> get_unsat_assumptions() override;

  std::vector<Term> get_unsat_core() override;

  void push(uint32_t n_levels) override;
  void pop(uint32_t n_levels) override;

  void print_model() override;

  void reset() override;
  void reset_assertions() override;

  void set_opt(const std::string& opt, const std::string& value) override;

  std::vector<Term> get_value(std::vector<Term>& terms) override;

  void disable_unsupported_actions(FSM* fsm) const override;

  static void get_sorts_helper(const std::vector<Sort>& sorts,
                               std::vector<Sort>& sorts_orig,
                               std::vector<Sort>& sorts_shadow);

  static void get_terms_helper(const std::vector<Term>& terms,
                               std::vector<Term>& terms_orig,
                               std::vector<Term>& terms_shadow);

 protected:
  /** The solver under test. */
  std::unique_ptr<Solver> d_solver;
  /** The solver used for checking. */
  std::unique_ptr<Solver> d_solver_shadow;
  /** Flag that indicates whether d_solver and d_solver_shadow are instances of
   * the same solver. */
  bool d_same_solver;
};

}  // namespace shadow
}  // namespace murxla
#endif
