#ifdef SMTMBT_USE_YICES

#ifndef __SMTMBT__YICES_SOLVER_H
#define __SMTMBT__YICES_SOLVER_H

#include <bitset>

#include "fsm.hpp"
#include "solver.hpp"
#include "theory.hpp"
#include "yices.h"

namespace smtmbt {
namespace yices {

/* -------------------------------------------------------------------------- */
/* YicesSort */
/* -------------------------------------------------------------------------- */

class YicesSort : public AbsSort
{
  friend class YicesSolver;

 public:
  YicesSort(type_t sort) : d_sort(sort) {}
  ~YicesSort() override {}
  size_t hash() const override;
  bool equals(const Sort& other) const override;
  bool is_array() const override;
  bool is_bool() const override;
  bool is_bv() const override;
  bool is_fp() const override;
  bool is_fun() const override;
  bool is_int() const override;
  bool is_real() const override;
  bool is_reglan() const override;
  bool is_rm() const override;
  bool is_string() const override;
  uint32_t get_bv_size() const override;

 private:
  type_t d_sort = 0;
};

/* -------------------------------------------------------------------------- */
/* YicesTerm */
/* -------------------------------------------------------------------------- */

class YicesTerm : public AbsTerm
{
  friend class YicesSolver;

 public:
  YicesTerm(term_t term) : d_term(term) {}
  ~YicesTerm() override {}
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
  term_t d_term = 0;
};

/* -------------------------------------------------------------------------- */
/* YicesSolver */
/* -------------------------------------------------------------------------- */

class YicesSolver : public Solver
{
 public:
  /* Solver-specific operators. */
  // BV
  static const OpKind OP_ASHIFT_RIGHT;
  static const OpKind OP_BITEXTRACT;
  static const OpKind OP_BVARRAY;
  static const OpKind OP_BVPOWER;
  static const OpKind OP_BVSQUARE;
  static const OpKind OP_REDAND;
  static const OpKind OP_REDOR;
  static const OpKind OP_SHIFT_LEFT0;
  static const OpKind OP_SHIFT_LEFT1;
  static const OpKind OP_SHIFT_RIGHT0;
  static const OpKind OP_SHIFT_RIGHT1;
  // Arithmetic
  static const OpKind OP_INT_CEIL;
  static const OpKind OP_INT_FLOOR;
  static const OpKind OP_INT_EQ0;
  static const OpKind OP_INT_GEQ0;
  static const OpKind OP_INT_GT0;
  static const OpKind OP_INT_LEQ0;
  static const OpKind OP_INT_LT0;
  static const OpKind OP_INT_NEQ0;
  static const OpKind OP_INT_POLY;
  static const OpKind OP_INT_POWER;
  static const OpKind OP_INT_SQUARE;
  static const OpKind OP_REAL_CEIL;
  static const OpKind OP_REAL_FLOOR;
  static const OpKind OP_REAL_EQ0;
  static const OpKind OP_REAL_GEQ0;
  static const OpKind OP_REAL_GT0;
  static const OpKind OP_REAL_LEQ0;
  static const OpKind OP_REAL_LT0;
  static const OpKind OP_REAL_NEQ0;
  static const OpKind OP_REAL_POLY;
  static const OpKind OP_REAL_RPOLY;
  static const OpKind OP_REAL_POWER;
  static const OpKind OP_REAL_SQUARE;

  YicesSolver(RNGenerator& rng) : Solver(rng) {}
  ~YicesSolver() override{};

  void new_solver() override;
  void delete_solver() override;
  bool is_initialized() const override;

  TheoryIdVector get_supported_theories() const override;

  void configure_fsm(FSM* fsm) const override;
  void configure_smgr(SolverManager* smgr) const override;
  void reset_sat() override;

  void set_opt(const std::string& opt, const std::string& value) override;

  bool check_failed_assumption(const Term& t) const override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;

  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;

  term_t get_yices_term(Term term) const;

  Term mk_var(Sort sort, const std::string& name) override;

  Term mk_const(Sort sort, const std::string& name) override;

  Term mk_fun(Sort sort, const std::string& name) override
  {  // TODO:
    return nullptr;
  }

  Term mk_value(Sort sort, bool value) override;
  Term mk_value(Sort sort, std::string value) override;
  Term mk_value(Sort sort, std::string num, std::string den) override;
  Term mk_value(Sort sort, std::string value, Base base) override;

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
  type_t get_yices_sort(Sort sort) const;
  bool is_valid_sort(type_t sort) const;
  bool is_valid_term(term_t term) const;

  std::vector<int32_t> bin_str_to_int_array(std::string s);

  term_t mk_value_bv_int_or_special(Sort sort, std::string value, Base base);

  term_t mk_term_left_assoc(std::vector<term_t>& args,
                            term_t (*fun)(term_t, term_t)) const;
  term_t mk_term_pairwise(std::vector<term_t>& args,
                          term_t (*fun)(term_t, term_t)) const;
  term_t mk_term_chained(std::vector<term_t>& args,
                         term_t (*fun)(term_t, term_t)) const;

  std::vector<type_t> sorts_to_yices_sorts(
      const std::vector<Sort>& sorts) const;

  std::vector<Term> yices_terms_to_terms(term_vector_t* terms) const;
  std::vector<Term> yices_terms_to_terms(std::vector<term_t>& terms) const;
  std::vector<term_t> terms_to_yices_terms(std::vector<Term>& terms) const;

  bool d_is_initialized  = false;
  bool d_incremental     = false;
  ctx_config_t* d_config = nullptr;
  context_t* d_context   = nullptr;
  model_t* d_model       = nullptr;
};

}  // namespace yices
}  // namespace smtmbt

#endif

#endif
