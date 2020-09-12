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

 private:
  term_t d_term = 0;
};

/* -------------------------------------------------------------------------- */
/* YicesSolver */
/* -------------------------------------------------------------------------- */

class YicesSolver : public Solver
{
 public:
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

  /* solver-specific operators */
  // BV
  const OpKind d_op_ashift_right = OP_EXT_OP_01;
  const OpKind d_op_bitextract   = OP_EXT_OP_02;
  const OpKind d_op_bvarray      = OP_EXT_OP_03;
  const OpKind d_op_bvpower      = OP_EXT_OP_04;
  const OpKind d_op_bvsquare     = OP_EXT_OP_05;
  const OpKind d_op_redand       = OP_EXT_OP_06;
  const OpKind d_op_redor        = OP_EXT_OP_07;
  const OpKind d_op_shift_left0  = OP_EXT_OP_08;
  const OpKind d_op_shift_left1  = OP_EXT_OP_09;
  const OpKind d_op_shift_right0 = OP_EXT_OP_10;
  const OpKind d_op_shift_right1 = OP_EXT_OP_11;
  // Arithmetic
  const OpKind d_op_int_ceil    = OP_EXT_OP_12;
  const OpKind d_op_int_floor   = OP_EXT_OP_13;
  const OpKind d_op_int_eq0     = OP_EXT_OP_14;
  const OpKind d_op_int_geq0    = OP_EXT_OP_15;
  const OpKind d_op_int_gt0     = OP_EXT_OP_16;
  const OpKind d_op_int_leq0    = OP_EXT_OP_17;
  const OpKind d_op_int_lt0     = OP_EXT_OP_18;
  const OpKind d_op_int_neq0    = OP_EXT_OP_19;
  const OpKind d_op_int_poly    = OP_EXT_OP_20;
  const OpKind d_op_int_power   = OP_EXT_OP_21;
  const OpKind d_op_int_square  = OP_EXT_OP_22;
  const OpKind d_op_real_ceil   = OP_EXT_OP_23;
  const OpKind d_op_real_floor  = OP_EXT_OP_24;
  const OpKind d_op_real_eq0    = OP_EXT_OP_25;
  const OpKind d_op_real_geq0   = OP_EXT_OP_26;
  const OpKind d_op_real_gt0    = OP_EXT_OP_27;
  const OpKind d_op_real_leq0   = OP_EXT_OP_28;
  const OpKind d_op_real_lt0    = OP_EXT_OP_29;
  const OpKind d_op_real_neq0   = OP_EXT_OP_30;
  const OpKind d_op_real_poly   = OP_EXT_OP_31;
  const OpKind d_op_real_rpoly  = OP_EXT_OP_32;
  const OpKind d_op_real_power  = OP_EXT_OP_33;
  const OpKind d_op_real_square = OP_EXT_OP_34;
};

}  // namespace yices
}  // namespace smtmbt

#endif

#endif
