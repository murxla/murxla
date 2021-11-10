#ifdef MURXLA_USE_YICES

#ifndef __MURXLA__YICES_SOLVER_H
#define __MURXLA__YICES_SOLVER_H

#include <bitset>

#include "fsm.hpp"
#include "solver.hpp"
#include "theory.hpp"
#include "yices.h"

namespace murxla {
namespace yices {

/* -------------------------------------------------------------------------- */
/* YicesSort */
/* -------------------------------------------------------------------------- */

class YicesSort : public AbsSort
{
  friend class YicesSolver;

 public:
  /** Get wrapped Yices sort from Murxla sort. */
  static type_t get_yices_sort(Sort sort);
  /** Convert vector of Murxla sorts to Yices sorts. */
  static std::vector<type_t> sorts_to_yices_sorts(
      const std::vector<Sort>& sorts);

  YicesSort(type_t sort) : d_sort(sort) {}
  ~YicesSort() override {}
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
  bool is_reglan() const override;
  bool is_rm() const override;
  bool is_seq() const override;
  bool is_set() const override;
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
  /** Get wrapped Yices term from Murxla term. */
  static term_t get_yices_term(Term term);
  /** Convert vector of Yices terms to vector Murxla terms. */
  static std::vector<Term> yices_terms_to_terms(term_vector_t* terms);
  static std::vector<Term> yices_terms_to_terms(
      const std::vector<term_t>& terms);
  /** Convert vector of Murxla terms to vector Yices terms. */
  static std::vector<term_t> terms_to_yices_terms(
      const std::vector<Term>& terms);

  /* Solver-specific operators. */
  // BV
  inline static const Op::Kind OP_ASHIFT_RIGHT = "yices-OP_ASHIFT_RIGHT";
  inline static const Op::Kind OP_BITEXTRACT   = "yices-OP_BITEXTRACT";
  inline static const Op::Kind OP_BVARRAY      = "yices-OP_BVARRAY";
  inline static const Op::Kind OP_BVPOWER      = "yices-OP_BVPOWER";
  inline static const Op::Kind OP_BVSQUARE     = "yices-OP_BVSQUARE";
  inline static const Op::Kind OP_REDAND       = "yices-OP_REDAND";
  inline static const Op::Kind OP_REDOR        = "yices-OP_REDOR";
  inline static const Op::Kind OP_SHIFT_LEFT0  = "yices-OP_SHIFT_LEFT0";
  inline static const Op::Kind OP_SHIFT_LEFT1  = "yices-OP_SHIFT_LEFT1";
  inline static const Op::Kind OP_SHIFT_RIGHT0 = "yices-OP_SHIFT_RIGHT0";
  inline static const Op::Kind OP_SHIFT_RIGHT1 = "yices-OP_SHIFT_RIGHT1";
  // Arithmetic
  inline static const Op::Kind OP_INT_CEIL    = "yices-OP_INT_CEIL";
  inline static const Op::Kind OP_INT_FLOOR   = "yices-OP_INT_FLOOR";
  inline static const Op::Kind OP_INT_EQ0     = "yices-OP_INT_EQ0";
  inline static const Op::Kind OP_INT_GEQ0    = "yices-OP_INT_GEQ0";
  inline static const Op::Kind OP_INT_GT0     = "yices-OP_INT_GT0";
  inline static const Op::Kind OP_INT_LEQ0    = "yices-OP_INT_LEQ0";
  inline static const Op::Kind OP_INT_LT0     = "yices-OP_INT_LT0";
  inline static const Op::Kind OP_INT_NEQ0    = "yices-OP_INT_NEQ0";
  inline static const Op::Kind OP_INT_POLY    = "yices-OP_INT_POLY";
  inline static const Op::Kind OP_INT_POWER   = "yices-OP_INT_POWER";
  inline static const Op::Kind OP_INT_SQUARE  = "yices-OP_INT_SQUARE";
  inline static const Op::Kind OP_REAL_CEIL   = "yices-OP_REAL_CEIL";
  inline static const Op::Kind OP_REAL_FLOOR  = "yices-OP_REAL_FLOOR";
  inline static const Op::Kind OP_REAL_EQ0    = "yices-OP_REAL_EQ0";
  inline static const Op::Kind OP_REAL_GEQ0   = "yices-OP_REAL_GEQ0";
  inline static const Op::Kind OP_REAL_GT0    = "yices-OP_REAL_GT0";
  inline static const Op::Kind OP_REAL_LEQ0   = "yices-OP_REAL_LEQ0";
  inline static const Op::Kind OP_REAL_LT0    = "yices-OP_REAL_LT0";
  inline static const Op::Kind OP_REAL_NEQ0   = "yices-OP_REAL_NEQ0";
  inline static const Op::Kind OP_REAL_POLY   = "yices-OP_REAL_POLY";
  inline static const Op::Kind OP_REAL_RPOLY  = "yices-OP_REAL_RPOLY";
  inline static const Op::Kind OP_REAL_POWER  = "yices-OP_REAL_POWER";
  inline static const Op::Kind OP_REAL_SQUARE = "yices-OP_REAL_SQUARE";

  YicesTerm(term_t term) : d_term(term) {}
  ~YicesTerm() override {}
  size_t hash() const override;
  std::string to_string() const override;
  bool equals(const Term& other) const override;
  bool is_array() const override;
  bool is_bool() const override;
  bool is_bv() const override;
  bool is_fun() const override;
  bool is_int() const override;
  bool is_real() const override;

  uint32_t get_bv_size() const override;

 private:
  term_t d_term = 0;
};

/* -------------------------------------------------------------------------- */
/* YicesSolver */
/* -------------------------------------------------------------------------- */

class YicesSolver : public Solver
{
 public:
  YicesSolver(SolverSeedGenerator& sng) : Solver(sng) {}
  ~YicesSolver() override;

  void new_solver() override;
  void delete_solver() override;
  bool is_initialized() const override;
  const std::string get_name() const override;

  TheoryIdVector get_supported_theories() const override;
  SortKindSet get_unsupported_array_index_sort_kinds() const override;
  SortKindSet get_unsupported_array_element_sort_kinds() const override;
  SortKindSet get_unsupported_fun_domain_sort_kinds() const override;
  SortKindSet get_unsupported_fun_codomain_sort_kinds() const override;

  void configure_fsm(FSM* fsm) const override;
  void configure_opmgr(OpKindManager* opmgr) const override;
  void reset() override;
  void reset_sat() override;

  void set_opt(const std::string& opt, const std::string& value) override;

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
  Term mk_value(Sort sort, std::string value) override;
  Term mk_value(Sort sort, std::string num, std::string den) override;
  Term mk_value(Sort sort, std::string value, Base base) override;

  Term mk_special_value(Sort sort,
                        const AbsTerm::SpecialValueKind& value) override;

  Sort mk_sort(const std::string name, uint32_t arity) override
  {  // TODO:
    return nullptr;
  }

  Sort mk_sort(SortKind kind) override;
  Sort mk_sort(SortKind kind, uint32_t size) override;

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

  void reset_assertions() override;

  //
  // get_model()
  // get_proof()
  //
  //
 private:
  bool is_valid_sort(type_t sort) const;
  bool is_valid_term(term_t term) const;
  bool check_bits(uint32_t bw, term_t term, std::string& expected) const;

  std::vector<int32_t> bin_str_to_int_array(std::string s) const;

  term_t mk_term_left_assoc(std::vector<term_t>& args,
                            term_t (*fun)(term_t, term_t)) const;
  term_t mk_term_right_assoc(std::vector<term_t>& args,
                             term_t (*fun)(term_t, term_t)) const;
  term_t mk_term_pairwise(std::vector<term_t>& args,
                          term_t (*fun)(term_t, term_t)) const;
  term_t mk_term_chained(std::vector<term_t>& args,
                         term_t (*fun)(term_t, term_t)) const;

  bool d_is_initialized  = false;
  bool d_incremental     = false;
  ctx_config_t* d_config = nullptr;
  context_t* d_context   = nullptr;
  model_t* d_model       = nullptr;
};

}  // namespace yices
}  // namespace murxla

#endif

#endif
