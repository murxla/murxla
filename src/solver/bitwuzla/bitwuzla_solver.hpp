/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifdef MURXLA_USE_BITWUZLA

#ifndef __MURXLA__BITWUZLA_SOLVER_H
#define __MURXLA__BITWUZLA_SOLVER_H

#include "bitwuzla/api/cpp/bitwuzla.h"
#include "fsm.hpp"
#include "solver/solver.hpp"
#include "theory.hpp"

namespace murxla {
namespace bitwuzla {

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

class BitwuzlaSort : public AbsSort
{
  friend class BitwuzlaSolver;

 public:
  /** Get wrapped Bitwuzla sort from Murxla Sort. */
  static const ::bitwuzla::Sort& get_bitwuzla_sort(Sort sort);
  /** Convert array of Bitwuzla sorts to Murxla sorts. */
  static std::vector<Sort> bitwuzla_sorts_to_sorts(
      const std::vector<::bitwuzla::Sort>& sorts);

  BitwuzlaSort(const ::bitwuzla::Sort& sort);
  ~BitwuzlaSort() override;
  size_t hash() const override;
  bool equals(const Sort& other) const override;
  std::string to_string() const override;
  bool is_array() const override;
  bool is_bool() const override;
  bool is_bv() const override;
  bool is_fp() const override;
  bool is_fun() const override;
  bool is_rm() const override;
  uint32_t get_bv_size() const override;
  uint32_t get_fp_exp_size() const override;
  uint32_t get_fp_sig_size() const override;
  Sort get_array_index_sort() const override;
  Sort get_array_element_sort() const override;
  uint32_t get_fun_arity() const override;
  Sort get_fun_codomain_sort() const override;
  std::vector<Sort> get_fun_domain_sorts() const override;

 private:
  ::bitwuzla::Sort d_sort;
};

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

class BitwuzlaTerm : public AbsTerm
{
  friend class BitwuzlaSolver;

 public:
  /** Get wrapped Bitwuzla term from Murxla term. */
  static const ::bitwuzla::Term& get_bitwuzla_term(Term term);
  /** Convert vector of Bitwuzla terms to vector of Murxla terms. */
  static std::vector<Term> bitwuzla_terms_to_terms(
      const std::vector<::bitwuzla::Term>& terms);
  /** Convert vector of Murxla terms to vector of Bitwuzla terms. */
  static std::vector<::bitwuzla::Term> terms_to_bitwuzla_terms(
      const std::vector<Term>& terms);

  /** Map operator kinds to Bitwuzla operator kinds. */
  static std::unordered_map<Op::Kind, ::bitwuzla::Kind>
      s_kinds_to_bitwuzla_kinds;
  /** Map Bitwuzla operator kinds to operator kinds. */
  static std::unordered_map<::bitwuzla::Kind, Op::Kind>
      s_bitwuzla_kinds_to_kinds;

  /** Solver-specific operators. */
  //! [docs-bitwuzla-op-bv_dec start]
  inline static const Op::Kind OP_BV_DEC = "bitwuzla-OP_BV_DEC";
  //! [docs-bitwuzla-op-bv_dec end]
  inline static const Op::Kind OP_BV_INC    = "bitwuzla-OP_BV_INC";
  inline static const Op::Kind OP_BV_REDAND = "bitwuzla-OP_BV_REDAND";
  inline static const Op::Kind OP_BV_REDOR  = "bitwuzla-OP_BV_REDOR";
  inline static const Op::Kind OP_BV_REDXOR = "bitwuzla-OP_BV_REDXOR";
  inline static const Op::Kind OP_BV_ROL    = "bitwuzla-OP_BV_ROL";
  inline static const Op::Kind OP_BV_ROR    = "bitwuzla-OP_BV_ROR";
  inline static const Op::Kind OP_BV_SADDO  = "bitwuzla-OP_BV_SADDO";
  inline static const Op::Kind OP_BV_SDIVO  = "bitwuzla-OP_BV_SDIVO";
  inline static const Op::Kind OP_BV_SMULO  = "bitwuzla-OP_BV_SMULO";
  inline static const Op::Kind OP_BV_SSUBO  = "bitwuzla-OP_BV_SSUBO";
  inline static const Op::Kind OP_BV_UADDO  = "bitwuzla-OP_BV_UADDO";
  inline static const Op::Kind OP_BV_UMULO  = "bitwuzla-OP_BV_UMULO";
  inline static const Op::Kind OP_BV_USUBO  = "bitwuzla-OP_BV_USUBO";
  inline static const Op::Kind OP_FP_TO_FP_FROM_REAL =
      "bitwuzla-OP_FP_TO_FP_FROM_REAL";
  inline static const Op::Kind OP_IFF = "bitwuzla-OP_IFF";

  BitwuzlaTerm(const ::bitwuzla::Term& term);
  ~BitwuzlaTerm() override;
  size_t hash() const override;
  std::string to_string() const override;
  bool equals(const Term& other) const override;
  bool is_array() const override;
  bool is_bv() const override;
  bool is_fp() const override;
  bool is_fun() const override;
  bool is_rm() const override;
  bool is_bool_value() const override;
  bool is_bv_value() const override;
  bool is_fp_value() const override;
  bool is_rm_value() const override;
  bool is_special_value(const SpecialValueKind& kind) const override;
  bool is_const() const override;
  bool is_value() const override;
  bool is_var() const override;
  const Op::Kind& get_kind() const override;
  std::vector<Term> get_children() const override;
  size_t get_num_indices() const override;
  bool is_indexed() const override;
  std::vector<std::string> get_indices() const override;
  uint32_t get_bv_size() const override;
  uint32_t get_fp_exp_size() const override;
  uint32_t get_fp_sig_size() const override;
  Sort get_array_index_sort() const override;
  Sort get_array_element_sort() const override;
  uint32_t get_fun_arity() const override;
  Sort get_fun_codomain_sort() const override;
  std::vector<Sort> get_fun_domain_sorts() const override;

 private:
  ::bitwuzla::Term d_term;
};

/* -------------------------------------------------------------------------- */
/* BitwuzlaSolver                                                             */
/* -------------------------------------------------------------------------- */

class BitwuzlaSolver : public Solver
{
 public:
  /* Solver-specific states. */
  inline static const State::Kind STATE_UNKNOWN = "bitwuzla-unknown";

  /** Constructor. */
  BitwuzlaSolver(SolverSeedGenerator& sng) : Solver(sng), d_solver(nullptr) {}
  /** Destructor. */
  ~BitwuzlaSolver() override;

  void new_solver() override;

  void delete_solver() override;

  ::bitwuzla::Bitwuzla* get_solver();

  bool is_initialized() const override;

  const std::string get_name() const override;

  const std::string get_profile() const override;

  void configure_fsm(FSM* fsm) const override;
  void disable_unsupported_actions(FSM* fsm) const override;
  void configure_opmgr(OpKindManager* opmgr) const override;
  void configure_options(SolverManager* smgr) const override;

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

  Term mk_fun(const std::string& name,
              const std::vector<Term>& args,
              Term body) override;

  Term mk_value(Sort sort, bool value) override;
  Term mk_value(Sort sort, const std::string& value) override;
  Term mk_value(Sort sort, const std::string& value, Base base) override;

  Term mk_special_value(Sort sort,
                        const AbsTerm::SpecialValueKind& value) override;

  Sort mk_sort(SortKind kind) override;
  Sort mk_sort(SortKind kind, uint32_t size) override;
  Sort mk_sort(SortKind kind, uint32_t esize, uint32_t ssize) override;
  Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) override;

  Term mk_term(const Op::Kind& kind,
               const std::vector<Term>& args,
               const std::vector<uint32_t>& indices) override;

  Sort get_sort(Term term, SortKind sort_kind) override;

  void assert_formula(const Term& t) override;

  Result check_sat() override;
  Result check_sat_assuming(const std::vector<Term>& assumptions) override;

  std::vector<Term> get_unsat_assumptions() override;

  std::vector<Term> get_unsat_core() override;

  std::vector<Term> get_value(const std::vector<Term>& terms) override;

  void push(uint32_t n_levels) override;
  void pop(uint32_t n_levels) override;

  void print_model() override;

  void reset() override;
  void reset_assertions() override;

  void check_term(Term term) override;

  //
  // get_model()
  // get_proof()
  //
  //
 private:
  void init_solver();
  ::bitwuzla::Term mk_value_bv_uint64(Sort sort, uint64_t value);
  ::bitwuzla::Term mk_value_bv_int64(Sort sort, int64_t value);

  std::unique_ptr<::bitwuzla::Bitwuzla> d_solver;
  std::unique_ptr<::bitwuzla::Options> d_options;
  std::unordered_map<std::string, ::bitwuzla::Option> d_option_name_to_enum;
  std::unordered_map<std::string, ::bitwuzla::Kind> d_op_kinds;

  uint64_t d_num_symbols;
};

}  // namespace bitwuzla
}  // namespace murxla

#endif

#endif
