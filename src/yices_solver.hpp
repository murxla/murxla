#ifdef SMTMBT_USE_YICES

#ifndef __SMTMBT__YICES_SOLVER_H
#define __SMTMBT__YICES_SOLVER_H

#include "fsm.hpp"
#include "solver.hpp"
#include "theory.hpp"
#include "yices_types.h"

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
  bool is_bool() const override;
  bool is_bv() const override;
  bool is_fp() const override;
  bool is_int() const override;
  bool is_real() const override;
  bool is_rm() const override;
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
  // OpKindSet get_supported_op_kinds() const override; // check if needed
  OpKindSet get_unsupported_op_kinds() const override;  // check if needed

  void configure_fsm(FSM* fsm) const override;

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

  void assert_formula(const Term& t) const override;

  Result check_sat() const override;
  Result check_sat_assuming(std::vector<Term>& assumptions) const override;

  std::vector<Term> get_unsat_assumptions() const override;

  std::vector<Term> get_value(std::vector<Term>& terms) const override;

  void push(uint32_t n_levels) const override;
  void pop(uint32_t n_levels) const override;

  void print_model() const override;

  void reset_assertions() const override;

  //
  // get_model()
  // get_proof()
  // get_unsat_core()
  //
  //
 private:
  context_t* d_context = nullptr;
  type_t get_yices_sort(Sort sort) const;
};

}  // namespace yices
}  // namespace smtmbt

#endif

#endif
