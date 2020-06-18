#ifdef SMTMBT_USE_CVC4

#ifndef __SMTMBT__CVC4_SOLVER_H
#define __SMTMBT__CVC4_SOLVER_H

#include "cvc4/api/cvc4cpp.h"
#include "fsm.hpp"
#include "solver.hpp"

namespace smtmbt {
namespace cvc4 {

/* -------------------------------------------------------------------------- */
/* CVC4Sort                                                                   */
/* -------------------------------------------------------------------------- */

class CVC4Sort : public AbsSort
{
  friend class CVC4Solver;

 public:
  CVC4Sort(CVC4::api::Solver* cvc4, CVC4::api::Sort sort);
  ~CVC4Sort() override;
  size_t hash() const override;
  bool equals(const Sort& other) const override;
  bool is_bool() const override;
  bool is_bv() const override;
  uint32_t get_bv_size() const override;

 private:
  CVC4::api::Solver* d_solver;
  CVC4::api::Sort d_sort;
};

/* -------------------------------------------------------------------------- */
/* CVC4Term                                                                   */
/* -------------------------------------------------------------------------- */

class CVC4Term : public AbsTerm
{
  friend class CVC4Solver;

 public:
  CVC4Term(CVC4::api::Solver* cvc4, CVC4::api::Term d_term);
  ~CVC4Term() override;
  size_t hash() const override;
  bool equals(const Term& other) const override;

 private:
  CVC4::api::Solver* d_solver = nullptr;
  CVC4::api::Term d_term;
};

/* -------------------------------------------------------------------------- */
/* CVC4Solver                                                                 */
/* -------------------------------------------------------------------------- */

class CVC4Solver : public Solver
{
 public:
  CVC4Solver(RNGenerator& rng) : Solver(rng), d_solver(nullptr) {}

  OpKindSet get_unsupported_op_kinds() const override;

  void new_solver() override;

  void delete_solver() override;

  CVC4::api::Solver* get_solver();
  CVC4::api::Term& get_cvc4_term(Term term) const;

  bool is_initialized() const override;

  void configure_fsm(FSM* fsm) const override;

  bool check_failed_assumption(const Term& t) const override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;
  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;
  std::string get_option_value_enable_incremental() const override;
  std::string get_option_value_enable_model_gen() const override;
  std::string get_option_value_enable_unsat_assumptions() const override;

  std::vector<CVC4::api::Term> terms_to_cvc4_terms(
      std::vector<Term>& terms) const;

  Term mk_var(Sort sort, const std::string name) const override
  {  // TODO:
    return nullptr;
  }
  Term mk_fun(Sort sort, const std::string name) const override
  {  // TODO:
    return nullptr;
  }

  Term mk_value(Sort sort, bool value) const override;
  Term mk_value(Sort sort, uint64_t value) const override;
  Term mk_value(Sort sort, std::string value, Base base) const override;

  Sort mk_sort(const std::string name, uint32_t arity) const override
  {  // TODO:
    return nullptr;
  }

  Sort mk_sort(SortKind kind) const override;
  Sort mk_sort(SortKind kind, uint32_t size) const override;
  Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) const override;

  Term mk_const(Sort sort, const std::string name) const override;
  Term mk_term(const OpKind& kind,
               std::vector<Term>& args,
               std::vector<uint32_t>& params) const override;

  Sort get_sort(Term term) const override;

  void assert_formula(const Term& t) const override;

  Result check_sat() const override;
  Result check_sat_assuming(std::vector<Term>& assumptions) const override;

  std::vector<Term> get_unsat_assumptions() const override;

  std::vector<Term> get_value(std::vector<Term>& terms) const override;

  void push(uint32_t n_levels) const override;
  void pop(uint32_t n_levels) const override;

  void print_model() const override;

  void reset_assertions() const override;

  void set_opt(const std::string& opt, const std::string& value) const override;

  //
  // get_model()
  // get_proof()
  // get_unsat_core()
  //
  //
 private:
  void init_op_kinds();
  CVC4::api::Sort& get_cvc4_sort(Sort sort) const;
  std::vector<Term> cvc4_terms_to_terms(
      std::vector<CVC4::api::Term>& terms) const;

  CVC4::api::Solver* d_solver;
  std::unordered_map<OpKind, CVC4::api::Kind, OpKindHashFunction> d_kinds;
  std::unordered_map<OpKind, CVC4::api::Kind, OpKindHashFunction> d_op_kinds;
};

}  // namespace btor
}  // namespace smtmbt

#endif

#endif

