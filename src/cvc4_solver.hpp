#ifdef SMTMBT_USE_CVC4

#ifndef __SMTMBT__CVC4_SOLVER_H
#define __SMTMBT__CVC4_SOLVER_H

#include "solver.hpp"

#include "cvc4/api/cvc4cpp.h"

namespace smtmbt {
namespace cvc4 {

class CVC4Term : public AbsTerm
{
  friend class CVC4Solver;

 public:
  CVC4Term(CVC4::api::Solver* cvc4, CVC4::api::Term d_term);
  ~CVC4Term() override;
  std::size_t hash() const override;
 private:
  CVC4::api::Solver* d_solver;
  CVC4::api::Term d_term;
};

class CVC4Sort : public AbsSort
{
 public:
  CVC4Sort(CVC4::api::Solver* cvc4, CVC4::api::Sort sort);
  ~CVC4Sort() override;
  std::size_t hash() const override;
 private:
  CVC4::api::Solver* d_solver;
  CVC4::api::Sort d_sort;
};

class CVC4Solver : public Solver
{
 public:
  CVC4Solver(RNGenerator& rng) : Solver(rng), d_solver(nullptr) {}

  void new_solver() override;

  void delete_solver() override;

  bool is_initialized() const override;

  void set_opt(const std::string& opt, bool value) const
  {  // TODO:
  }

  Term mk_var(Sort sort, const std::string name) const
  {  // TODO:
    return nullptr;
  }
  Term mk_const(Sort sort, const std::string name) const
  {  // TODO:
    return nullptr;
  }
  Term mk_fun(Sort sort, const std::string name) const
  {  // TODO:
    return nullptr;
  }

  Term mk_value(Sort sort, uint32_t value) const
  {  // TODO:
    return nullptr;
  }
  // TODO: more

  Sort mk_sort(const std::string name, uint32_t arity) const
  {  // TODO:
    return nullptr;
  }

  Sort mk_sort(SortKind kind) const override;
  Sort mk_sort(SortKind kind, uint32_t size) const override;

  Sort mk_sort(SortKind kind, std::vector<Sort>& sorts, Sort sort) const
  {  // TODO:
    return nullptr;
  }

  Term mk_term(const OpKindData& kind, std::vector<Term>& args) override;

  Sort get_sort(Term term) const
  {  // TODO:
    return nullptr;
  }

  void assert_formula(const Term& t) const
  {  // TODO:
  }

  Result check_sat() const
  {  // TODO:
    return Result::UNKNOWN;
  }

  //
  // get_model()
  // get_value()
  // get_proof()
  // get_unsat_core()
  //
  //
 private:
  void init_op_kinds();
  CVC4::api::Term& get_term(Term term);

  CVC4::api::Solver* d_solver;
  std::unordered_map<OpKind, CVC4::api::Kind, OpKindHashFunction> d_op_kinds;
};

}  // namespace btor
}  // namespace smtmbt

#endif

#endif

