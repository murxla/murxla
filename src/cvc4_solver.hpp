#ifdef SMTMBT_USE_CVC4

#ifndef __SMTMBT__CVC4_SOLVER_H
#define __SMTMBT__CVC4_SOLVER_H

#include "solver.hpp"

#include "cvc4/api/cvc4cpp.h"

namespace smtmbt {
namespace cvc4 {

class CVC4Term : public AbsTerm
{
 public:
  CVC4Term(){};
  ~CVC4Term() override;
  std::size_t hash() const override;
  CVC4Term* copy() const override;
 private:
  CVC4::api::Term d_term;
};

class CVC4Sort : public AbsSort
{
 public:
  CVC4Sort(CVC4::api::Sort sort) : d_sort(sort){};
  ~CVC4Sort() override;
  std::size_t hash() const override;
  CVC4Sort* copy() const override;
 private:
  CVC4::api::Sort d_sort;
};

class CVC4Solver : public Solver
{
 public:
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
  Sort mk_sort(SortKind kind) const
  {  // TODO:
    return nullptr;
  }
  Sort mk_sort(SortKind kind, uint32_t size) const override;

  Sort mk_sort(SortKind kind, std::vector<Sort>& sorts, Sort sort) const
  {  // TODO:
    return nullptr;
  }

  Sort get_sort(Term term) const
  {  // TODO:
    return nullptr;
  }

  Op mk_op(OpKind kind) const
  {  // TODO:
    return Op();
  }
  Op mk_op(OpKind kind, std::vector<uint32_t>& indices) const
  {  // TODO:
    return Op();
  }

  Term apply(Op op, std::vector<Term>& children) const
  {  // TODO:
    return nullptr;
  }
  Term apply(Term term, std::vector<Term>& children) const
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
  // RNG?
  CVC4::api::Solver* d_solver;
};

}  // namespace btor
}  // namespace smtmbt

#endif

#endif

