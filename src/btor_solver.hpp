#ifdef SMTMBT_USE_BOOLECTOR

#ifndef __SMTMBT__BTOR_SOLVER_H
#define __SMTMBT__BTOR_SOLVER_H

#include "solver.hpp"

extern "C" {
struct Btor;
}

namespace smtmbt {
namespace btor {

class BtorTerm : public AbsTerm
{
 public:
  BtorTerm(){};
  ~BtorTerm() override;
  std::size_t hash() const override;
  BtorTerm* copy() const override;
};

class BtorSort : public AbsSort
{
 public:
  BtorSort(){};
  ~BtorSort() override;
  std::size_t hash() const override;
  BtorSort* copy() const override;
};

class BtorSolver : public Solver
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
  Sort mk_sort(SortKind kind, uint32_t size) const
  {  // TODO:
    return nullptr;
  }
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
  Btor* d_solver;
};

}  // namespace btor
}  // namespace smtmbt

#endif

#endif
