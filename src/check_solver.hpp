#ifndef __MURXLA__CHECK_SOLVER_H
#define __MURXLA__CHECK_SOLVER_H

#include "shadow_solver.hpp"

namespace murxla {

class CheckSolver : public shadow::ShadowSolver
{
 public:
  CheckSolver(RNGenerator& rng, Solver* solver, Solver* solver_check);
  ~CheckSolver() override;

  bool option_unsat_cores_enabled() const override;

  void assert_formula(const Term& t) override;

  Solver::Result check_sat() override;
  Result check_sat_assuming(std::vector<Term>& assumptions) override;

  std::vector<Term> get_unsat_core() override;
  std::vector<Term> get_unsat_assumptions() override;

  void print_model() override;

  void set_opt(const std::string& opt, const std::string& value) override;

  std::vector<Term> get_value(std::vector<Term>& terms) override;

  void disable_unsupported_actions(FSM* fsm) const override;

 private:
  /**
   * Need a custom equality comparison since terms from the wrapped solvers may
   * have incomplete information about sorts. Thus, we only ask the wrapped
   * solvers if terms are equal.
   */
  class Equal
  {
   public:
    bool operator()(const Term& t1, const Term& t2) const
    {
      return t1->equals(t2);
    }
  };

  std::unordered_map<Term, Term, std::hash<Term>, Equal> d_assertions;

  std::vector<Term> d_assumptions_shadow;
  std::unordered_map<Term, Term, std::hash<Term>, Equal> d_assumptions;

  /* Flag whether incremental was enabled for d_solver. */
  bool d_incremental = false;
};

}  // namespace murxla

#endif