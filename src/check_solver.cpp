#include "check_solver.hpp"

namespace murxla {

using namespace shadow;

CheckSolver::CheckSolver(SolverSeedGenerator& sng,
                         Solver* solver,
                         Solver* solver_check)
    : ShadowSolver(sng, solver, solver_check)
{
  d_same_solver = false;
}

CheckSolver::~CheckSolver() {}

void
CheckSolver::delete_solver()
{
  d_assertions.clear();
  d_assumptions.clear();
  d_assumptions_shadow.clear();
  ShadowSolver::delete_solver();
}

bool
CheckSolver::option_unsat_cores_enabled() const
{
  return d_solver->option_unsat_cores_enabled();
}

void
CheckSolver::assert_formula(const Term& t)
{
  ShadowTerm* term = checked_cast<ShadowTerm*>(t.get());
  assert(term);
  d_solver->assert_formula(term->get_term());
  d_assertions[term->get_term()] = term->get_term_shadow();
}

Solver::Result
CheckSolver::check_sat()
{
  d_assumptions_shadow.clear();
  return d_solver->check_sat();
}

Solver::Result
CheckSolver::check_sat_assuming(const std::vector<Term>& assumptions)
{
  d_assumptions_shadow.clear();
  d_assumptions.clear();

  std::vector<Term> assumptions_orig;
  ShadowSolver::get_terms_helper(
      assumptions, assumptions_orig, d_assumptions_shadow);
  for (size_t i = 0, size = assumptions.size(); i < size; ++i)
  {
    d_assumptions.emplace(assumptions_orig[i], d_assumptions_shadow[i]);
  }
  return d_solver->check_sat_assuming(assumptions_orig);
}

std::vector<Term>
CheckSolver::get_unsat_core()
{
  std::vector<Term> terms, terms_shadow;
  auto unsat_core = d_solver->get_unsat_core();

  // Check unsat core with d_solver_shadow
  d_solver_shadow->push(1);
  for (const Term& t : unsat_core)
  {
    if (d_assertions.find(t) != d_assertions.end())
    {
      d_solver_shadow->assert_formula(d_assertions.at(t));
    }
    else if (d_assumptions.find(t) != d_assumptions.end())
    {
      d_solver_shadow->assert_formula(d_assumptions.at(t));
    }
  }
  Result res = d_solver_shadow->check_sat_assuming(d_assumptions_shadow);
  MURXLA_TEST(res == Result::UNSAT);
  d_solver_shadow->pop(1);

  return std::vector<Term>();
}

std::vector<Term>
CheckSolver::get_unsat_assumptions()
{
  auto unsat_assumptions = d_solver->get_unsat_assumptions();

  for (const Term& t : unsat_assumptions)
  {
    MURXLA_TEST(d_solver->is_unsat_assumption(t));
  }

  /* Check unsat assumptions with d_solver. */
  MURXLA_TEST(d_solver->check_sat_assuming(unsat_assumptions) == Result::UNSAT);

  return std::vector<Term>();
}

void
CheckSolver::print_model()
{
  d_solver->print_model();
}

void
CheckSolver::set_opt(const std::string& opt, const std::string& value)
{
  // Do not reset incremental usage of d_solver_shadow since it is required for
  // checking unsat cores
  if (opt == d_solver->get_option_name_incremental())
  {
    d_solver->set_opt(opt, value);
    d_incremental = value == "true";
  }
  else
  {
    ShadowSolver::set_opt(opt, value);
  }
  if (opt == d_solver->get_option_name_unsat_cores() && value == "true")
  {
    d_solver_shadow->set_opt(d_solver_shadow->get_option_name_incremental(),
                             "true");
  }
}

std::vector<Term>
CheckSolver::get_value(const std::vector<Term>& terms)
{
  std::vector<Term> res, terms_orig, terms_shadow;
  get_terms_helper(terms, terms_orig, terms_shadow);
  auto values_orig = d_solver->get_value(terms_orig);

  /* Check values with d_shadow. */
  if (d_incremental)
  {
    std::vector<Term> assumptions;
    for (size_t i = 0, n = terms_orig.size(); i < n; ++i)
    {
      assumptions.push_back(
          d_solver->mk_term(Op::EQUAL, {terms_orig[i], values_orig[i]}, {}));
    }
    MURXLA_TEST(d_solver->check_sat_assuming(assumptions)
                == Solver::Result::SAT);
  }
  return std::vector<Term>();
}

void
CheckSolver::reset()
{
  d_assertions.clear();
  d_assumptions.clear();
  d_assumptions_shadow.clear();
  d_incremental = false;
  ShadowSolver::reset();
}

void
CheckSolver::disable_unsupported_actions(FSM* fsm) const
{
  d_solver->disable_unsupported_actions(fsm);
  d_solver_shadow->disable_unsupported_actions(fsm);
}

}  // namespace murxla
