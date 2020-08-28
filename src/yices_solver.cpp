#include "yices_solver.hpp"

#include "yices.h"

namespace smtmbt {
namespace yices {

/* -------------------------------------------------------------------------- */
/* YicesSort */
/* -------------------------------------------------------------------------- */

size_t
YicesSort::hash() const
{
  return d_sort;
}

bool
YicesSort::equals(const Sort& other) const
{
  YicesSort* yices_sort = dynamic_cast<YicesSort*>(other.get());
  if (yices_sort)
  {
    return d_sort == yices_sort->d_sort;
  }
  return false;
}

bool
YicesSort::is_bool() const
{
  return yices_type_is_bool(d_sort);
}

bool
YicesSort::is_bv() const
{
  return yices_type_is_bitvector(d_sort);
}

bool
YicesSort::is_fp() const
{
  return false;
}

bool
YicesSort::is_int() const
{
  bool res = yices_type_is_int(d_sort);
  assert(!res || yices_type_is_arithmetic(d_sort));
  return res;
}

bool
YicesSort::is_real() const
{
  bool res = yices_type_is_real(d_sort);
  assert(!res || yices_type_is_arithmetic(d_sort));
  return res;
}

bool
YicesSort::is_rm() const
{
  return false;
}

uint32_t
YicesSort::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = yices_bvtype_size(d_sort);
  assert(res);
  return res;
}

/* -------------------------------------------------------------------------- */
/* YicesTerm */
/* -------------------------------------------------------------------------- */

size_t
YicesTerm::hash() const
{
  return d_term;
}

bool
YicesTerm::equals(const Term& other) const
{
  YicesTerm* yices_term = dynamic_cast<YicesTerm*>(other.get());
  if (yices_term)
  {
    return d_term == yices_term->d_term;
  }
  return false;
}

/* -------------------------------------------------------------------------- */
/* YicesSolver */
/* -------------------------------------------------------------------------- */

void
YicesSolver::new_solver()
{
  yices_init();
  d_context = yices_new_context(nullptr);
}

void
YicesSolver::delete_solver()
{
  yices_free_context(d_context);
  yices_exit();
}

bool
YicesSolver::is_initialized() const
{
  return d_context != nullptr;
}

TheoryIdVector
YicesSolver::get_supported_theories() const
{
  return {THEORY_ARRAY, THEORY_BV, THEORY_BOOL, THEORY_INT, THEORY_REAL};
}

OpKindSet
YicesSolver::get_unsupported_op_kinds() const
{
  return {};
}

void
YicesSolver::configure_fsm(FSM* fsm) const
{
  // TODO
}

void
YicesSolver::set_opt(const std::string& opt, const std::string& value)
{
  // TODO
}

bool
YicesSolver::check_failed_assumption(const Term& t) const
{
  // TODO
}

std::string
YicesSolver::get_option_name_incremental() const
{
  // TODO
}

std::string
YicesSolver::get_option_name_model_gen() const
{
  // TODO
}

std::string
YicesSolver::get_option_name_unsat_assumptions() const
{
  // TODO
}

bool
YicesSolver::option_incremental_enabled() const
{
  // TODO
}

bool
YicesSolver::option_model_gen_enabled() const
{
  // TODO
}

bool
YicesSolver::option_unsat_assumptions_enabled() const
{
  // TODO
}

term_t
YicesSolver::get_yices_term(Term term) const
{
  // TODO
}

Term
YicesSolver::mk_var(Sort sort, const std::string& name)
{
  // TODO
}

Term
YicesSolver::mk_const(Sort sort, const std::string& name)
{
  // TODO
}

Term
YicesSolver::mk_value(Sort sort, bool value)
{
  // TODO
}

Term
YicesSolver::mk_value(Sort sort, std::string num, std::string den)
{
  // TODO
}

Term
YicesSolver::mk_value(Sort sort, std::string value, Base base)
{
  // TODO
}

Sort
YicesSolver::mk_sort(SortKind kind)
{
  // TODO
}

Sort
YicesSolver::mk_sort(SortKind kind, uint32_t size)
{
  // TODO
}

Sort
YicesSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  // TODO
}

Term
YicesSolver::mk_term(const OpKind& kind,
                     std::vector<Term>& args,
                     std::vector<uint32_t>& params)
{
  // TODO
}

Sort
YicesSolver::get_sort(Term term, SortKind sort_kind) const
{
  // TODO
}

void
YicesSolver::assert_formula(const Term& t) const
{
  // TODO
}

Solver::Result
YicesSolver::check_sat() const
{
  // TODO
}

Solver::Result
YicesSolver::check_sat_assuming(std::vector<Term>& assumptions) const
{
  // TODO
}

std::vector<Term>
YicesSolver::get_unsat_assumptions() const
{
  // TODO
}

std::vector<Term>
YicesSolver::get_value(std::vector<Term>& terms) const
{
  // TODO
}

void
YicesSolver::push(uint32_t n_levels) const
{
  // TODO
}

void
YicesSolver::pop(uint32_t n_levels) const
{
  // TODO
}

void
YicesSolver::print_model() const
{
  // TODO
}

void
YicesSolver::reset_assertions() const
{
  // TODO
}

}  // namespace yices
}  // namespace smtmbt
