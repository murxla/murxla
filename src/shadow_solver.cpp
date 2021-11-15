#include "shadow_solver.hpp"

namespace murxla {
namespace shadow {

ShadowSort::ShadowSort(Sort sort, Sort sort_shadow)
    : d_sort(sort), d_sort_shadow(sort_shadow)
{
}

ShadowSort::~ShadowSort() {}

size_t
ShadowSort::hash() const
{
  return d_sort->hash();
}

bool
ShadowSort::equals(const Sort& other) const
{
  ShadowSort* s_sort = dynamic_cast<ShadowSort*>(other.get());
  return d_sort->equals(s_sort->d_sort)
         && d_sort_shadow->equals(s_sort->d_sort_shadow);
}

std::string
ShadowSort::to_string() const
{
  return d_sort->to_string();
}

bool
ShadowSort::is_array() const
{
  return d_sort->is_array();
}

bool
ShadowSort::is_bool() const
{
  return d_sort->is_bool();
}

bool
ShadowSort::is_bv() const
{
  return d_sort->is_bv();
}

bool
ShadowSort::is_fp() const
{
  return d_sort->is_fp();
}

bool
ShadowSort::is_fun() const
{
  return d_sort->is_fun();
}

bool
ShadowSort::is_int() const
{
  return d_sort->is_int();
}

bool
ShadowSort::is_real() const
{
  return d_sort->is_real();
}

bool
ShadowSort::is_rm() const
{
  return d_sort->is_rm();
}

bool
ShadowSort::is_seq() const
{
  return d_sort->is_seq();
}

bool
ShadowSort::is_set() const
{
  return d_sort->is_set();
}

bool
ShadowSort::is_string() const
{
  return d_sort->is_string();
}

bool
ShadowSort::is_reglan() const
{
  return d_sort->is_reglan();
}

uint32_t
ShadowSort::get_bv_size() const
{
  uint32_t res = d_sort->get_bv_size();
  MURXLA_TEST(res == d_sort_shadow->get_bv_size());
  return res;
}

uint32_t
ShadowSort::get_fp_exp_size() const
{
  uint32_t res = d_sort->get_fp_exp_size();
  MURXLA_TEST(res == d_sort_shadow->get_fp_exp_size());
  return res;
}

uint32_t
ShadowSort::get_fp_sig_size() const
{
  uint32_t res = d_sort->get_fp_sig_size();
  MURXLA_TEST(res == d_sort_shadow->get_fp_sig_size());
  return res;
}

Sort
ShadowSort::get_array_index_sort() const
{
  std::shared_ptr<ShadowSort> res(new ShadowSort(
      d_sort->get_array_index_sort(), d_sort_shadow->get_array_index_sort()));
  return res;
}

Sort
ShadowSort::get_array_element_sort() const
{
  std::shared_ptr<ShadowSort> res(
      new ShadowSort(d_sort->get_array_element_sort(),
                     d_sort_shadow->get_array_element_sort()));
  return res;
}

uint32_t
ShadowSort::get_fun_arity() const
{
  uint32_t res = d_sort->get_fun_arity();
  MURXLA_TEST(res == d_sort_shadow->get_fun_arity());
  return res;
}

Sort
ShadowSort::get_fun_codomain_sort() const
{
  std::shared_ptr<ShadowSort> res(new ShadowSort(
      d_sort->get_fun_codomain_sort(), d_sort_shadow->get_fun_codomain_sort()));
  return res;
}

std::vector<Sort>
ShadowSort::get_fun_domain_sorts() const
{
  std::vector<Sort> sorts        = d_sort->get_fun_domain_sorts();
  std::vector<Sort> sorts_shadow = d_sort_shadow->get_fun_domain_sorts();
  MURXLA_TEST(sorts.size() == sorts_shadow.size());
  std::vector<Sort> res;
  for (size_t i = 0, n = sorts.size(); i < n; ++i)
  {
    res.push_back(
        std::shared_ptr<ShadowSort>(new ShadowSort(sorts[i], sorts_shadow[i])));
  }
  return res;
}

Sort
ShadowSort::get_seq_element_sort() const
{
  std::shared_ptr<ShadowSort> res(new ShadowSort(
      d_sort->get_seq_element_sort(), d_sort_shadow->get_seq_element_sort()));
  return res;
}

Sort
ShadowSort::get_set_element_sort() const
{
  std::shared_ptr<ShadowSort> res(new ShadowSort(
      d_sort->get_set_element_sort(), d_sort_shadow->get_set_element_sort()));
  return res;
}

void
ShadowSort::set_kind(SortKind sort_kind)
{
  d_sort->set_kind(sort_kind);
  d_sort_shadow->set_kind(sort_kind);
  d_kind = sort_kind;
}

void
ShadowSort::set_sorts(const std::vector<Sort>& sorts)
{
  std::vector<Sort> sorts_orig, sorts_shadow;
  ShadowSolver::get_sorts_helper(sorts, sorts_orig, sorts_shadow);
  d_sort->set_sorts(sorts_orig);
  d_sort_shadow->set_sorts(sorts_shadow);
  d_sorts = sorts;
}

ShadowTerm::ShadowTerm(Term term, Term term_shadow)
    : d_term(term), d_term_shadow(term_shadow){};

ShadowTerm::~ShadowTerm() {}

size_t
ShadowTerm::hash() const
{
  return d_term->hash() + d_term_shadow->hash();
}
bool
ShadowTerm::equals(const Term& other) const
{
  ShadowTerm* s_term = dynamic_cast<ShadowTerm*>(other.get());
  if (s_term)
  {
    return d_term->equals(s_term->d_term)
           && d_term_shadow->equals(s_term->d_term_shadow);
  }
  return false;
}
std::string
ShadowTerm::to_string() const
{
  return d_term->to_string();
}

const Op::Kind&
ShadowTerm::get_kind() const
{
  return d_term->get_kind();
}

bool
ShadowTerm::is_array() const
{
  return d_term->is_array();
}
bool
ShadowTerm::is_bool() const
{
  return d_term->is_bool();
}
bool
ShadowTerm::is_bv() const
{
  return d_term->is_bv();
}
bool
ShadowTerm::is_fp() const
{
  return d_term->is_fp();
}
bool
ShadowTerm::is_fun() const
{
  return d_term->is_fun();
}
bool
ShadowTerm::is_int() const
{
  return d_term->is_int();
}
bool
ShadowTerm::is_real() const
{
  return d_term->is_real();
}
bool
ShadowTerm::is_rm() const
{
  return d_term->is_rm();
}
bool
ShadowTerm::is_string() const
{
  return d_term->is_string();
}
bool
ShadowTerm::is_reglan() const
{
  return d_term->is_reglan();
}

bool
ShadowTerm::is_bool_value() const
{
  return d_term->is_bool_value();
}

bool
ShadowTerm::is_bv_value() const
{
  return d_term->is_bv_value();
}

bool
ShadowTerm::is_fp_value() const
{
  return d_term->is_fp_value();
}

bool
ShadowTerm::is_int_value() const
{
  return d_term->is_int_value();
}

bool
ShadowTerm::is_real_value() const
{
  return d_term->is_real_value();
}

bool
ShadowTerm::is_reglan_value() const
{
  return d_term->is_reglan_value();
}

bool
ShadowTerm::is_rm_value() const
{
  return d_term->is_rm_value();
}

bool
ShadowTerm::is_string_value() const
{
  return d_term->is_string_value();
}

bool
ShadowTerm::is_special_value(const SpecialValueKind& kind) const
{
  return d_term->is_special_value(kind);
}

bool
ShadowTerm::is_const() const
{
  return d_term->is_const();
}

void
ShadowTerm::set_sort(Sort sort)
{
  AbsTerm::set_sort(sort);
  ShadowSort* s = dynamic_cast<ShadowSort*>(sort.get());
  assert(s);
  d_term->set_sort(s->d_sort);
  d_term_shadow->set_sort(s->d_sort_shadow);
}

void
ShadowTerm::set_special_value_kind(const SpecialValueKind& value_kind)
{
  AbsTerm::set_special_value_kind(value_kind);
  d_term->set_special_value_kind(value_kind);
  d_term_shadow->set_special_value_kind(value_kind);
}

void
ShadowTerm::set_leaf_kind(LeafKind kind)
{
  AbsTerm::set_leaf_kind(kind);
  d_term->set_leaf_kind(kind);
  d_term_shadow->set_leaf_kind(kind);
}

ShadowSolver::ShadowSolver(SolverSeedGenerator& sng,
                           Solver* solver,
                           Solver* solver_shadow)
    : Solver(sng),
      d_solver(solver),
      d_solver_shadow(solver_shadow),
      d_same_solver(solver->get_name() == solver_shadow->get_name()){};

ShadowSolver::~ShadowSolver(){};

void
ShadowSolver::get_sorts_helper(const std::vector<Sort>& sorts,
                               std::vector<Sort>& sorts_orig,
                               std::vector<Sort>& sorts_shadow)
{
  for (auto s : sorts)
  {
    ShadowSort* sort = dynamic_cast<ShadowSort*>(s.get());
    assert(sort);
    sorts_orig.push_back(sort->get_sort());
    sorts_shadow.push_back(sort->get_sort_shadow());
  }
}

void
ShadowSolver::get_terms_helper(const std::vector<Term>& terms,
                               std::vector<Term>& terms_orig,
                               std::vector<Term>& terms_shadow)
{
  for (auto t : terms)
  {
    ShadowTerm* term = dynamic_cast<ShadowTerm*>(t.get());
    assert(term);
    terms_orig.push_back(term->get_term());
    terms_shadow.push_back(term->get_term_shadow());
  }
}

void
ShadowSolver::new_solver()
{
  d_solver->new_solver();
  d_solver_shadow->new_solver();
}

void
ShadowSolver::delete_solver()
{
  d_solver->delete_solver();
  d_solver_shadow->delete_solver();
  d_solver.reset(nullptr);
  d_solver_shadow.reset(nullptr);
}

bool
ShadowSolver::is_initialized() const
{
  bool res = d_solver->is_initialized();
  assert(d_solver_shadow->is_initialized() == res);
  return res;
}

const std::string
ShadowSolver::get_name() const
{
  return "ShadowSolver(" + d_solver->get_name() + ","
         + d_solver_shadow->get_name() + ")";
}

/** Return intersection of supported theories. */
TheoryIdVector
ShadowSolver::get_supported_theories() const
{
  TheoryIdVector supported;

  auto supported_orig = d_solver->get_supported_theories();
  auto supported_shadow  = d_solver_shadow->get_supported_theories();

  /* Return intersection of supported theories. */
  for (auto theory : supported_orig)
  {
    if (std::find(supported_shadow.begin(), supported_shadow.end(), theory)
        != supported_shadow.end())
    {
      supported.push_back(theory);
    }
  }

  return supported;
}

/** Return union of unsupported theories. */
TheoryIdVector
ShadowSolver::get_unsupported_quant_theories() const
{
  TheoryIdVector unsupported;
  auto unsupported_orig = d_solver->get_unsupported_quant_theories();
  auto unsupported_shadow  = d_solver_shadow->get_unsupported_quant_theories();
  unsupported.insert(
      unsupported.end(), unsupported_orig.begin(), unsupported_orig.end());
  unsupported.insert(
      unsupported.end(), unsupported_shadow.begin(), unsupported_shadow.end());
  return unsupported;
}

/** Return union of unsupported operators kinds. */
OpKindSet
ShadowSolver::get_unsupported_op_kinds() const
{
  OpKindSet unsupported;
  auto unsupported_orig = d_solver->get_unsupported_op_kinds();
  auto unsupported_shadow  = d_solver_shadow->get_unsupported_op_kinds();
  unsupported.insert(unsupported_orig.begin(), unsupported_orig.end());
  unsupported.insert(unsupported_shadow.begin(), unsupported_shadow.end());
  return unsupported;
}

Solver::OpKindSortKindMap
ShadowSolver::get_unsupported_op_sort_kinds() const
{
  OpKindSortKindMap unsupported;
  auto unsupported_orig   = d_solver->get_unsupported_op_sort_kinds();
  auto unsupported_shadow = d_solver_shadow->get_unsupported_op_sort_kinds();
  unsupported.insert(unsupported_orig.begin(), unsupported_orig.end());
  unsupported.insert(unsupported_shadow.begin(), unsupported_shadow.end());
  return unsupported;
}

SortKindSet
ShadowSolver::get_unsupported_var_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_orig = d_solver->get_unsupported_var_sort_kinds();
  auto unsupported_shadow  = d_solver_shadow->get_unsupported_var_sort_kinds();
  unsupported.insert(unsupported_orig.begin(), unsupported_orig.end());
  unsupported.insert(unsupported_shadow.begin(), unsupported_shadow.end());
  return unsupported;
}

SortKindSet
ShadowSolver::get_unsupported_fun_domain_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_orig = d_solver->get_unsupported_fun_domain_sort_kinds();
  auto unsupported_shadow =
      d_solver_shadow->get_unsupported_fun_domain_sort_kinds();
  unsupported.insert(unsupported_orig.begin(), unsupported_orig.end());
  unsupported.insert(unsupported_shadow.begin(), unsupported_shadow.end());
  return unsupported;
}

SortKindSet
ShadowSolver::get_unsupported_fun_codomain_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_orig = d_solver->get_unsupported_fun_codomain_sort_kinds();
  auto unsupported_shadow =
      d_solver_shadow->get_unsupported_fun_codomain_sort_kinds();
  unsupported.insert(unsupported_orig.begin(), unsupported_orig.end());
  unsupported.insert(unsupported_shadow.begin(), unsupported_shadow.end());
  return unsupported;
}

SortKindSet
ShadowSolver::get_unsupported_array_index_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_orig = d_solver->get_unsupported_array_index_sort_kinds();
  auto unsupported_shadow =
      d_solver_shadow->get_unsupported_array_index_sort_kinds();
  unsupported.insert(unsupported_orig.begin(), unsupported_orig.end());
  unsupported.insert(unsupported_shadow.begin(), unsupported_shadow.end());
  return unsupported;
}

SortKindSet
ShadowSolver::get_unsupported_array_element_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_orig = d_solver->get_unsupported_array_element_sort_kinds();
  auto unsupported_shadow =
      d_solver_shadow->get_unsupported_array_element_sort_kinds();
  unsupported.insert(unsupported_orig.begin(), unsupported_orig.end());
  unsupported.insert(unsupported_shadow.begin(), unsupported_shadow.end());
  return unsupported;
}

SortKindSet
ShadowSolver::get_unsupported_seq_element_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_orig = d_solver->get_unsupported_seq_element_sort_kinds();
  auto unsupported_shadow =
      d_solver_shadow->get_unsupported_seq_element_sort_kinds();
  unsupported.insert(unsupported_orig.begin(), unsupported_orig.end());
  unsupported.insert(unsupported_shadow.begin(), unsupported_shadow.end());
  return unsupported;
}

SortKindSet
ShadowSolver::get_unsupported_set_element_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_orig = d_solver->get_unsupported_set_element_sort_kinds();
  auto unsupported_shadow =
      d_solver_shadow->get_unsupported_set_element_sort_kinds();
  unsupported.insert(unsupported_orig.begin(), unsupported_orig.end());
  unsupported.insert(unsupported_shadow.begin(), unsupported_shadow.end());
  return unsupported;
}

Term
ShadowSolver::mk_var(Sort sort, const std::string& name)
{
  ShadowSort* s = dynamic_cast<ShadowSort*>(sort.get());
  assert(s);
  Term t        = d_solver->mk_var(s->d_sort, name);
  Term t_shadow = d_solver_shadow->mk_var(s->d_sort_shadow, name);
  std::shared_ptr<ShadowTerm> res(new ShadowTerm(t, t_shadow));
  return res;
}

Term
ShadowSolver::mk_const(Sort sort, const std::string& name)
{
  ShadowSort* s = dynamic_cast<ShadowSort*>(sort.get());
  assert(s);
  Term t        = d_solver->mk_const(s->d_sort, name);
  Term t_shadow = d_solver_shadow->mk_const(s->d_sort_shadow, name);
  std::shared_ptr<ShadowTerm> res(new ShadowTerm(t, t_shadow));
  return res;
}

Term
ShadowSolver::mk_fun(Sort sort, const std::string& name)
{
  ShadowSort* s = dynamic_cast<ShadowSort*>(sort.get());
  assert(s);
  Term t        = d_solver->mk_fun(s->d_sort, name);
  Term t_shadow = d_solver_shadow->mk_fun(s->d_sort_shadow, name);
  std::shared_ptr<ShadowTerm> res(new ShadowTerm(t, t_shadow));
  return res;
}

Term
ShadowSolver::mk_value(Sort sort, bool value)
{
  ShadowSort* s = dynamic_cast<ShadowSort*>(sort.get());
  assert(s);
  Term t        = d_solver->mk_value(s->d_sort, value);
  Term t_shadow = d_solver_shadow->mk_value(s->d_sort_shadow, value);
  std::shared_ptr<ShadowTerm> res(new ShadowTerm(t, t_shadow));
  return res;
}

Term
ShadowSolver::mk_value(Sort sort, std::string value)
{
  ShadowSort* s = dynamic_cast<ShadowSort*>(sort.get());
  assert(s);
  Term t        = d_solver->mk_value(s->d_sort, value);
  Term t_shadow = d_solver_shadow->mk_value(s->d_sort_shadow, value);
  std::shared_ptr<ShadowTerm> res(new ShadowTerm(t, t_shadow));
  return res;
}

Term
ShadowSolver::mk_value(Sort sort, std::string num, std::string den)
{
  ShadowSort* s = dynamic_cast<ShadowSort*>(sort.get());
  assert(s);
  Term t        = d_solver->mk_value(s->d_sort, num, den);
  Term t_shadow = d_solver_shadow->mk_value(s->d_sort_shadow, num, den);
  std::shared_ptr<ShadowTerm> res(new ShadowTerm(t, t_shadow));
  return res;
}

Term
ShadowSolver::mk_value(Sort sort, std::string value, Base base)
{
  ShadowSort* s = dynamic_cast<ShadowSort*>(sort.get());
  assert(s);
  Term t        = d_solver->mk_value(s->d_sort, value, base);
  Term t_shadow = d_solver_shadow->mk_value(s->d_sort_shadow, value, base);
  std::shared_ptr<ShadowTerm> res(new ShadowTerm(t, t_shadow));
  return res;
}

Term
ShadowSolver::mk_special_value(Sort sort,
                               const AbsTerm::SpecialValueKind& value)
{
  ShadowSort* s = dynamic_cast<ShadowSort*>(sort.get());
  assert(s);
  Term t        = d_solver->mk_special_value(s->d_sort, value);
  Term t_shadow = d_solver_shadow->mk_special_value(s->d_sort_shadow, value);
  std::shared_ptr<ShadowTerm> res(new ShadowTerm(t, t_shadow));
  return res;
}

Sort
ShadowSolver::mk_sort(const std::string name, uint32_t arity)
{
  Sort s        = d_solver->mk_sort(name, arity);
  Sort s_shadow = d_solver_shadow->mk_sort(name, arity);
  std::shared_ptr<ShadowSort> res(new ShadowSort(s, s_shadow));
  return res;
}

Sort
ShadowSolver::mk_sort(SortKind kind)
{
  Sort s        = d_solver->mk_sort(kind);
  Sort s_shadow = d_solver_shadow->mk_sort(kind);
  std::shared_ptr<ShadowSort> res(new ShadowSort(s, s_shadow));
  return res;
}

Sort
ShadowSolver::mk_sort(SortKind kind, uint32_t size)
{
  Sort s        = d_solver->mk_sort(kind, size);
  Sort s_shadow = d_solver_shadow->mk_sort(kind, size);
  std::shared_ptr<ShadowSort> res(new ShadowSort(s, s_shadow));
  return res;
}

Sort
ShadowSolver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  Sort s        = d_solver->mk_sort(kind, esize, ssize);
  Sort s_shadow = d_solver_shadow->mk_sort(kind, esize, ssize);
  std::shared_ptr<ShadowSort> res(new ShadowSort(s, s_shadow));
  return res;
}

Sort
ShadowSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  std::vector<Sort> sorts_orig, sorts_shadow;
  get_sorts_helper(sorts, sorts_orig, sorts_shadow);
  Sort s        = d_solver->mk_sort(kind, sorts_orig);
  Sort s_shadow = d_solver_shadow->mk_sort(kind, sorts_shadow);
  std::shared_ptr<ShadowSort> res(new ShadowSort(s, s_shadow));
  return res;
}

Term
ShadowSolver::mk_term(const Op::Kind& kind,
                      const std::vector<Term>& args,
                      const std::vector<uint32_t>& params)
{
  std::vector<Term> terms_orig, terms_shadow;
  get_terms_helper(args, terms_orig, terms_shadow);
  Term t        = d_solver->mk_term(kind, terms_orig, params);
  Term t_shadow = d_solver_shadow->mk_term(kind, terms_shadow, params);
  std::shared_ptr<ShadowTerm> res(new ShadowTerm(t, t_shadow));
  return res;
}

Sort
ShadowSolver::get_sort(Term term, SortKind sort_kind) const
{
  ShadowTerm* t = dynamic_cast<ShadowTerm*>(term.get());
  assert(t);
  Sort s        = d_solver->get_sort(t->get_term(), sort_kind);
  Sort s_shadow = d_solver_shadow->get_sort(t->get_term_shadow(), sort_kind);
  std::shared_ptr<ShadowSort> res(new ShadowSort(s, s_shadow));
  return res;
}

std::string
ShadowSolver::get_option_name_incremental() const
{
  return d_solver->get_option_name_incremental();
}

std::string
ShadowSolver::get_option_name_model_gen() const
{
  return d_solver->get_option_name_model_gen();
}

std::string
ShadowSolver::get_option_name_unsat_assumptions() const
{
  return d_solver->get_option_name_unsat_assumptions();
}

std::string
ShadowSolver::get_option_name_unsat_cores() const
{
  return d_solver->get_option_name_unsat_cores();
}

bool
ShadowSolver::option_incremental_enabled() const
{
  return d_solver->option_incremental_enabled()
         && d_solver_shadow->option_incremental_enabled();
}

bool
ShadowSolver::option_model_gen_enabled() const
{
  return d_solver->option_model_gen_enabled()
         && d_solver_shadow->option_model_gen_enabled();
}

bool
ShadowSolver::option_unsat_assumptions_enabled() const
{
  return d_solver->option_unsat_assumptions_enabled()
         && d_solver_shadow->option_unsat_assumptions_enabled();
}

bool
ShadowSolver::option_unsat_cores_enabled() const
{
  return d_solver->option_unsat_cores_enabled()
         && d_solver_shadow->option_unsat_cores_enabled();
}

bool
ShadowSolver::is_unsat_assumption(const Term& t) const
{
  ShadowTerm* term = dynamic_cast<ShadowTerm*>(t.get());
  assert(term);
  bool res = d_solver->is_unsat_assumption(term->get_term());
  if (d_same_solver)
  {
    assert(res
           == d_solver_shadow->is_unsat_assumption(term->get_term_shadow()));
  }
  return res;
}

void
ShadowSolver::assert_formula(const Term& t)
{
  ShadowTerm* term = dynamic_cast<ShadowTerm*>(t.get());
  assert(term);
  d_solver->assert_formula(term->get_term());
  d_solver_shadow->assert_formula(term->get_term_shadow());
}

Solver::Result
ShadowSolver::check_sat()
{
  Result res_orig = d_solver->check_sat();
  Result res_shadow  = d_solver_shadow->check_sat();
  assert(res_orig == res_shadow);
  return res_orig;
}

Solver::Result
ShadowSolver::check_sat_assuming(std::vector<Term>& assumptions)
{
  std::vector<Term> assumptions_orig, assumptions_shadow;
  get_terms_helper(assumptions, assumptions_orig, assumptions_shadow);
  Result res_orig = d_solver->check_sat_assuming(assumptions_orig);
  Result res_shadow  = d_solver_shadow->check_sat_assuming(assumptions_shadow);
  assert(res_orig == res_shadow);
  return res_orig;
}

std::vector<Term>
ShadowSolver::get_unsat_assumptions()
{
  assert(d_same_solver);
  std::vector<Term> res, terms, terms_shadow;
  auto ua_orig   = d_solver->get_unsat_assumptions();
  auto ua_shadow = d_solver_shadow->get_unsat_assumptions();
  assert(ua_orig.size() == ua_shadow.size());
  for (size_t i = 0; i < ua_orig.size(); ++i)
  {
    res.emplace_back(new ShadowTerm(ua_orig[i], ua_shadow[i]));
  }
  return res;
}

std::vector<Term>
ShadowSolver::get_unsat_core()
{
  assert(d_same_solver);
  std::vector<Term> res, terms, terms_shadow;
  auto uc_orig   = d_solver->get_unsat_core();
  auto uc_shadow = d_solver_shadow->get_unsat_core();
  assert(uc_orig.size() == uc_shadow.size());
  for (size_t i = 0; i < uc_orig.size(); ++i)
  {
    res.emplace_back(new ShadowTerm(uc_orig[i], uc_shadow[i]));
  }
  return res;
}

void
ShadowSolver::push(uint32_t n_levels)
{
  d_solver->push(n_levels);
  d_solver_shadow->push(n_levels);
}

void
ShadowSolver::pop(uint32_t n_levels)
{
  d_solver->pop(n_levels);
  d_solver_shadow->pop(n_levels);
}

void
ShadowSolver::print_model()
{
  d_solver->print_model();
  d_solver_shadow->print_model();
}

void
ShadowSolver::reset()
{
  d_solver->reset();
  d_solver_shadow->reset();
}

void
ShadowSolver::reset_assertions()
{
  d_solver->reset_assertions();
  d_solver_shadow->reset_assertions();
}

void
ShadowSolver::set_opt(const std::string& opt, const std::string& value)
{
  d_solver->set_opt(opt, value);
  if (opt == d_solver->get_option_name_incremental())
  {
    d_solver_shadow->set_opt(d_solver_shadow->get_option_name_incremental(),
                             value);
  }
  else if (opt == d_solver->get_option_name_model_gen())
  {
    d_solver_shadow->set_opt(d_solver_shadow->get_option_name_model_gen(),
                             value);
  }
  else if (opt == d_solver->get_option_name_unsat_assumptions())
  {
    d_solver_shadow->set_opt(
        d_solver_shadow->get_option_name_unsat_assumptions(), value);
  }
}

std::vector<Term>
ShadowSolver::get_value(std::vector<Term>& terms)
{
  assert(d_same_solver);
  std::vector<Term> res, terms_orig, terms_shadow;
  get_terms_helper(terms, terms_orig, terms_shadow);
  auto values_orig   = d_solver->get_value(terms_orig);
  auto values_shadow = d_solver_shadow->get_value(terms_shadow);
  assert(values_orig.size() == values_shadow.size());
  for (size_t i = 0; i < values_orig.size(); ++i)
  {
    res.emplace_back(new ShadowTerm(values_orig[i], values_shadow[i]));
  }
  return res;
}

void
ShadowSolver::disable_unsupported_actions(FSM* fsm) const
{
  d_solver->disable_unsupported_actions(fsm);
  d_solver_shadow->disable_unsupported_actions(fsm);

  if (!d_same_solver)
  {
    fsm->disable_action(Action::GET_VALUE);
    fsm->disable_action(Action::GET_UNSAT_CORE);
    fsm->disable_action(Action::GET_UNSAT_ASSUMPTIONS);
  }
}

}  // namespace shadow
}  // namespace murxla
