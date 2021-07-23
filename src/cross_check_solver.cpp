
#include "cross_check_solver.hpp"

namespace murxla {
namespace cross_check {

namespace {

void
get_sorts_helper(const std::vector<Sort>& sorts,
                 std::vector<Sort>& sorts_test,
                 std::vector<Sort>& sorts_ref)
{
  for (auto s : sorts)
  {
    CrossCheckSort* sort = dynamic_cast<CrossCheckSort*>(s.get());
    assert(sort);
    sorts_test.push_back(sort->get_sort_test());
    sorts_ref.push_back(sort->get_sort_ref());
  }
}

void
get_terms_helper(const std::vector<Term>& terms,
                 std::vector<Term>& terms_test,
                 std::vector<Term>& terms_ref)
{
  for (auto t : terms)
  {
    CrossCheckTerm* term = dynamic_cast<CrossCheckTerm*>(t.get());
    assert(term);
    terms_test.push_back(term->get_term_test());
    terms_ref.push_back(term->get_term_ref());
  }
}

}  // namespace

CrossCheckSort::CrossCheckSort(Sort sort_test, Sort sort_ref)
    : d_sort_test(sort_test), d_sort_ref(sort_ref)
{
}
CrossCheckSort::~CrossCheckSort() {}

size_t
CrossCheckSort::hash() const
{
  return d_sort_test->hash();
}
bool
CrossCheckSort::equals(const Sort& other) const
{
  CrossCheckSort* cc_sort = dynamic_cast<CrossCheckSort*>(other.get());
  return d_sort_test == cc_sort->d_sort_test;
}
std::string
CrossCheckSort::to_string() const
{
  return d_sort_test->to_string();
}
bool
CrossCheckSort::is_array() const
{
  return d_sort_test->is_array();
}
bool
CrossCheckSort::is_bool() const
{
  return d_sort_test->is_bool();
}
bool
CrossCheckSort::is_bv() const
{
  return d_sort_test->is_bv();
}
bool
CrossCheckSort::is_fp() const
{
  return d_sort_test->is_fp();
}
bool
CrossCheckSort::is_fun() const
{
  return d_sort_test->is_fun();
}
bool
CrossCheckSort::is_int() const
{
  return d_sort_test->is_int();
}
bool
CrossCheckSort::is_real() const
{
  return d_sort_test->is_real();
}
bool
CrossCheckSort::is_rm() const
{
  return d_sort_test->is_rm();
}
bool
CrossCheckSort::is_string() const
{
  return d_sort_test->is_string();
}
bool
CrossCheckSort::is_reglan() const
{
  return d_sort_test->is_reglan();
}
uint32_t
CrossCheckSort::get_bv_size() const
{
  return d_sort_test->get_bv_size();
}
uint32_t
CrossCheckSort::get_fp_exp_size() const
{
  return d_sort_test->get_fp_exp_size();
}
uint32_t
CrossCheckSort::get_fp_sig_size() const
{
  return d_sort_test->get_fp_sig_size();
}
void
CrossCheckSort::set_kind(SortKind sort_kind)
{
  d_sort_test->set_kind(sort_kind);
  d_sort_ref->set_kind(sort_kind);
  d_kind = sort_kind;
}

void
CrossCheckSort::set_sorts(const std::vector<Sort>& sorts)
{
  std::vector<Sort> sorts_test, sorts_ref;
  get_sorts_helper(sorts, sorts_test, sorts_ref);
  d_sort_test->set_sorts(sorts_test);
  d_sort_ref->set_sorts(sorts_ref);
  d_sorts = sorts;
}

Sort
CrossCheckSort::get_sort_test() const
{
  return d_sort_test;
}

Sort
CrossCheckSort::get_sort_ref() const
{
  return d_sort_ref;
}

CrossCheckTerm::CrossCheckTerm(Term term_test, Term term_ref)
    : d_term_test(term_test), d_term_ref(term_ref){};
CrossCheckTerm::~CrossCheckTerm() {}
size_t
CrossCheckTerm::hash() const
{
  return d_term_test->hash();
}
bool
CrossCheckTerm::equals(const Term& other) const
{
  CrossCheckTerm* cc_term = dynamic_cast<CrossCheckTerm*>(other.get());
  return d_term_test == cc_term->d_term_test;
}
std::string
CrossCheckTerm::to_string() const
{
  return d_term_test->to_string();
}
bool
CrossCheckTerm::is_array() const
{
  return d_term_test->is_array();
}
bool
CrossCheckTerm::is_bool() const
{
  return d_term_test->is_bool();
}
bool
CrossCheckTerm::is_bv() const
{
  return d_term_test->is_bv();
}
bool
CrossCheckTerm::is_fp() const
{
  return d_term_test->is_fp();
}
bool
CrossCheckTerm::is_fun() const
{
  return d_term_test->is_fun();
}
bool
CrossCheckTerm::is_int() const
{
  return d_term_test->is_int();
}
bool
CrossCheckTerm::is_real() const
{
  return d_term_test->is_real();
}
bool
CrossCheckTerm::is_rm() const
{
  return d_term_test->is_rm();
}
bool
CrossCheckTerm::is_string() const
{
  return d_term_test->is_string();
}
bool
CrossCheckTerm::is_reglan() const
{
  return d_term_test->is_reglan();
}

void
CrossCheckTerm::set_sort(Sort sort)
{
  CrossCheckSort* s = dynamic_cast<CrossCheckSort*>(sort.get());
  d_term_test->set_sort(s->get_sort_test());
  d_term_ref->set_sort(s->get_sort_ref());
  d_sort = sort;
}

Term
CrossCheckTerm::get_term_test() const
{
  return d_term_test;
}

Term
CrossCheckTerm::get_term_ref() const
{
  return d_term_ref;
}

CrossCheckSolver::CrossCheckSolver(RNGenerator& rng,
                                   Solver* test_solver,
                                   Solver* reference_solver)
    : Solver(rng),
      d_test_solver(test_solver),
      d_reference_solver(reference_solver){};

CrossCheckSolver::~CrossCheckSolver(){};

void
CrossCheckSolver::new_solver()
{
  d_test_solver->new_solver();
  d_reference_solver->new_solver();
}

void
CrossCheckSolver::delete_solver()
{
  d_test_solver->delete_solver();
  d_reference_solver->delete_solver();
  d_test_solver.reset(nullptr);
  d_reference_solver.reset(nullptr);
}

bool
CrossCheckSolver::is_initialized() const
{
  bool res = d_test_solver->is_initialized();
  assert(d_reference_solver->is_initialized() == res);
  return res;
}

/** Return intersection of supported theories. */
TheoryIdVector
CrossCheckSolver::get_supported_theories() const
{
  TheoryIdVector supported;

  auto supported_test = d_test_solver->get_supported_theories();
  auto supported_ref  = d_reference_solver->get_supported_theories();

  /* Return intersection of supported theories. */
  for (auto theory : supported_test)
  {
    if (std::find(supported_ref.begin(), supported_ref.end(), theory)
        != supported_ref.end())
    {
      supported.push_back(theory);
    }
  }

  return supported;
}

/** Return union of unsupported theories. */
TheoryIdVector
CrossCheckSolver::get_unsupported_quant_theories() const
{
  TheoryIdVector unsupported;
  auto unsupported_test = d_test_solver->get_unsupported_quant_theories();
  auto unsupported_ref  = d_reference_solver->get_unsupported_quant_theories();
  unsupported.insert(
      unsupported.end(), unsupported_test.begin(), unsupported_test.end());
  unsupported.insert(
      unsupported.end(), unsupported_ref.begin(), unsupported_ref.end());
  return unsupported;
}

/** Return union of unsupported operators kinds. */
OpKindSet
CrossCheckSolver::get_unsupported_op_kinds() const
{
  OpKindSet unsupported;
  auto unsupported_test = d_test_solver->get_unsupported_op_kinds();
  auto unsupported_ref  = d_reference_solver->get_unsupported_op_kinds();
  unsupported.insert(unsupported_test.begin(), unsupported_test.end());
  unsupported.insert(unsupported_ref.begin(), unsupported_ref.end());
  return unsupported;
}

SortKindSet
CrossCheckSolver::get_unsupported_var_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_test = d_test_solver->get_unsupported_var_sort_kinds();
  auto unsupported_ref  = d_reference_solver->get_unsupported_var_sort_kinds();
  unsupported.insert(unsupported_test.begin(), unsupported_test.end());
  unsupported.insert(unsupported_ref.begin(), unsupported_ref.end());
  return unsupported;
}

SortKindSet
CrossCheckSolver::get_unsupported_fun_domain_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_test =
      d_test_solver->get_unsupported_fun_domain_sort_kinds();
  auto unsupported_ref =
      d_reference_solver->get_unsupported_fun_domain_sort_kinds();
  unsupported.insert(unsupported_test.begin(), unsupported_test.end());
  unsupported.insert(unsupported_ref.begin(), unsupported_ref.end());
  return unsupported;
}

SortKindSet
CrossCheckSolver::get_unsupported_array_index_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_test =
      d_test_solver->get_unsupported_array_index_sort_kinds();
  auto unsupported_ref =
      d_reference_solver->get_unsupported_array_index_sort_kinds();
  unsupported.insert(unsupported_test.begin(), unsupported_test.end());
  unsupported.insert(unsupported_ref.begin(), unsupported_ref.end());
  return unsupported;
}

SortKindSet
CrossCheckSolver::get_unsupported_array_element_sort_kinds() const
{
  SortKindSet unsupported;
  auto unsupported_test =
      d_test_solver->get_unsupported_array_element_sort_kinds();
  auto unsupported_ref =
      d_reference_solver->get_unsupported_array_element_sort_kinds();
  unsupported.insert(unsupported_test.begin(), unsupported_test.end());
  unsupported.insert(unsupported_ref.begin(), unsupported_ref.end());
  return unsupported;
}

Term
CrossCheckSolver::mk_var(Sort sort, const std::string& name)
{
  CrossCheckSort* s = dynamic_cast<CrossCheckSort*>(sort.get());
  assert(s);
  Term t_test = d_test_solver->mk_var(s->get_sort_test(), name);
  Term t_ref  = d_reference_solver->mk_var(s->get_sort_ref(), name);
  std::shared_ptr<CrossCheckTerm> res(new CrossCheckTerm(t_test, t_ref));
  return res;
}

Term
CrossCheckSolver::mk_const(Sort sort, const std::string& name)
{
  CrossCheckSort* s = dynamic_cast<CrossCheckSort*>(sort.get());
  assert(s);
  Term t_test = d_test_solver->mk_const(s->get_sort_test(), name);
  Term t_ref  = d_reference_solver->mk_const(s->get_sort_ref(), name);
  std::shared_ptr<CrossCheckTerm> res(new CrossCheckTerm(t_test, t_ref));
  return res;
}

Term
CrossCheckSolver::mk_fun(Sort sort, const std::string& name)
{
  CrossCheckSort* s = dynamic_cast<CrossCheckSort*>(sort.get());
  assert(s);
  Term t_test = d_test_solver->mk_fun(s->get_sort_test(), name);
  Term t_ref  = d_reference_solver->mk_fun(s->get_sort_ref(), name);
  std::shared_ptr<CrossCheckTerm> res(new CrossCheckTerm(t_test, t_ref));
  return res;
}

Term
CrossCheckSolver::mk_value(Sort sort, bool value)
{
  CrossCheckSort* s = dynamic_cast<CrossCheckSort*>(sort.get());
  assert(s);
  Term t_test = d_test_solver->mk_value(s->get_sort_test(), value);
  Term t_ref  = d_reference_solver->mk_value(s->get_sort_ref(), value);
  std::shared_ptr<CrossCheckTerm> res(new CrossCheckTerm(t_test, t_ref));
  return res;
}

Term
CrossCheckSolver::mk_value(Sort sort, std::string value)
{
  CrossCheckSort* s = dynamic_cast<CrossCheckSort*>(sort.get());
  assert(s);
  Term t_test = d_test_solver->mk_value(s->get_sort_test(), value);
  Term t_ref  = d_reference_solver->mk_value(s->get_sort_ref(), value);
  std::shared_ptr<CrossCheckTerm> res(new CrossCheckTerm(t_test, t_ref));
  return res;
}

Term
CrossCheckSolver::mk_value(Sort sort, std::string num, std::string den)
{
  CrossCheckSort* s = dynamic_cast<CrossCheckSort*>(sort.get());
  assert(s);
  Term t_test = d_test_solver->mk_value(s->get_sort_test(), num, den);
  Term t_ref  = d_reference_solver->mk_value(s->get_sort_ref(), num, den);
  std::shared_ptr<CrossCheckTerm> res(new CrossCheckTerm(t_test, t_ref));
  return res;
}

Term
CrossCheckSolver::mk_value(Sort sort, std::string value, Base base)
{
  CrossCheckSort* s = dynamic_cast<CrossCheckSort*>(sort.get());
  assert(s);
  Term t_test = d_test_solver->mk_value(s->get_sort_test(), value, base);
  Term t_ref  = d_reference_solver->mk_value(s->get_sort_ref(), value, base);
  std::shared_ptr<CrossCheckTerm> res(new CrossCheckTerm(t_test, t_ref));
  return res;
}

Term
CrossCheckSolver::mk_special_value(Sort sort, const SpecialValueKind& value)
{
  CrossCheckSort* s = dynamic_cast<CrossCheckSort*>(sort.get());
  assert(s);
  Term t_test = d_test_solver->mk_special_value(s->get_sort_test(), value);
  Term t_ref  = d_reference_solver->mk_special_value(s->get_sort_ref(), value);
  std::shared_ptr<CrossCheckTerm> res(new CrossCheckTerm(t_test, t_ref));
  return res;
}

Sort
CrossCheckSolver::mk_sort(const std::string name, uint32_t arity)
{
  Sort s_test = d_test_solver->mk_sort(name, arity);
  Sort s_ref  = d_reference_solver->mk_sort(name, arity);
  std::shared_ptr<CrossCheckSort> res(new CrossCheckSort(s_test, s_ref));
  return res;
}

Sort
CrossCheckSolver::mk_sort(SortKind kind)
{
  Sort s_test = d_test_solver->mk_sort(kind);
  Sort s_ref  = d_reference_solver->mk_sort(kind);
  std::shared_ptr<CrossCheckSort> res(new CrossCheckSort(s_test, s_ref));
  return res;
}

Sort
CrossCheckSolver::mk_sort(SortKind kind, uint32_t size)
{
  Sort s_test = d_test_solver->mk_sort(kind, size);
  Sort s_ref  = d_reference_solver->mk_sort(kind, size);
  std::shared_ptr<CrossCheckSort> res(new CrossCheckSort(s_test, s_ref));
  return res;
}

Sort
CrossCheckSolver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  Sort s_test = d_test_solver->mk_sort(kind, esize, ssize);
  Sort s_ref  = d_reference_solver->mk_sort(kind, esize, ssize);
  std::shared_ptr<CrossCheckSort> res(new CrossCheckSort(s_test, s_ref));
  return res;
}

Sort
CrossCheckSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  std::vector<Sort> sorts_test, sorts_ref;
  get_sorts_helper(sorts, sorts_test, sorts_ref);
  Sort s_test = d_test_solver->mk_sort(kind, sorts_test);
  Sort s_ref  = d_reference_solver->mk_sort(kind, sorts_ref);
  std::shared_ptr<CrossCheckSort> res(new CrossCheckSort(s_test, s_ref));
  return res;
}

Term
CrossCheckSolver::mk_term(const Op::Kind& kind,
                          std::vector<Term>& args,
                          std::vector<uint32_t>& params)
{
  std::vector<Term> terms_test, terms_ref;
  get_terms_helper(args, terms_test, terms_ref);
  Term t_test = d_test_solver->mk_term(kind, terms_test, params);
  Term t_ref  = d_reference_solver->mk_term(kind, terms_ref, params);
  std::shared_ptr<CrossCheckTerm> res(new CrossCheckTerm(t_test, t_ref));
  return res;
}

Sort
CrossCheckSolver::get_sort(Term term, SortKind sort_kind) const
{
  CrossCheckTerm* t = dynamic_cast<CrossCheckTerm*>(term.get());
  assert(t);
  Sort s_test = d_test_solver->get_sort(t->get_term_test(), sort_kind);
  Sort s_ref  = d_reference_solver->get_sort(t->get_term_ref(), sort_kind);
  std::shared_ptr<CrossCheckSort> res(new CrossCheckSort(s_test, s_ref));
  return res;
}

std::string
CrossCheckSolver::get_option_name_incremental() const
{
  return d_test_solver->get_option_name_incremental();
}

std::string
CrossCheckSolver::get_option_name_model_gen() const
{
  return d_test_solver->get_option_name_model_gen();
}

std::string
CrossCheckSolver::get_option_name_unsat_assumptions() const
{
  return d_test_solver->get_option_name_unsat_assumptions();
}

bool
CrossCheckSolver::option_incremental_enabled() const
{
  return d_test_solver->option_incremental_enabled()
         && d_reference_solver->option_incremental_enabled();
}

bool
CrossCheckSolver::option_model_gen_enabled() const
{
  return d_test_solver->option_model_gen_enabled()
         && d_reference_solver->option_model_gen_enabled();
}

bool
CrossCheckSolver::option_unsat_assumptions_enabled() const
{
  return d_test_solver->option_unsat_assumptions_enabled()
         && d_reference_solver->option_unsat_assumptions_enabled();
}

bool
CrossCheckSolver::check_unsat_assumption(const Term& t) const
{
  CrossCheckTerm* term = dynamic_cast<CrossCheckTerm*>(t.get());
  assert(term);
  // TODO: asking d_reference_solver probably doesn't make sense
  return d_test_solver->check_unsat_assumption(term->get_term_test());
}

void
CrossCheckSolver::assert_formula(const Term& t)
{
  CrossCheckTerm* term = dynamic_cast<CrossCheckTerm*>(t.get());
  assert(term);
  d_test_solver->assert_formula(term->get_term_test());
  d_reference_solver->assert_formula(term->get_term_ref());
}

Solver::Result
CrossCheckSolver::check_sat()
{
  Result res_test = d_test_solver->check_sat();
  Result res_ref  = d_reference_solver->check_sat();
  assert(res_test == res_ref);
  return res_test;
}

Solver::Result
CrossCheckSolver::check_sat_assuming(std::vector<Term>& assumptions)
{
  std::vector<Term> assumptions_test, assumptions_ref;
  get_terms_helper(assumptions, assumptions_test, assumptions_ref);
  Result res_test = d_test_solver->check_sat_assuming(assumptions_test);
  Result res_ref  = d_reference_solver->check_sat_assuming(assumptions_ref);
  assert(res_test == res_ref);
  return res_test;
}

std::vector<Term>
CrossCheckSolver::get_unsat_assumptions()
{
  return std::vector<Term>();
}

void
CrossCheckSolver::push(uint32_t n_levels)
{
  d_test_solver->push(n_levels);
  d_reference_solver->push(n_levels);
}

void
CrossCheckSolver::pop(uint32_t n_levels)
{
  d_test_solver->pop(n_levels);
  d_reference_solver->pop(n_levels);
}

void
CrossCheckSolver::print_model()
{
  d_test_solver->print_model();
  d_reference_solver->print_model();
}

void
CrossCheckSolver::reset_assertions()
{
  d_test_solver->reset_assertions();
  d_reference_solver->reset_assertions();
}

void
CrossCheckSolver::set_opt(const std::string& opt, const std::string& value)
{
  d_test_solver->set_opt(opt, value);
  if (opt == d_test_solver->get_option_name_incremental())
  {
    d_reference_solver->set_opt(
        d_reference_solver->get_option_name_incremental(), value);
  }
  else if (opt == d_test_solver->get_option_name_model_gen())
  {
    d_reference_solver->set_opt(d_reference_solver->get_option_name_model_gen(),
                                value);
  }
  else if (opt == d_test_solver->get_option_name_unsat_assumptions())
  {
    d_reference_solver->set_opt(
        d_reference_solver->get_option_name_unsat_assumptions(), value);
  }
}

std::vector<Term>
CrossCheckSolver::get_value(std::vector<Term>& terms)
{
  return std::vector<Term>();
}

void
CrossCheckSolver::configure_fsm(FSM* fsm) const
{
  fsm->disable_action(Action::GET_VALUE);
}

Sort
CrossCheckSolver::get_sort_test(Sort s) const
{
  CrossCheckSort* sort = dynamic_cast<CrossCheckSort*>(s.get());
  return sort->get_sort_test();
}

Sort
CrossCheckSolver::get_sort_ref(Sort s) const
{
  CrossCheckSort* sort = dynamic_cast<CrossCheckSort*>(s.get());
  return sort->get_sort_ref();
}

}  // namespace cross_check
}  // namespace murxla
