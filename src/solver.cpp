#include "solver.hpp"

#include <algorithm>

#include "theory.hpp"

/* -------------------------------------------------------------------------- */

namespace murxla {

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

void
AbsSort::set_id(uint64_t id)
{
  d_id = id;
}

uint64_t
AbsSort::get_id() const
{
  return d_id;
}

void
AbsSort::set_kind(SortKind sort_kind)
{
  d_kind = sort_kind;
}

SortKind
AbsSort::get_kind() const
{
  return d_kind;
}

void
AbsSort::set_sorts(const std::vector<Sort>& sorts)
{
  d_sorts = sorts;
}

const std::vector<Sort>&
AbsSort::get_sorts() const
{
  return d_sorts;
}

void
AbsSort::set_dt_ctors(const DatatypeConstructorMap& ctors)
{
  d_dt_ctors = ctors;
}

std::vector<std::string>
AbsSort::get_dt_ctor_names() const
{
  std::vector<std::string> res(d_dt_ctors.size());
  std::transform(
      d_dt_ctors.begin(), d_dt_ctors.end(), res.begin(), [](const auto& pair) {
        return pair.first;
      });
  return res;
}

std::vector<std::string>
AbsSort::get_dt_sel_names(const std::string& ctor) const
{
  std::vector<std::string> res(d_dt_ctors.at(ctor).size());
  std::transform(d_dt_ctors.at(ctor).begin(),
                 d_dt_ctors.at(ctor).end(),
                 res.begin(),
                 [](const auto& pair) { return pair.first; });
  return res;
}

Sort
AbsSort::get_dt_sel_sort(const std::string& ctor, const std::string& sel) const
{
  const auto& sels = d_dt_ctors.at(ctor);
  Sort res;
  for (const auto& s : sels)
  {
    if (s.first == sel)
    {
      res = s.second;
      break;
    }
  }
  return res;
}

const AbsSort::DatatypeConstructorMap&
AbsSort::get_dt_ctors() const
{
  return d_dt_ctors;
}

uint32_t
AbsSort::get_bv_size() const
{
  return 0;
}

std::string
AbsSort::get_dt_name() const
{
  return "";
}

uint32_t
AbsSort::get_dt_num_cons() const
{
  return 0;
}

std::vector<std::string>
AbsSort::get_dt_cons_names() const
{
  return {};
}

uint32_t
AbsSort::get_dt_cons_num_sels(const std::string& name) const
{
  return 0;
}

std::vector<std::string>
AbsSort::get_dt_cons_sel_names(const std::string& name) const
{
  return {};
}

uint32_t
AbsSort::get_fp_exp_size() const
{
  return 0;
}
uint32_t
AbsSort::get_fp_sig_size() const
{
  return 0;
}

Sort
AbsSort::get_array_index_sort() const
{
  return nullptr;
}

Sort
AbsSort::get_array_element_sort() const
{
  return nullptr;
}

Sort
AbsSort::get_bag_element_sort() const
{
  return nullptr;
}

uint32_t
AbsSort::get_fun_arity() const
{
  return 0;
}

Sort
AbsSort::get_fun_codomain_sort() const
{
  return nullptr;
}

std::vector<Sort>
AbsSort::get_fun_domain_sorts() const
{
  return std::vector<Sort>();
}

Sort
AbsSort::get_seq_element_sort() const
{
  return nullptr;
}

Sort
AbsSort::get_set_element_sort() const
{
  return nullptr;
}

bool
AbsSort::not_equals(const std::shared_ptr<AbsSort>& other) const
{
  return !equals(other);
}

bool
operator==(const Sort& a, const Sort& b)
{
  if (a == nullptr) return b == nullptr;
  if (b == nullptr) return a == nullptr;
  return a->equals(b) && a->get_kind() == b->get_kind();
}

bool
operator!=(const Sort& a, const Sort& b)
{
  if (a == nullptr) return b != nullptr;
  if (b == nullptr) return a != nullptr;
  return a->not_equals(b) || a->get_kind() != b->get_kind();
}

std::ostream&
operator<<(std::ostream& out, const Sort s)
{
  assert(s->get_id());
  out << "s" << s->get_id();
  return out;
}

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

bool
AbsTerm::is_array() const
{
  return get_sort()->is_array();
}

bool
AbsTerm::is_bag() const
{
  return get_sort()->is_bag();
}

bool
AbsTerm::is_bool() const
{
  return get_sort()->is_bool();
}

bool
AbsTerm::is_bv() const
{
  return get_sort()->is_bv();
}

bool
AbsTerm::is_dt() const
{
  return get_sort()->is_dt();
}

bool
AbsTerm::is_fp() const
{
  return get_sort()->is_fp();
}

bool
AbsTerm::is_fun() const
{
  return get_sort()->is_fun();
}

bool
AbsTerm::is_int() const
{
  return get_sort()->is_int();
}

bool
AbsTerm::is_real() const
{
  return get_sort()->is_real();
}

bool
AbsTerm::is_rm() const
{
  return get_sort()->is_rm();
}

bool
AbsTerm::is_string() const
{
  return get_sort()->is_string();
}

bool
AbsTerm::is_reglan() const
{
  return get_sort()->is_reglan();
}

bool
AbsTerm::is_seq() const
{
  return get_sort()->is_seq();
}

bool
AbsTerm::is_set() const
{
  return get_sort()->is_set();
}

bool
AbsTerm::is_bag_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_bag();
}

bool
AbsTerm::is_bool_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_bool();
}

bool
AbsTerm::is_bv_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_bv();
}

bool
AbsTerm::is_dt_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_dt();
}

bool
AbsTerm::is_fp_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_fp();
}

bool
AbsTerm::is_int_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_int();
}

bool
AbsTerm::is_real_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_real();
}

bool
AbsTerm::is_reglan_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_reglan();
}

bool
AbsTerm::is_rm_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_rm();
}

bool
AbsTerm::is_seq_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_seq();
}

bool
AbsTerm::is_set_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_set();
}

bool
AbsTerm::is_string_value() const
{
  return get_leaf_kind() == LeafKind::VALUE && is_string();
}

void
AbsTerm::set_special_value_kind(const AbsTerm::SpecialValueKind& kind)
{
  d_value_kind = kind;
}

bool
AbsTerm::is_special_value(const AbsTerm::SpecialValueKind& kind) const
{
  assert(get_leaf_kind() == LeafKind::VALUE
         || d_value_kind == SPECIAL_VALUE_NONE);
  bool res = d_value_kind == kind;
  if (!res && is_bv() && get_bv_size() == 1)
  {
    if (kind == AbsTerm::SPECIAL_VALUE_BV_ONE)
    {
      return d_value_kind == AbsTerm::SPECIAL_VALUE_BV_ONES
             || d_value_kind == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED;
    }
    else if (kind == AbsTerm::SPECIAL_VALUE_BV_ONES)
    {
      return d_value_kind == AbsTerm::SPECIAL_VALUE_BV_ONE
             || d_value_kind == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED;
    }
    else if (kind == AbsTerm::SPECIAL_VALUE_BV_ZERO)
    {
      return d_value_kind == AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED;
    }
    else if (kind == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED)
    {
      return d_value_kind == AbsTerm::SPECIAL_VALUE_BV_ONE
             || d_value_kind == AbsTerm::SPECIAL_VALUE_BV_ONES;
    }
    else
    {
      assert(kind == AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED);
      return d_value_kind == AbsTerm::SPECIAL_VALUE_BV_ZERO;
    }
  }
  return res;
}

bool
AbsTerm::is_const() const
{
  return d_leaf_kind == LeafKind::CONSTANT;
}

bool
AbsTerm::is_value() const
{
  return d_leaf_kind == LeafKind::VALUE;
}

bool
AbsTerm::is_var() const
{
  return d_leaf_kind == LeafKind::VARIABLE;
}

const Op::Kind&
AbsTerm::get_kind() const
{
  return Op::UNDEFINED;
}

std::vector<std::shared_ptr<AbsTerm>>
AbsTerm::get_children() const
{
  return {};
}

void
AbsTerm::set_id(uint64_t id)
{
  d_id = id;
}

uint64_t
AbsTerm::get_id() const
{
  return d_id;
}

void
AbsTerm::set_sort(Sort sort)
{
  d_sort = sort;
}

void
AbsTerm::set_leaf_kind(LeafKind kind)
{
  d_leaf_kind = kind;
}

AbsTerm::LeafKind
AbsTerm::get_leaf_kind() const
{
  return d_leaf_kind;
}

Sort
AbsTerm::get_sort() const
{
  return d_sort;
}

uint32_t
AbsTerm::get_bv_size() const
{
  return get_sort()->get_bv_size();
}

uint32_t
AbsTerm::get_fp_exp_size() const
{
  return get_sort()->get_fp_exp_size();
}
uint32_t
AbsTerm::get_fp_sig_size() const
{
  return get_sort()->get_fp_sig_size();
}

Sort
AbsTerm::get_array_index_sort() const
{
  return get_sort()->get_array_index_sort();
}

Sort
AbsTerm::get_array_element_sort() const
{
  return get_sort()->get_array_element_sort();
}

uint32_t
AbsTerm::get_fun_arity() const
{
  return get_sort()->get_fun_arity();
}

Sort
AbsTerm::get_fun_codomain_sort() const
{
  return get_sort()->get_fun_codomain_sort();
}

std::vector<Sort>
AbsTerm::get_fun_domain_sorts() const
{
  return get_sort()->get_fun_domain_sorts();
}

bool
AbsTerm::is_indexed() const
{
  Op::Kind kind = get_kind();
  if (kind == Op::BV_EXTRACT || kind == Op::BV_REPEAT
      || kind == Op::BV_ROTATE_LEFT || kind == Op::BV_ROTATE_RIGHT
      || kind == Op::BV_SIGN_EXTEND || kind == Op::BV_ZERO_EXTEND
      || kind == Op::INT_IS_DIV)
  {
    return true;
  }
  return false;
}

std::vector<std::string>
AbsTerm::get_indices() const
{
  return {};
}

size_t
AbsTerm::get_num_indices() const
{
  return 0;
}

void
AbsTerm::set_levels(const std::vector<uint64_t>& levels)
{
  d_levels.clear();
  d_levels.insert(d_levels.end(), levels.begin(), levels.end());
}

const std::vector<uint64_t>&
AbsTerm::get_levels() const
{
  return d_levels;
}

bool
AbsTerm::not_equals(const std::shared_ptr<AbsTerm>& other) const
{
  return !equals(other);
}

bool
operator==(const Term& a, const Term& b)
{
  if (a == nullptr) return b == nullptr;
  if (b == nullptr) return a == nullptr;
  bool res = a->equals(b) && a->get_sort() == b->get_sort();
  assert(!res || a->get_id() == 0 || b->get_id() == 0
         || a->get_id() == b->get_id());
  return res;
}

bool
operator!=(const Term& a, const Term& b)
{
  if (a == nullptr) return b != nullptr;
  if (b == nullptr) return a != nullptr;
  bool res = a->not_equals(b) || a->get_sort() != b->get_sort();
  assert(!res || (a->get_id() != 0 && b->get_id() != 0)
         || a->get_id() != b->get_id());
  return res;
}

std::ostream&
operator<<(std::ostream& out, const Term t)
{
  assert(t->get_id());
  out << "t" << t->get_id();
  return out;
}

std::ostream&
operator<<(std::ostream& out, const std::vector<Term>& vector)
{
  for (const Term& term : vector) out << " " << term;
  return out;
}

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

bool
Solver::supports_theory(TheoryId theory) const
{
  const TheoryIdVector& theories = get_supported_theories();
  return std::find(theories.begin(), theories.end(), theory) != theories.end();
}

TheoryIdVector
Solver::get_supported_theories() const
{
  TheoryIdVector res;
  for (int32_t t = 0; t < THEORY_ALL; ++t)
    res.push_back(static_cast<TheoryId>(t));
  return res;
}

TheoryIdVector
Solver::get_unsupported_quant_theories() const
{
  return {};
}

OpKindSet
Solver::get_unsupported_op_kinds() const
{
  return {};
}

Solver::OpKindSortKindMap
Solver::get_unsupported_op_sort_kinds() const
{
  /* Exclude sorts that would create higher order terms. */
  return {{Op::DISTINCT, {SORT_FUN}},
          {Op::EQUAL, {SORT_FUN}},
          {Op::ITE, {SORT_FUN}}};
}

SortKindSet
Solver::get_unsupported_var_sort_kinds() const
{
  return {SORT_FUN};
}

SortKindSet
Solver::get_unsupported_dt_sel_codomain_sort_kinds() const
{
  return {SORT_FUN};
}

SortKindSet
Solver::get_unsupported_fun_domain_sort_kinds() const
{
  return {SORT_FUN};
}

SortKindSet
Solver::get_unsupported_fun_codomain_sort_kinds() const
{
  return {SORT_FUN};
}

SortKindSet
Solver::get_unsupported_array_index_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
}

SortKindSet
Solver::get_unsupported_array_element_sort_kinds() const
{
  return {};
}

SortKindSet
Solver::get_unsupported_bag_element_sort_kinds() const
{
  return {};
}

SortKindSet
Solver::get_unsupported_seq_element_sort_kinds() const
{
  return {};
}

SortKindSet
Solver::get_unsupported_set_element_sort_kinds() const
{
  return {SORT_FUN};
}

SortKindSet
Solver::get_unsupported_get_value_sort_kinds() const
{
  return {};
}

void
Solver::configure_fsm(FSM* fsm) const
{
  // default: do nothing
}

void
Solver::disable_unsupported_actions(FSM* fsm) const
{
  // default: do nothing
}

void
Solver::configure_smgr(SolverManager* smgr) const
{
  // default: do nothing
}

void
Solver::configure_opmgr(OpKindManager* opmgr) const
{
  // default: do nothing
}

void
Solver::add_special_value(SortKind sort_kind,
                          const AbsTerm::SpecialValueKind& kind)
{
  if (d_special_values.find(sort_kind) == d_special_values.end())
  {
    d_special_values[sort_kind] = {};
  }
  if (d_special_values.at(sort_kind).find(kind)
      == d_special_values.at(sort_kind).end())
  {
    d_special_values.at(sort_kind).insert(kind);
  }
}

void
Solver::reset_sat()
{
  // default: do nothing
}

const std::vector<Solver::Base>&
Solver::get_bases() const
{
  return d_bases;
}

const std::unordered_set<AbsTerm::SpecialValueKind>&
Solver::get_special_values(SortKind sort_kind) const
{
  if (d_special_values.find(sort_kind) == d_special_values.end())
  {
    return d_special_values.at(SORT_ANY);
  }
  return d_special_values.at(sort_kind);
}

Term
Solver::mk_value(Sort sort, const std::string& value)
{
  return Term();
}

Term
Solver::mk_value(Sort sort, const std::string& num, const std::string& den)
{
  return Term();
}

Term
Solver::mk_value(Sort sort, const std::string& value, Base base)
{
  return Term();
}

Term
Solver::mk_special_value(Sort sort, const AbsTerm::SpecialValueKind& value)
{
  return Term();
}

Sort
Solver::mk_sort(SortKind kind, uint32_t size)
{
  return Sort();
}

Sort
Solver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  return Sort();
}

Sort
Solver::mk_sort(SortKind kind,
                const std::string& name,
                const AbsSort::DatatypeConstructorMap& ctors)
{
  return Sort();
}

Term
Solver::mk_term(const Op::Kind& kind,
                const std::vector<std::string>& str_args,
                const std::vector<Term>& args)
{
  return Term();
}

std::vector<Term>
Solver::get_unsat_core()
{
  return std::vector<Term>();
}

std::ostream&
operator<<(std::ostream& out, const Solver::Result& r)
{
  switch (r)
  {
    case Solver::Result::SAT: out << "sat"; break;
    case Solver::Result::UNSAT: out << "unsat"; break;
    default: out << "unknown";
  }
  return out;
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla

namespace std {

size_t
hash<murxla::Sort>::operator()(const murxla::Sort& s) const
{
  return s->hash();
};

size_t
hash<murxla::Term>::operator()(const murxla::Term& t) const
{
  return t->hash();
};

}  // namespace std
