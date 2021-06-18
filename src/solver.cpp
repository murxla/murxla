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
AbsSort::get_kind()
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

uint32_t
AbsSort::get_bv_size() const
{
  return 0;
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

bool
operator==(const Sort& a, const Sort& b)
{
  return a->equals(b) && a->get_kind() == b->get_kind();
}

std::ostream&
operator<<(std::ostream& out, const Sort s)
{
  assert(s->get_id());
  out << s->get_id();
  return out;
}

size_t
HashSort::operator()(const Sort s) const
{
  return s->hash();
}

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

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
AbsTerm::set_is_value(bool is_value)
{
  d_is_value = is_value;
}

bool
AbsTerm::is_value()
{
  return d_is_value;
}

Sort
AbsTerm::get_sort() const
{
  return d_sort;
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
operator==(const Term& a, const Term& b)
{
  bool res = a->equals(b) && a->get_sort() == b->get_sort();
  assert(!res || a->get_id() == 0 || b->get_id() == 0
         || a->get_id() == b->get_id());
  return res;
}

std::ostream&
operator<<(std::ostream& out, const Term t)
{
  assert(t->get_id());
  out << t->get_id();
  return out;
}

std::ostream&
operator<<(std::ostream& out, const std::vector<Term>& vector)
{
  for (const Term& term : vector) out << " " << term;
  return out;
}

size_t
HashTerm::operator()(const Term t) const
{
  return t->hash();
}

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

const Solver::SpecialValueKind Solver::SPECIAL_VALUE_BV_ZERO = "bv-zero";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_BV_ONE  = "bv-one";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_BV_ONES = "bv-ones";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_BV_MIN_SIGNED =
    "bv-min-signed";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_BV_MAX_SIGNED =
    "bv-max-signed";

const Solver::SpecialValueKind Solver::SPECIAL_VALUE_FP_NAN      = "nan";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_FP_POS_INF  = "+oo";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_FP_NEG_INF  = "-oo";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_FP_POS_ZERO = "+zero";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_FP_NEG_ZERO = "-zero";

const Solver::SpecialValueKind Solver::SPECIAL_VALUE_RM_RNE = "rne";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_RM_RNA = "rna";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_RM_RTN = "rtn";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_RM_RTP = "rtp";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_RM_RTZ = "rtz";

const Solver::SpecialValueKind Solver::SPECIAL_VALUE_RE_NONE    = "re.none";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_RE_ALL     = "re.all";
const Solver::SpecialValueKind Solver::SPECIAL_VALUE_RE_ALLCHAR = "re.allchar";

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

SortKindSet
Solver::get_unsupported_var_sort_kinds() const
{
  return {SORT_FUN};
}

SortKindSet
Solver::get_unsupported_fun_domain_sort_kinds() const
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

void
Solver::configure_fsm(FSM* fsm) const
{
  // default: do nothing
}

void
Solver::configure_smgr(SolverManager* smgr) const
{
  // default: do nothing
}

void
Solver::add_special_value(SortKind sort_kind, const SpecialValueKind& kind)
{
  if (d_special_values.find(sort_kind) == d_special_values.end())
  {
    d_special_values[sort_kind] = {};
  }
  assert(d_special_values.at(sort_kind).find(kind)
         == d_special_values.at(sort_kind).end());
  d_special_values.at(sort_kind).insert(kind);
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

const std::unordered_set<Solver::SpecialValueKind>&
Solver::get_special_values(SortKind sort_kind) const
{
  if (d_special_values.find(sort_kind) == d_special_values.end())
  {
    return d_special_values.at(SORT_ANY);
  }
  return d_special_values.at(sort_kind);
}

Term
Solver::mk_value(Sort sort, std::string value)
{
  return Term();
}

Term
Solver::mk_value(Sort sort, std::string num, std::string den)
{
  return Term();
}

Term
Solver::mk_value(Sort sort, std::string value, Base base)
{
  return Term();
}

Term
Solver::mk_special_value(Sort sort, const SpecialValueKind& value)
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
