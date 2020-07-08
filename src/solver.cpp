#include "solver.hpp"
#include "theory.hpp"

/* -------------------------------------------------------------------------- */

namespace smtmbt {

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

Sort
AbsTerm::get_sort() const
{
  return d_sort;
}

void
AbsTerm::set_level(uint64_t level)
{
  d_level = level;
}

uint64_t
AbsTerm::get_level() const
{
  return d_level;
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

const std::unordered_map<std::string, Solver::SpecialValueFP>
    Solver::s_special_values_fp = {
        {"nan", Solver::SpecialValueFP::SMTMBT_FP_NAN},
        {"+oo", Solver::SpecialValueFP::SMTMBT_FP_POS_INF},
        {"-oo", Solver::SpecialValueFP::SMTMBT_FP_NEG_INF},
        {"+zero", Solver::SpecialValueFP::SMTMBT_FP_POS_ZERO},
        {"-zero", Solver::SpecialValueFP::SMTMBT_FP_NEG_ZERO}};

const std::unordered_map<std::string, Solver::SpecialValueRM>
    Solver::s_special_values_rm = {
        {"rne", Solver::SpecialValueRM::SMTMBT_FP_RNE},
        {"rna", Solver::SpecialValueRM::SMTMBT_FP_RNA},
        {"rtn", Solver::SpecialValueRM::SMTMBT_FP_RTN},
        {"rtp", Solver::SpecialValueRM::SMTMBT_FP_RTP},
        {"rtz", Solver::SpecialValueRM::SMTMBT_FP_RTZ}};

Solver::Solver(RNGenerator& rng) : d_rng(rng) {}

TheoryIdVector
Solver::get_supported_theories() const
{
  TheoryIdVector res;
  for (int32_t t = 0; t < THEORY_ALL; ++t)
    res.push_back(static_cast<TheoryId>(t));
  return res;
}

OpKindSet
Solver::get_supported_op_kinds() const
{
  OpKindSet unsupported = get_unsupported_op_kinds();
  OpKindSet res;
  for (int32_t o = 0; o < OP_ALL; ++o)
  {
    OpKind op = static_cast<OpKind>(o);
    if (unsupported.find(op) == unsupported.end())
    {
      res.insert(op);
    }
  }
  return res;
}

OpKindSet
Solver::get_unsupported_op_kinds() const
{
  return {};
}

void
Solver::configure_fsm(FSM* fsm) const
{
  // default: do nothing
}

const std::vector<Solver::Base>&
Solver::get_bases() const
{
  return d_bases;
}

const std::vector<Solver::SpecialValueBV>&
Solver::get_special_values_bv() const
{
  return d_special_values_bv;
}

Term
Solver::mk_value(Sort sort, uint64_t value)
{
  return Term();
}

Term
Solver::mk_value(Sort sort, std::string value, Base base)
{
  return Term();
}

Term
Solver::mk_value(Sort sort, SpecialValueFP value)
{
  return Term();
}

Term
Solver::mk_value(Sort sort, SpecialValueRM value)
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
operator<<(std::ostream& out, const Solver::SpecialValueBV val)
{
  switch (val)
  {
    case Solver::SpecialValueBV::SMTMBT_BV_ONE: out << "bv-one";
    case Solver::SpecialValueBV::SMTMBT_BV_ONES: out << "bv-ones";
    case Solver::SpecialValueBV::SMTMBT_BV_MIN_SIGNED: out << "bv-min-signed";
    case Solver::SpecialValueBV::SMTMBT_BV_MAX_SIGNED: out << "bv-max-signed";
    default:
      assert(val == Solver::SpecialValueBV::SMTMBT_BV_ZERO);
      out << "bv-zero";
  }
  return out;
}

std::ostream&
operator<<(std::ostream& out, const Solver::SpecialValueFP val)
{
  for (const auto& p : Solver::s_special_values_fp)
  {
    if (p.second == val)
    {
      out << p.first;
      return out;
    }
  }
  out << "unknown";
  return out;
}

std::ostream&
operator<<(std::ostream& out, const Solver::SpecialValueRM val)
{
  for (const auto& p : Solver::s_special_values_rm)
  {
    if (p.second == val)
    {
      out << p.first;
      return out;
    }
  }
  out << "unknown";
  return out;
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

}  // namespace smtmbt
