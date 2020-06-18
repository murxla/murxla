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

Solver::Solver(RNGenerator& rng) : d_rng(rng)
{
}

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

std::ostream&
operator<<(std::ostream& out, const Solver::Result& r)
{
  std::string s;
  switch (r)
  {
    case Solver::Result::SAT: s = "SAT"; break;
    case Solver::Result::UNSAT: s = "UNSAT"; break;
    default: s = "UNKNOWN";
  }
  out << s;
  return out;
}

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt
