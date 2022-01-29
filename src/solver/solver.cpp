/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include "solver/solver.hpp"

#include <algorithm>

#include "theory.hpp"
#include "util.hpp"

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
AbsSort::set_associated_sort(Sort sort)
{
  d_associated_sort = sort;
}

Sort
AbsSort::get_associated_sort() const
{
  return d_associated_sort;
}

void
AbsSort::set_dt_ctors(const DatatypeConstructorMap& ctors)
{
  d_dt_ctors = ctors;
}

bool
AbsSort::is_param_sort() const
{
  return false;
}

bool
AbsSort::is_unresolved_sort() const
{
  return false;
}

std::vector<std::string>
AbsSort::get_dt_ctor_names() const
{
  std::vector<std::string> res(d_dt_ctors.size());
  std::transform(
      d_dt_ctors.begin(), d_dt_ctors.end(), res.begin(), [](const auto& pair) {
        return pair.first;
      });
  assert(!res.empty());
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
AbsSort::get_dt_sel_sort(Sort dt_sort,
                         const std::string& ctor,
                         const std::string& sel) const
{
  const auto& sels = d_dt_ctors.at(ctor);
  Sort res;
  for (const auto& s : sels)
  {
    if (s.first == sel)
    {
      res = s.second;
      if (res == nullptr) res = dt_sort;
      break;
    }
  }
  return res;
}

AbsSort::DatatypeConstructorMap&
AbsSort::get_dt_ctors()
{
  return d_dt_ctors;
}

AbsSort::DatatypeConstructorMap
AbsSort::instantiate_dt_param_sort(const std::vector<Sort>& sorts) const
{
  assert(d_sorts.size() == sorts.size());
  std::unordered_map<Sort, Sort> sorts_map;
  for (size_t i = 0, n = d_sorts.size(); i < n; ++i)
  {
    assert(sorts_map.find(d_sorts[i]) == sorts_map.end());
    sorts_map[d_sorts[i]] = sorts[i];
  }

  DatatypeConstructorMap res;
  for (const auto& c : d_dt_ctors)
  {
    const auto& cname = c.first;
    res[cname]        = {};
    const auto& sels  = c.second;
    for (const auto& sel : sels)
    {
      const auto& sname = sel.first;
      const auto& ssort = sel.second;
      if (ssort && ssort->is_param_sort())
      {
        assert(sorts_map.find(ssort) != sorts_map.end());
        res.at(cname).emplace_back(sname, sorts_map.at(ssort));
      }
      else if (ssort && ssort->is_unresolved_sort())
      {
        std::vector<Sort> inst_sorts = ssort->get_sorts();
        UnresolvedSort* usort =
            new UnresolvedSort(*checked_cast<UnresolvedSort*>(ssort.get()));
        for (auto& s : inst_sorts)
        {
          if (s->is_param_sort())
          {
            assert(sorts_map.find(s) != sorts_map.end());
            s = sorts_map.at(s);
          }
        }
        usort->set_sorts(inst_sorts);
        res.at(cname).emplace_back(sname,
                                   std::shared_ptr<UnresolvedSort>(usort));
      }
      else
      {
        res.at(cname).emplace_back(sname, ssort);
      }
    }
  }
  return res;
}

bool
AbsSort::is_dt_well_founded() const
{
  return true;
}

void
AbsSort::set_dt_is_instantiated(bool value)
{
  d_dt_is_instantiated = value;
}

bool
AbsSort::is_dt_instantiated() const
{
  return d_dt_is_instantiated;
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
  if (s)
  {
    if (s->is_param_sort())
    {
      assert(!s->get_id());
      out << "s\"" << s->to_string() << "\"";
    }
    else if (s->is_unresolved_sort())
    {
      assert(!s->get_id());
      out << "s<\"" << s->to_string() << "\">";
    }
    else
    {
      assert(s->get_id());
      out << "s" << s->get_id();
    }
  }
  else
  {
    out << "s(nil)";
  }
  return out;
}

std::ostream&
operator<<(std::ostream& out, const std::vector<Sort>& vector)
{
  for (const Sort& sort : vector) out << " " << sort;
  return out;
}

size_t
ParamSort::hash() const
{
  return std::hash<std::string>{}(d_symbol);
}

std::string
ParamSort::to_string() const
{
  return d_symbol;
}

bool
ParamSort::equals(const Sort& other) const
{
  return d_symbol == checked_cast<ParamSort*>(other.get())->get_symbol();
}

size_t
UnresolvedSort::hash() const
{
  return std::hash<std::string>{}(d_symbol);
}

std::string
UnresolvedSort::to_string() const
{
  return d_symbol;
}

bool
UnresolvedSort::equals(const Sort& other) const
{
  return d_symbol == checked_cast<UnresolvedSort*>(other.get())->get_symbol();
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
AbsTerm::is_uninterpreted() const
{
  return get_sort()->is_uninterpreted();
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
  if (t)
  {
    assert(t->get_id());
    out << "t" << t->get_id();
  }
  else
  {
    out << "t(nil)";
  }
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

Solver::Solver(SolverSeedGenerator& sng) : d_rng(sng.seed())
{
  for (const auto& it : d_special_values)
  {
    if (!it.second.empty())
    {
      d_special_values_sort_kinds.insert(it.first);
    }
  }
}

void
Solver::add_special_value(SortKind sort_kind,
                          const AbsTerm::SpecialValueKind& kind)
{
  if (d_special_values.find(sort_kind) == d_special_values.end())
  {
    d_special_values[sort_kind] = {};
    d_special_values_sort_kinds.insert(sort_kind);
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

const std::unordered_set<AbsTerm::SpecialValueKind>&
Solver::get_special_values(SortKind sort_kind) const
{
  if (d_special_values.find(sort_kind) == d_special_values.end())
  {
    return d_special_values.at(SORT_ANY);
  }
  return d_special_values.at(sort_kind);
}

const SortKindSet&
Solver::get_special_values_sort_kinds() const
{
  return d_special_values_sort_kinds;
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

std::vector<Sort>
Solver::mk_sort(
    SortKind kind,
    const std::vector<std::string>& dt_names,
    const std::vector<std::vector<Sort>>& param_sorts,
    const std::vector<AbsSort::DatatypeConstructorMap>& constructors)
{
  return {};
}

Sort
Solver::instantiate_sort(Sort param_sort, const std::vector<Sort>& sorts)
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

Term
Solver::mk_term(const Op::Kind& kind,
                Sort sort,
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
