/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */

#ifdef MURXLA_USE_CVC5

#include "solver/cvc5/cvc5_tracer.hpp"

#include <cassert>
#include <cstring>
#include <type_traits>

using namespace cvc5;

namespace murxla {

// get_id specializations
template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::get_id(const Term& term)
{
  auto it = d_data.get_term_map().find(term);
  assert(it != d_data.get_term_map().end());
  return it->second;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::get_id(const Op& op)
{
  auto it = d_data.get_op_map().find(op);
  assert(it != d_data.get_op_map().end());
  return it->second;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::get_id(const Sort& sort)
{
  auto it = d_data.get_sort_map().find(sort);
  assert(it != d_data.get_sort_map().end());
  return it->second;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::get_id(const DatatypeDecl& decl)
{
  auto it = d_data.get_dt_decl_map().find(decl.getName());
  assert(it != d_data.get_dt_decl_map().end());
  return it->second;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::get_id(const DatatypeConstructor& cons)
{
  auto it = d_data.get_dt_cons_map().find(cons.getName());
  assert(it != d_data.get_dt_cons_map().end());
  return it->second;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::get_id(const DatatypeConstructorDecl& decl)
{
  std::string s = decl.toString();
  // String representation of constructor declarations change as soon as
  // selectors are added. We only use the name of the constructor.
  auto pos = s.find('(');
  if (pos != std::string::npos)
  {
    s = s.substr(0, pos);
  }
  auto it = d_data.get_dt_cons_decl_map().find(s);
  assert(it != d_data.get_dt_cons_decl_map().end());
  return it->second;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::get_id(const DatatypeSelector& sel)
{
  auto it = d_data.get_dt_sel_map().find(sel.getName());
  assert(it != d_data.get_dt_sel_map().end());
  return it->second;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::get_id(const Datatype& dt)
{
  auto it = d_data.get_dt_map().find(dt.getName());
  assert(it != d_data.get_dt_map().end());
  return it->second;
}

Tracer<cvc5::Cvc5TracerData>&
operator<<(Tracer<cvc5::Cvc5TracerData>& tracer, const Term& term)
{
  tracer.get_trace() << "t" << tracer.get_id(term);
  return tracer;
}

Tracer<cvc5::Cvc5TracerData>&
operator<<(Tracer<cvc5::Cvc5TracerData>& tracer, const Op& op)
{
  tracer.get_trace() << "o" << tracer.get_id(op);
  return tracer;
}

Tracer<cvc5::Cvc5TracerData>&
operator<<(Tracer<cvc5::Cvc5TracerData>& tracer, const Sort& sort)
{
  tracer.get_trace() << "s" << tracer.get_id(sort);
  return tracer;
}

Tracer<cvc5::Cvc5TracerData>&
operator<<(Tracer<cvc5::Cvc5TracerData>& tracer, const DatatypeDecl& decl)
{
  tracer.get_trace() << "d" << tracer.get_id(decl);
  return tracer;
}

Tracer<cvc5::Cvc5TracerData>&
operator<<(Tracer<cvc5::Cvc5TracerData>& tracer,
           const DatatypeConstructor& cons)
{
  tracer.get_trace() << "dtc" << tracer.get_id(cons);
  return tracer;
}

Tracer<cvc5::Cvc5TracerData>&
operator<<(Tracer<cvc5::Cvc5TracerData>& tracer,
           const DatatypeConstructorDecl& decl)
{
  tracer.get_trace() << "dtcd" << tracer.get_id(decl);
  return tracer;
}

Tracer<cvc5::Cvc5TracerData>&
operator<<(Tracer<cvc5::Cvc5TracerData>& tracer, const DatatypeSelector& sel)
{
  tracer.get_trace() << "dts" << tracer.get_id(sel);
  return tracer;
}

Tracer<cvc5::Cvc5TracerData>&
operator<<(Tracer<cvc5::Cvc5TracerData>& tracer, const Datatype& dt)
{
  tracer.get_trace() << "dt" << tracer.get_id(dt);
  return tracer;
}

Tracer<cvc5::Cvc5TracerData>&
operator<<(Tracer<cvc5::Cvc5TracerData>& tracer, const ::cvc5::RoundingMode& m)
{
  switch (m)
  {
    case ::cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY:
      tracer.get_trace() << "cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY";
      break;
    case ::cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN:
      tracer.get_trace() << "cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN";
      break;
    case ::cvc5::RoundingMode::ROUND_TOWARD_ZERO:
      tracer.get_trace() << "cvc5::RoundingMode::ROUND_TOWARD_ZERO";
      break;
    case ::cvc5::RoundingMode::ROUND_TOWARD_NEGATIVE:
      tracer.get_trace() << "cvc5::RoundingMode::ROUND_TOWARD_NEGATIVE";
      break;
    case ::cvc5::RoundingMode::ROUND_TOWARD_POSITIVE:
      tracer.get_trace() << "cvc5::RoundingMode::ROUND_TOWARD_POSITIVE";
      break;
  }
  return tracer;
}

Tracer<cvc5::Cvc5TracerData>&
operator<<(Tracer<cvc5::Cvc5TracerData>& tracer,
           const ::cvc5::modes::BlockModelsMode& m)
{
  switch (m)
  {
    case ::cvc5::modes::BlockModelsMode::LITERALS:
      tracer.get_trace() << "cvc5::modes::BlockModelsMode::LITERALS";
      break;
    case ::cvc5::modes::BlockModelsMode::VALUES:
      tracer.get_trace() << "cvc5::modes::BlockModelsMode::VALUES";
      break;
  }
  return tracer;
}

// new_id specializations
template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<Term>()
{
  uint64_t id = d_id++;
  *this << "Term t" << id << " = ";
  return id;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<std::vector<Term>>()
{
  uint64_t id = d_id++;
  *this << "std::vector<Term> v" << id << " = ";
  return id;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<Op>()
{
  uint64_t id = d_id++;
  *this << "Op o" << id << " = ";
  return id;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<Sort>()
{
  uint64_t id = d_id++;
  *this << "Sort s" << id << " = ";
  return id;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<std::vector<Sort>>()
{
  uint64_t id = d_id++;
  *this << "std::vector<Sort> v" << id << " = ";
  return id;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<DatatypeDecl>()
{
  uint64_t id = d_id++;
  *this << "DatatypeDecl d" << id << " = ";
  return id;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<DatatypeConstructor>()
{
  uint64_t id = d_id++;
  *this << "DatatypeConstructor dtc" << id << " = ";
  return id;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<DatatypeConstructorDecl>()
{
  uint64_t id = d_id++;
  *this << "DatatypeConstructorDecl dtcd" << id << " = ";
  return id;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<DatatypeSelector>()
{
  uint64_t id = d_id++;
  *this << "DatatypeSelector dts" << id << " = ";
  return id;
}

template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<Datatype>()
{
  uint64_t id = d_id++;
  *this << "Datatype dt" << id << " = ";
  return id;
}

// register_id specializations

template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t id, Sort& sort)
{
  d_data.get_sort_map().emplace(sort, id);
}

template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t vecid,
                                          std::vector<Sort>& sorts)
{
  for (size_t i = 0; i < sorts.size(); ++i)
  {
    uint64_t id = d_id++;
    d_data.get_sort_map().emplace(sorts[i], id);
    *this << "Sort s" << id << " = v" << vecid << "[" << i << "];\n";
  }
}

template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t vecid,
                                          std::vector<Term>& terms)
{
  for (size_t i = 0; i < terms.size(); ++i)
  {
    uint64_t id = d_id++;
    d_data.get_term_map().emplace(terms[i], id);
    *this << "Term t" << id << " = v" << vecid << "[" << i << "];\n";
  }
}

template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t id, Term& term)
{
  d_data.get_term_map().emplace(term, id);
  auto sort = term.getSort();
  // If term has a new sort that we haven't seen yet, declare it so it can be
  // used later as an argument.
  auto it = d_data.get_sort_map().find(sort);
  if (it == d_data.get_sort_map().end())
  {
    auto sort_id = new_id<Sort>();
    *this << term << ".getSort();\n";
    register_id(sort_id, sort);
  }
}

template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t id, Op& op)
{
  d_data.get_op_map().emplace(op, id);
}

template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t id, DatatypeDecl& decl)
{
  d_data.get_dt_decl_map().emplace(decl.getName(), id);
}

template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t id,
                                          DatatypeConstructor& cons)
{
  d_data.get_dt_cons_map().emplace(cons.getName(), id);
}

template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t id,
                                          DatatypeConstructorDecl& decl)
{
  d_data.get_dt_cons_decl_map().emplace(decl.toString(), id);
}

template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t id, DatatypeSelector& sel)
{
  d_data.get_dt_sel_map().emplace(sel.getName(), id);
}

template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t id, Datatype& dt)
{
  d_data.get_dt_map().emplace(dt.getName(), id);
}

// Ignore types
template <>
template <>
uint64_t
Tracer<cvc5::Cvc5TracerData>::new_id<Result>()
{
  return 0;
}
template <>
template <>
void
Tracer<cvc5::Cvc5TracerData>::register_id(uint64_t id, Result& r)
{
}

template <>
void
Tracer<cvc5::Cvc5TracerData>::init()
{
  if (d_print_trace)
  {
    *this << "#include <cvc5/cvc5.h>\n\n";
    *this << "using namespace cvc5;\n";
    *this << "int main(void)\n{\n";
    *this << "Solver solver;\n";
  }
}

}  // namespace murxla

#endif
