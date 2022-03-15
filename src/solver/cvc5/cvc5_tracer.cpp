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

using namespace cvc5::api;

namespace murxla {
namespace cvc5 {

// get_id specializations
template <>
uint64_t
Tracer::get_id(const Term& term)
{
  auto it = d_term_map.find(term);
  assert(it != d_term_map.end());
  return it->second;
}

template <>
uint64_t
Tracer::get_id(const Op& op)
{
  auto it = d_op_map.find(op);
  assert(it != d_op_map.end());
  return it->second;
}

template <>
uint64_t
Tracer::get_id(const Sort& sort)
{
  auto it = d_sort_map.find(sort);
  assert(it != d_sort_map.end());
  return it->second;
}

template <>
uint64_t
Tracer::get_id(const DatatypeDecl& decl)
{
  auto it = d_dt_decl_map.find(decl.getName());
  assert(it != d_dt_decl_map.end());
  return it->second;
}

Tracer&
Tracer::operator<<(const Term& term)
{
  d_trace << "t" << get_id(term);
  return *this;
}

Tracer&
Tracer::operator<<(const Op& op)
{
  d_trace << "o" << get_id(op);
  return *this;
}

Tracer&
Tracer::operator<<(const Sort& sort)
{
  d_trace << "s" << get_id(sort);
  return *this;
}

Tracer&
Tracer::operator<<(const DatatypeDecl& decl)
{
  d_trace << "d" << get_id(decl);
  return *this;
}

Tracer&
Tracer::operator<<(const std::string& s)
{
  d_trace << "\"" << s << "\"";
  return *this;
}

Tracer&
Tracer::operator<<(const char* s)
{
  d_trace << s;

  // Writes and flushes to stdout if '\n' is encountered.
  size_t len = strlen(s);
  if (d_print_trace && s[len - 1] == '\n')
  {
    std::cout << d_trace.str() << std::flush;
    d_trace.str("");
    d_trace.clear();
  }
  return *this;
}

Tracer&
Tracer::operator<<(bool b)
{
  d_trace << std::boolalpha << b;
  return *this;
}

void
Tracer::init()
{
  *this << "#include <cvc5/cvc5.h>\n\n";
  *this << "using namespace cvc5::api;\n";
  *this << "int main(void)\n{\n";
  *this << "Solver solver;\n";
}

// new_id specializations
template <>
uint64_t
Tracer::new_id<Term>()
{
  uint64_t id = d_term_id++;
  *this << "Term t" << id << " = ";
  return id;
}

template <>
uint64_t
Tracer::new_id<Op>()
{
  uint64_t id = d_op_id++;
  *this << "Op o" << id << " = ";
  return id;
}

template <>
uint64_t
Tracer::new_id<Sort>()
{
  uint64_t id = d_sort_id++;
  *this << "Sort s" << id << " = ";
  return id;
}

template <>
uint64_t
Tracer::new_id<DatatypeDecl>()
{
  uint64_t id = d_dt_decl_id++;
  *this << "DatatypeDecl d" << id << " = ";
  return id;
}

// register_id specializations

template <>
void
Tracer::register_id(uint64_t id, Sort& sort)
{
  d_sort_map.emplace(sort, id);
}

template <>
void
Tracer::register_id(uint64_t id, Term& term)
{
  d_term_map.emplace(term, id);
  auto sort = term.getSort();
  // If term has a new sort that we haven't seen yet, declare it so it can be
  // used later as an argument.
  auto it = d_sort_map.find(sort);
  if (it == d_sort_map.end())
  {
    auto sort_id = new_id<Sort>();
    *this << term << ".getSort();\n";
    register_id(sort_id, sort);
  }
}

template <>
void
Tracer::register_id(uint64_t id, Op& op)
{
  d_op_map.emplace(op, id);
}

template <>
void
Tracer::register_id(uint64_t id, DatatypeDecl& decl)
{
  d_dt_decl_map.emplace(decl.getName(), id);
}

}  // namespace cvc5
}  // namespace murxla

#endif
