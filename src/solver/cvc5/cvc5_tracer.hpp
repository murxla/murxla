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

#ifndef __MURXLA__CVC5_TRACER_H
#define __MURXLA__CVC5_TRACER_H

#include <iostream>

#include "cvc5/cvc5.h"

namespace murxla {
namespace cvc5 {

class Tracer
{
 public:
  Tracer(bool print_trace) : d_print_trace(print_trace) {}

  void init();

  /** Retrieve id for given object o. */
  template <typename T>
  uint64_t get_id(const T& o);

  Tracer& operator<<(const ::cvc5::api::Term& term);
  Tracer& operator<<(const ::cvc5::api::Op& op);
  Tracer& operator<<(const ::cvc5::api::Sort& sort);
  Tracer& operator<<(const ::cvc5::api::DatatypeDecl& decl);
  Tracer& operator<<(const std::string& s);
  Tracer& operator<<(const char* s);
  Tracer& operator<<(bool b);

  template <typename T>
  Tracer& operator<<(const std::vector<T>& args)
  {
    *this << "{";
    for (size_t i = 0; i < args.size(); ++i)
    {
      if (i > 0)
      {
        *this << ", ";
      }
      *this << args[i];
    }
    *this << "}";
    return *this;
  }

  template <typename T>
  Tracer& operator<<(const std::set<T>& args)
  {
    *this << "{";
    size_t i = 0;
    for (const auto& a : args)
    {
      if (i++ > 0)
      {
        *this << ", ";
      }
      *this << a;
    }
    *this << "}";
    return *this;
  }

  template <typename T>
  Tracer& operator<<(T x)
  {
    d_trace << x;
    return *this;
  }

  void trace() {}
  template <typename First, typename... Args>
  void trace(First&& first, Args&&... args)
  {
    *this << first;
    if constexpr (sizeof...(args) > 0)
    {
      *this << ", ";
      trace(std::forward<Args>(args)...);
    }
  }

  template <typename FT, typename FF, typename... Args>
  auto operator()(const char* name, FT&& trace_func, FF&& func, Args&&... args)
  {
    using result_type = decltype(func(std::forward<Args>(args)...));
    uint64_t id       = 0;
    if constexpr (!std::is_same_v<result_type, void>)
    {
      if (d_print_trace)
      {
        id = new_id<result_type>();
      }
    }
    if (d_print_trace)
    {
      trace_func(*this, std::forward<Args>(args)...);
      *this << "(";
      trace(std::forward<Args>(args)...);
      *this << ");\n";
    }
    if constexpr (std::is_same_v<result_type, void>)
    {
      func(std::forward<Args>(args)...);
    }
    else
    {
      auto res = func(std::forward<Args>(args)...);
      if (d_print_trace)
      {
        register_id(id, res);
      }
      return res;
    }
  }

 private:
  template <typename T>
  uint64_t new_id()
  {
    return 0;
  }
  template <typename T>
  void register_id(uint64_t id, T& o)
  {
  }

  uint64_t d_term_id    = 0;
  uint64_t d_op_id      = 0;
  uint64_t d_sort_id    = 0;
  uint64_t d_dt_decl_id = 0;
  uint64_t d_vec_id     = 0;

  std::unordered_map<::cvc5::api::Term, uint64_t> d_term_map;
  std::unordered_map<::cvc5::api::Op, uint64_t> d_op_map;
  std::unordered_map<::cvc5::api::Sort, uint64_t> d_sort_map;
  std::unordered_map<std::string, uint64_t> d_dt_decl_map;

  /** Used as line buffer for writing the trace. */
  std::stringstream d_trace;

  /** Indicates whether trace should be printed to stdout. */
  bool d_print_trace;
};

}  // namespace cvc5
}  // namespace murxla

#endif
#endif
