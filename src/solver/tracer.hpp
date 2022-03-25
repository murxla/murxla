/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */

#ifndef __MURXLA__SOLVER_TRACER_H
#define __MURXLA__SOLVER_TRACER_H

#include <cstring>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace murxla {

template <class TData>
class Tracer;

template <class TData>
Tracer<TData>& operator<<(Tracer<TData>& tracer, const char* s);

template <class TData>
Tracer<TData>& operator<<(Tracer<TData>& tracer, bool b);

template <typename T>
Tracer<class TData>& operator<<(Tracer<TData>& tracer, T x);

template <class TData, typename T>
Tracer<TData>&
operator<<(Tracer<TData>& tracer, const std::vector<T>& args)
{
  tracer << "{";
  for (size_t i = 0; i < args.size(); ++i)
  {
    if (i > 0)
    {
      tracer << ", ";
    }
    tracer << args[i];
  }
  tracer << "}";
  return tracer;
}

template <class TData, typename T>
Tracer<TData>&
operator<<(Tracer<TData>& tracer, const std::set<T>& args)
{
  tracer << "{";
  size_t i = 0;
  for (const auto& a : args)
  {
    if (i++ > 0)
    {
      tracer << ", ";
    }
    tracer << a;
  }
  tracer << "}";
  return tracer;
}

template <class TData>
class Tracer
{
 public:
  Tracer(bool print_trace, TData& data)
      : d_print_trace(print_trace), d_data(data)
  {
  }

  std::stringstream& get_trace() { return d_trace; }

  void init();

  /** Retrieve id for given object o. */
  template <typename T>
  uint64_t get_id(const T& o);

  template <typename T>
  uint64_t new_id();

  template <typename T>
  void register_id(uint64_t id, T& o);

  void trace() {}
  template <typename First, typename... Args>
  void trace(First&& first, Args&&... args)
  {
    using first_type = std::decay_t<
        std::remove_const_t<std::remove_reference_t<decltype(first)>>>;
    if constexpr (std::is_same_v<first_type, std:: string>
                  || std::is_same_v<first_type, char const*>
                  || std::is_same_v<first_type, char*>)
    {
      *this << "\"" << first << "\"";
    }
    else
    {
      *this << first;
    }
    if constexpr (sizeof...(args) > 0)
    {
      *this << ", ";
      trace(std::forward<Args>(args)...);
    }
  }

  template <typename FT, typename FF, typename... Args>
  auto operator()(FT&& trace_func, FF&& func, Args&&... args)
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

 protected:
  /** Used as line buffer for writing the trace. */
  std::stringstream d_trace;

  /** Indicates whether trace should be printed to stdout. */
  bool d_print_trace;

  /** ID counter. */
  uint64_t d_id = 0;

  TData& d_data;
};

template <class TData, typename T>
Tracer<TData>&
operator<<(Tracer<TData>& tracer, T x)
{
  tracer.get_trace() << x;
  return tracer;
}

template <class TData>
Tracer<TData>&
operator<<(Tracer<TData>& tracer, const char* s)
{
  auto& trace = tracer.get_trace();
  trace << s;

  // Writes and flushes to stdout if '\n' is encountered.
  size_t len = strlen(s);
  if (s[len - 1] == '\n')
  {
    std::cout << trace.str() << std::flush;
    trace.str("");
    trace.clear();
  }
  return tracer;
}

template <class TData>
Tracer<TData>&
operator<<(Tracer<TData>& tracer, bool b)
{
  tracer.get_trace() << std::boolalpha << b;
  return tracer;
}

}  // namespace murxla
#endif
