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
#include "solver/tracer.hpp"

namespace murxla {

namespace cvc5 {

class Cvc5TracerData
{
 public:
  auto& get_term_map() { return d_term_map; }
  auto& get_op_map() { return d_op_map; }
  auto& get_sort_map() { return d_sort_map; }
  auto& get_dt_decl_map() { return d_dt_decl_map; }
  auto& get_dt_sel_map() { return d_dt_sel_map; }
  auto& get_dt_cons_map() { return d_dt_cons_map; }
  auto& get_dt_cons_decl_map() { return d_dt_cons_decl_map; }
  auto& get_dt_map() { return d_dt_map; }

 private:
  std::unordered_map<::cvc5::Term, uint64_t> d_term_map;
  std::unordered_map<::cvc5::Op, uint64_t> d_op_map;
  std::unordered_map<::cvc5::Sort, uint64_t> d_sort_map;
  std::unordered_map<std::string, uint64_t> d_dt_decl_map;
  std::unordered_map<std::string, uint64_t> d_dt_sel_map;
  std::unordered_map<std::string, uint64_t> d_dt_cons_map;
  std::unordered_map<std::string, uint64_t> d_dt_cons_decl_map;
  std::unordered_map<std::string, uint64_t> d_dt_map;
};

}  // namespace cvc5

Tracer<cvc5::Cvc5TracerData>& operator<<(Tracer<cvc5::Cvc5TracerData>& tracer,
                                         const ::cvc5::Term& term);
Tracer<cvc5::Cvc5TracerData>& operator<<(Tracer<cvc5::Cvc5TracerData>& tracer,
                                         const ::cvc5::Op& op);
Tracer<cvc5::Cvc5TracerData>& operator<<(Tracer<cvc5::Cvc5TracerData>& tracer,
                                         const ::cvc5::Sort& sort);
Tracer<cvc5::Cvc5TracerData>& operator<<(Tracer<cvc5::Cvc5TracerData>& tracer,
                                         const ::cvc5::DatatypeDecl& decl);
Tracer<cvc5::Cvc5TracerData>& operator<<(
    Tracer<cvc5::Cvc5TracerData>& tracer,
    const ::cvc5::DatatypeConstructor& cons);
Tracer<cvc5::Cvc5TracerData>& operator<<(
    Tracer<cvc5::Cvc5TracerData>& tracer,
    const ::cvc5::DatatypeConstructorDecl& decl);
Tracer<cvc5::Cvc5TracerData>& operator<<(Tracer<cvc5::Cvc5TracerData>& tracer,
                                         const ::cvc5::DatatypeSelector& sel);
Tracer<cvc5::Cvc5TracerData>& operator<<(Tracer<cvc5::Cvc5TracerData>& tracer,
                                         const ::cvc5::Datatype& dt);
Tracer<cvc5::Cvc5TracerData>& operator<<(Tracer<cvc5::Cvc5TracerData>& tracer,
                                         const ::cvc5::RoundingMode& m);
Tracer<cvc5::Cvc5TracerData>& operator<<(
    Tracer<cvc5::Cvc5TracerData>& tracer,
    const ::cvc5::modes::BlockModelsMode& m);

}  // namespace murxla

#endif
#endif
