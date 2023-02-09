/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifdef MURXLA_USE_BITWUZLA

#include "bitwuzla_solver.hpp"

#include <bitset>
#include <cassert>
#include <cstdlib>
#include <string>

#include "action.hpp"
#include "config.hpp"
#include "except.hpp"
#include "solver/bitwuzla/profile.hpp"
#include "solver_option.hpp"
#include "theory.hpp"
#include "util.hpp"

namespace murxla {
namespace bitwuzla {

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

const ::bitwuzla::Sort&
BitwuzlaSort::get_bitwuzla_sort(Sort sort)
{
  return checked_cast<BitwuzlaSort*>(sort.get())->d_sort;
}

std::vector<Sort>
BitwuzlaSort::bitwuzla_sorts_to_sorts(
    const std::vector<::bitwuzla::Sort>& sorts)
{
  std::vector<Sort> res;
  for (auto& sort : sorts)
  {
    res.push_back(std::shared_ptr<BitwuzlaSort>(new BitwuzlaSort(sort)));
  }
  return res;
}

BitwuzlaSort::BitwuzlaSort(const ::bitwuzla::Sort& sort) : d_sort(sort) {}

BitwuzlaSort::~BitwuzlaSort() {}

size_t
BitwuzlaSort::hash() const
{
  return std::hash<::bitwuzla::Sort>{}(d_sort);
}

std::string
BitwuzlaSort::to_string() const
{
  return d_sort.str();
}

bool
BitwuzlaSort::equals(const Sort& other) const
{
  BitwuzlaSort* bzla_sort = checked_cast<BitwuzlaSort*>(other.get());
  if (bzla_sort)
  {
    return d_sort == bzla_sort->d_sort;
  }
  return false;
}

bool
BitwuzlaSort::is_array() const
{
  return d_sort.is_array();
}

bool
BitwuzlaSort::is_bool() const
{
  return d_sort == ::bitwuzla::mk_bool_sort() && d_kind == SORT_BOOL;
}

//! [docs-bitwuzla-sort-is_bv start]
bool
BitwuzlaSort::is_bv() const
{
  return d_sort.is_bv();
}
//! [docs-bitwuzla-sort-is_bv end]

bool
BitwuzlaSort::is_fp() const
{
  return d_sort.is_fp();
}

bool
BitwuzlaSort::is_fun() const
{
  return d_sort.is_fun();
}

bool
BitwuzlaSort::is_rm() const
{
  return d_sort.is_rm();
}

uint32_t
BitwuzlaSort::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = static_cast<uint32_t>(d_sort.bv_size());
  MURXLA_TEST(res);
  return res;
}

uint32_t
BitwuzlaSort::get_fp_exp_size() const
{
  assert(is_fp());
  uint32_t res = static_cast<uint32_t>(d_sort.fp_exp_size());
  MURXLA_TEST(res);
  return res;
}

uint32_t
BitwuzlaSort::get_fp_sig_size() const
{
  assert(is_fp());
  uint32_t res = static_cast<uint32_t>(d_sort.fp_sig_size());
  MURXLA_TEST(res);
  return res;
}

Sort
BitwuzlaSort::get_array_index_sort() const
{
  assert(is_array());
  const ::bitwuzla::Sort& bzla_res = d_sort.array_index();
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaSort> res(new BitwuzlaSort(bzla_res));
  assert(res);
  return res;
}

Sort
BitwuzlaSort::get_array_element_sort() const
{
  assert(is_array());
  const ::bitwuzla::Sort& bzla_res = d_sort.array_element();
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaSort> res(new BitwuzlaSort(bzla_res));
  assert(res);
  return res;
}

uint32_t
BitwuzlaSort::get_fun_arity() const
{
  assert(is_fun());
  return static_cast<uint32_t>(d_sort.fun_arity());
}

Sort
BitwuzlaSort::get_fun_codomain_sort() const
{
  assert(is_fun());
  const ::bitwuzla::Sort& bzla_res = d_sort.fun_codomain();
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaSort> res(new BitwuzlaSort(bzla_res));
  assert(res);
  return res;
}

std::vector<Sort>
BitwuzlaSort::get_fun_domain_sorts() const
{
  assert(is_fun());
  return bitwuzla_sorts_to_sorts(d_sort.fun_domain());
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm */
/* -------------------------------------------------------------------------- */

std::unordered_map<Op::Kind, ::bitwuzla::Kind>
    BitwuzlaTerm::s_kinds_to_bitwuzla_kinds = {
        /* Special Cases */
        {Op::DISTINCT, ::bitwuzla::Kind::DISTINCT},
        {Op::EQUAL, ::bitwuzla::Kind::EQUAL},
        {Op::ITE, ::bitwuzla::Kind::ITE},

        /* Bool */
        {Op::AND, ::bitwuzla::Kind::AND},
        {Op::OR, ::bitwuzla::Kind::OR},
        {Op::NOT, ::bitwuzla::Kind::NOT},
        {Op::XOR, ::bitwuzla::Kind::XOR},
        {Op::IMPLIES, ::bitwuzla::Kind::IMPLIES},
        {Op::IFF, ::bitwuzla::Kind::IFF},

        /* Arrays */
        {Op::ARRAY_SELECT, ::bitwuzla::Kind::ARRAY_SELECT},
        {Op::ARRAY_STORE, ::bitwuzla::Kind::ARRAY_STORE},

        /* BV */
        {Op::BV_EXTRACT, ::bitwuzla::Kind::BV_EXTRACT},
        {Op::BV_REPEAT, ::bitwuzla::Kind::BV_REPEAT},
        {Op::BV_ROTATE_LEFT, ::bitwuzla::Kind::BV_ROLI},
        {Op::BV_ROTATE_RIGHT, ::bitwuzla::Kind::BV_RORI},
        {Op::BV_SIGN_EXTEND, ::bitwuzla::Kind::BV_SIGN_EXTEND},
        {Op::BV_ZERO_EXTEND, ::bitwuzla::Kind::BV_ZERO_EXTEND},

        {Op::BV_CONCAT, ::bitwuzla::Kind::BV_CONCAT},
        {Op::BV_AND, ::bitwuzla::Kind::BV_AND},
        {Op::BV_OR, ::bitwuzla::Kind::BV_OR},
        {Op::BV_XOR, ::bitwuzla::Kind::BV_XOR},
        {Op::BV_MULT, ::bitwuzla::Kind::BV_MUL},
        {Op::BV_ADD, ::bitwuzla::Kind::BV_ADD},
        {Op::BV_NOT, ::bitwuzla::Kind::BV_NOT},
        {Op::BV_NEG, ::bitwuzla::Kind::BV_NEG},
        {Op::BV_NAND, ::bitwuzla::Kind::BV_NAND},
        {Op::BV_NOR, ::bitwuzla::Kind::BV_NOR},
        {Op::BV_XNOR, ::bitwuzla::Kind::BV_XNOR},
        {Op::BV_COMP, ::bitwuzla::Kind::BV_COMP},
        {Op::BV_SUB, ::bitwuzla::Kind::BV_SUB},
        {Op::BV_UDIV, ::bitwuzla::Kind::BV_UDIV},
        {Op::BV_UREM, ::bitwuzla::Kind::BV_UREM},
        {Op::BV_UREM, ::bitwuzla::Kind::BV_UREM},
        {Op::BV_SDIV, ::bitwuzla::Kind::BV_SDIV},
        {Op::BV_SREM, ::bitwuzla::Kind::BV_SREM},
        {Op::BV_SMOD, ::bitwuzla::Kind::BV_SMOD},
        {Op::BV_SHL, ::bitwuzla::Kind::BV_SHL},
        {Op::BV_LSHR, ::bitwuzla::Kind::BV_SHR},
        {Op::BV_ASHR, ::bitwuzla::Kind::BV_ASHR},
        {Op::BV_ULT, ::bitwuzla::Kind::BV_ULT},
        {Op::BV_ULE, ::bitwuzla::Kind::BV_ULE},
        {Op::BV_UGT, ::bitwuzla::Kind::BV_UGT},
        {Op::BV_UGE, ::bitwuzla::Kind::BV_UGE},
        {Op::BV_SLT, ::bitwuzla::Kind::BV_SLT},
        {Op::BV_SLE, ::bitwuzla::Kind::BV_SLE},
        {Op::BV_SGT, ::bitwuzla::Kind::BV_SGT},
        {Op::BV_SGE, ::bitwuzla::Kind::BV_SGE},

        /* FP */
        {Op::FP_ABS, ::bitwuzla::Kind::FP_ABS},
        {Op::FP_ADD, ::bitwuzla::Kind::FP_ADD},
        {Op::FP_DIV, ::bitwuzla::Kind::FP_DIV},
        {Op::FP_EQ, ::bitwuzla::Kind::FP_EQUAL},
        {Op::FP_FMA, ::bitwuzla::Kind::FP_FMA},
        {Op::FP_FP, ::bitwuzla::Kind::FP_FP},
        {Op::FP_IS_NORMAL, ::bitwuzla::Kind::FP_IS_NORMAL},
        {Op::FP_IS_SUBNORMAL, ::bitwuzla::Kind::FP_IS_SUBNORMAL},
        {Op::FP_IS_INF, ::bitwuzla::Kind::FP_IS_INF},
        {Op::FP_IS_NAN, ::bitwuzla::Kind::FP_IS_NAN},
        {Op::FP_IS_NEG, ::bitwuzla::Kind::FP_IS_NEG},
        {Op::FP_IS_POS, ::bitwuzla::Kind::FP_IS_POS},
        {Op::FP_IS_ZERO, ::bitwuzla::Kind::FP_IS_ZERO},
        {Op::FP_LT, ::bitwuzla::Kind::FP_LT},
        {Op::FP_LEQ, ::bitwuzla::Kind::FP_LEQ},
        {Op::FP_GT, ::bitwuzla::Kind::FP_GT},
        {Op::FP_GEQ, ::bitwuzla::Kind::FP_GEQ},
        {Op::FP_MAX, ::bitwuzla::Kind::FP_MAX},
        {Op::FP_MIN, ::bitwuzla::Kind::FP_MIN},
        {Op::FP_MUL, ::bitwuzla::Kind::FP_MUL},
        {Op::FP_NEG, ::bitwuzla::Kind::FP_NEG},
        {Op::FP_REM, ::bitwuzla::Kind::FP_REM},
        {Op::FP_RTI, ::bitwuzla::Kind::FP_RTI},
        {Op::FP_SQRT, ::bitwuzla::Kind::FP_SQRT},
        {Op::FP_SUB, ::bitwuzla::Kind::FP_SUB},
        {Op::FP_TO_FP_FROM_BV, ::bitwuzla::Kind::FP_TO_FP_FROM_BV},
        {Op::FP_TO_FP_FROM_SBV, ::bitwuzla::Kind::FP_TO_FP_FROM_SBV},
        {Op::FP_TO_FP_FROM_FP, ::bitwuzla::Kind::FP_TO_FP_FROM_FP},
        {Op::FP_TO_FP_FROM_UBV, ::bitwuzla::Kind::FP_TO_FP_FROM_UBV},
        {Op::FP_TO_SBV, ::bitwuzla::Kind::FP_TO_SBV},
        {Op::FP_TO_UBV, ::bitwuzla::Kind::FP_TO_UBV},

        /* Quantifiers */
        {Op::FORALL, ::bitwuzla::Kind::FORALL},
        {Op::EXISTS, ::bitwuzla::Kind::EXISTS},

        /* UF */
        {Op::UF_APPLY, ::bitwuzla::Kind::APPLY},

        /* Solver-specific operators */
        {OP_BV_DEC, ::bitwuzla::Kind::BV_DEC},
        {OP_BV_INC, ::bitwuzla::Kind::BV_INC},
        {OP_BV_ROL, ::bitwuzla::Kind::BV_ROL},
        {OP_BV_ROR, ::bitwuzla::Kind::BV_ROR},
        {OP_BV_REDAND, ::bitwuzla::Kind::BV_REDAND},
        {OP_BV_REDOR, ::bitwuzla::Kind::BV_REDOR},
        {OP_BV_REDXOR, ::bitwuzla::Kind::BV_REDXOR},
        {OP_BV_UADDO, ::bitwuzla::Kind::BV_UADD_OVERFLOW},
        {OP_BV_SADDO, ::bitwuzla::Kind::BV_SADD_OVERFLOW},
        {OP_BV_UMULO, ::bitwuzla::Kind::BV_UMUL_OVERFLOW},
        {OP_BV_SMULO, ::bitwuzla::Kind::BV_SMUL_OVERFLOW},
        {OP_BV_USUBO, ::bitwuzla::Kind::BV_USUB_OVERFLOW},
        {OP_BV_SSUBO, ::bitwuzla::Kind::BV_SSUB_OVERFLOW},
        {OP_BV_SDIVO, ::bitwuzla::Kind::BV_SDIV_OVERFLOW},
        {OP_IFF, ::bitwuzla::Kind::IFF},
        // Note: OP_FP_TO_FP_FROM_REAL needs special treatment, not a real
        // Bitwuzla
        //       kind
};

std::unordered_map<::bitwuzla::Kind, Op::Kind>
    BitwuzlaTerm::s_bitwuzla_kinds_to_kinds = {
        /* Leaf Kinds */
        {::bitwuzla::Kind::CONSTANT, Op::CONSTANT},
        {::bitwuzla::Kind::CONST_ARRAY, Op::CONST_ARRAY},
        {::bitwuzla::Kind::VALUE, Op::VALUE},
        {::bitwuzla::Kind::VARIABLE, Op::VARIABLE},
        {::bitwuzla::Kind::LAMBDA, Op::FUN},

        /* Special Cases */
        {::bitwuzla::Kind::DISTINCT, Op::DISTINCT},
        {::bitwuzla::Kind::EQUAL, Op::EQUAL},
        {::bitwuzla::Kind::ITE, Op::ITE},

        /* Bool */
        {::bitwuzla::Kind::AND, Op::AND},
        {::bitwuzla::Kind::OR, Op::OR},
        {::bitwuzla::Kind::NOT, Op::NOT},
        {::bitwuzla::Kind::XOR, Op::XOR},
        {::bitwuzla::Kind::IMPLIES, Op::IMPLIES},
        {::bitwuzla::Kind::IFF, Op::IFF},

        /* Arrays */
        {::bitwuzla::Kind::ARRAY_SELECT, Op::ARRAY_SELECT},
        {::bitwuzla::Kind::ARRAY_STORE, Op::ARRAY_STORE},

        /* BV */
        {::bitwuzla::Kind::BV_EXTRACT, Op::BV_EXTRACT},
        {::bitwuzla::Kind::BV_REPEAT, Op::BV_REPEAT},
        {::bitwuzla::Kind::BV_ROLI, Op::BV_ROTATE_LEFT},
        {::bitwuzla::Kind::BV_RORI, Op::BV_ROTATE_RIGHT},
        {::bitwuzla::Kind::BV_SIGN_EXTEND, Op::BV_SIGN_EXTEND},
        {::bitwuzla::Kind::BV_ZERO_EXTEND, Op::BV_ZERO_EXTEND},

        {::bitwuzla::Kind::BV_CONCAT, Op::BV_CONCAT},
        {::bitwuzla::Kind::BV_AND, Op::BV_AND},
        {::bitwuzla::Kind::BV_OR, Op::BV_OR},
        {::bitwuzla::Kind::BV_XOR, Op::BV_XOR},
        {::bitwuzla::Kind::BV_MUL, Op::BV_MULT},
        {::bitwuzla::Kind::BV_ADD, Op::BV_ADD},
        {::bitwuzla::Kind::BV_NOT, Op::BV_NOT},
        {::bitwuzla::Kind::BV_NEG, Op::BV_NEG},
        {::bitwuzla::Kind::BV_NAND, Op::BV_NAND},
        {::bitwuzla::Kind::BV_NOR, Op::BV_NOR},
        {::bitwuzla::Kind::BV_XNOR, Op::BV_XNOR},
        {::bitwuzla::Kind::BV_COMP, Op::BV_COMP},
        {::bitwuzla::Kind::BV_SUB, Op::BV_SUB},
        {::bitwuzla::Kind::BV_UDIV, Op::BV_UDIV},
        {::bitwuzla::Kind::BV_UREM, Op::BV_UREM},
        {::bitwuzla::Kind::BV_UREM, Op::BV_UREM},
        {::bitwuzla::Kind::BV_SDIV, Op::BV_SDIV},
        {::bitwuzla::Kind::BV_SREM, Op::BV_SREM},
        {::bitwuzla::Kind::BV_SMOD, Op::BV_SMOD},
        {::bitwuzla::Kind::BV_SHL, Op::BV_SHL},
        {::bitwuzla::Kind::BV_SHR, Op::BV_LSHR},
        {::bitwuzla::Kind::BV_ASHR, Op::BV_ASHR},
        {::bitwuzla::Kind::BV_ULT, Op::BV_ULT},
        {::bitwuzla::Kind::BV_ULE, Op::BV_ULE},
        {::bitwuzla::Kind::BV_UGT, Op::BV_UGT},
        {::bitwuzla::Kind::BV_UGE, Op::BV_UGE},
        {::bitwuzla::Kind::BV_SLT, Op::BV_SLT},
        {::bitwuzla::Kind::BV_SLE, Op::BV_SLE},
        {::bitwuzla::Kind::BV_SGT, Op::BV_SGT},
        {::bitwuzla::Kind::BV_SGE, Op::BV_SGE},

        /* FP */
        {::bitwuzla::Kind::FP_ABS, Op::FP_ABS},
        {::bitwuzla::Kind::FP_ADD, Op::FP_ADD},
        {::bitwuzla::Kind::FP_DIV, Op::FP_DIV},
        {::bitwuzla::Kind::FP_EQUAL, Op::FP_EQ},
        {::bitwuzla::Kind::FP_FMA, Op::FP_FMA},
        {::bitwuzla::Kind::FP_FP, Op::FP_FP},
        {::bitwuzla::Kind::FP_IS_NORMAL, Op::FP_IS_NORMAL},
        {::bitwuzla::Kind::FP_IS_SUBNORMAL, Op::FP_IS_SUBNORMAL},
        {::bitwuzla::Kind::FP_IS_INF, Op::FP_IS_INF},
        {::bitwuzla::Kind::FP_IS_NAN, Op::FP_IS_NAN},
        {::bitwuzla::Kind::FP_IS_NEG, Op::FP_IS_NEG},
        {::bitwuzla::Kind::FP_IS_POS, Op::FP_IS_POS},
        {::bitwuzla::Kind::FP_IS_ZERO, Op::FP_IS_ZERO},
        {::bitwuzla::Kind::FP_LT, Op::FP_LT},
        {::bitwuzla::Kind::FP_LEQ, Op::FP_LEQ},
        {::bitwuzla::Kind::FP_GT, Op::FP_GT},
        {::bitwuzla::Kind::FP_GEQ, Op::FP_GEQ},
        {::bitwuzla::Kind::FP_MAX, Op::FP_MAX},
        {::bitwuzla::Kind::FP_MIN, Op::FP_MIN},
        {::bitwuzla::Kind::FP_MUL, Op::FP_MUL},
        {::bitwuzla::Kind::FP_NEG, Op::FP_NEG},
        {::bitwuzla::Kind::FP_REM, Op::FP_REM},
        {::bitwuzla::Kind::FP_RTI, Op::FP_RTI},
        {::bitwuzla::Kind::FP_SQRT, Op::FP_SQRT},
        {::bitwuzla::Kind::FP_SUB, Op::FP_SUB},
        {::bitwuzla::Kind::FP_TO_FP_FROM_BV, Op::FP_TO_FP_FROM_BV},
        {::bitwuzla::Kind::FP_TO_FP_FROM_SBV, Op::FP_TO_FP_FROM_SBV},
        {::bitwuzla::Kind::FP_TO_FP_FROM_FP, Op::FP_TO_FP_FROM_FP},
        {::bitwuzla::Kind::FP_TO_FP_FROM_UBV, Op::FP_TO_FP_FROM_UBV},
        {::bitwuzla::Kind::FP_TO_SBV, Op::FP_TO_SBV},
        {::bitwuzla::Kind::FP_TO_UBV, Op::FP_TO_UBV},

        /* Quantifiers */
        {::bitwuzla::Kind::FORALL, Op::FORALL},
        {::bitwuzla::Kind::EXISTS, Op::EXISTS},

        /* UF */
        {::bitwuzla::Kind::APPLY, Op::UF_APPLY},

        /* Solver-specific operators */
        {::bitwuzla::Kind::BV_DEC, BitwuzlaTerm::OP_BV_DEC},
        {::bitwuzla::Kind::BV_INC, BitwuzlaTerm::OP_BV_INC},
        {::bitwuzla::Kind::BV_ROL, BitwuzlaTerm::OP_BV_ROL},
        {::bitwuzla::Kind::BV_ROR, BitwuzlaTerm::OP_BV_ROR},
        {::bitwuzla::Kind::BV_REDAND, BitwuzlaTerm::OP_BV_REDAND},
        {::bitwuzla::Kind::BV_REDOR, BitwuzlaTerm::OP_BV_REDOR},
        {::bitwuzla::Kind::BV_REDXOR, BitwuzlaTerm::OP_BV_REDXOR},
        {::bitwuzla::Kind::BV_UADD_OVERFLOW, BitwuzlaTerm::OP_BV_UADDO},
        {::bitwuzla::Kind::BV_SADD_OVERFLOW, BitwuzlaTerm::OP_BV_SADDO},
        {::bitwuzla::Kind::BV_UMUL_OVERFLOW, BitwuzlaTerm::OP_BV_UMULO},
        {::bitwuzla::Kind::BV_SMUL_OVERFLOW, BitwuzlaTerm::OP_BV_SMULO},
        {::bitwuzla::Kind::BV_USUB_OVERFLOW, BitwuzlaTerm::OP_BV_USUBO},
        {::bitwuzla::Kind::BV_SSUB_OVERFLOW, BitwuzlaTerm::OP_BV_SSUBO},
        {::bitwuzla::Kind::BV_SDIV_OVERFLOW, BitwuzlaTerm::OP_BV_SDIVO},
        {::bitwuzla::Kind::IFF, BitwuzlaTerm::OP_IFF},
};

const ::bitwuzla::Term&
BitwuzlaTerm::get_bitwuzla_term(Term term)
{
  return checked_cast<BitwuzlaTerm*>(term.get())->d_term;
}

std::vector<Term>
BitwuzlaTerm::bitwuzla_terms_to_terms(
    const std::vector<::bitwuzla::Term>& terms)
{
  std::vector<Term> res;
  for (const auto& t : terms)
  {
    res.push_back(std::shared_ptr<BitwuzlaTerm>(new BitwuzlaTerm(t)));
  }
  return res;
}

std::vector<::bitwuzla::Term>
BitwuzlaTerm::terms_to_bitwuzla_terms(const std::vector<Term>& terms)
{
  std::vector<::bitwuzla::Term> res;
  for (auto& t : terms)
  {
    res.push_back(BitwuzlaTerm::get_bitwuzla_term(t));
  }
  return res;
}

BitwuzlaTerm::BitwuzlaTerm(const ::bitwuzla::Term& term) : d_term(term) {}

BitwuzlaTerm::~BitwuzlaTerm() {}

size_t
BitwuzlaTerm::hash() const
{
  return std::hash<::bitwuzla::Term>{}(d_term);
}

bool
BitwuzlaTerm::equals(const Term& other) const
{
  BitwuzlaTerm* bzla_term = checked_cast<BitwuzlaTerm*>(other.get());
  return d_term == bzla_term->d_term;
}

std::string
BitwuzlaTerm::to_string() const
{
  return d_term.str();
}

bool
BitwuzlaTerm::is_array() const
{
  return d_term.sort().is_array();
}

bool
BitwuzlaTerm::is_bv() const
{
  return d_term.sort().is_bv();
}

bool
BitwuzlaTerm::is_fp() const
{
  return d_term.sort().is_fp();
}

bool
BitwuzlaTerm::is_fun() const
{
  return d_term.sort().is_fun();
}

bool
BitwuzlaTerm::is_rm() const
{
  return d_term.sort().is_rm();
}

bool
BitwuzlaTerm::is_bool_value() const
{
  return d_term.is_value() && d_term.sort().is_bool();
}

bool
BitwuzlaTerm::is_bv_value() const
{
  return d_term.is_value() && d_term.sort().is_bv();
}

bool
BitwuzlaTerm::is_fp_value() const
{
  return d_term.is_value() && d_term.sort().is_fp();
}

bool
BitwuzlaTerm::is_rm_value() const
{
  return d_term.is_value() && d_term.sort().is_rm();
}

bool
BitwuzlaTerm::is_special_value(const AbsTerm::SpecialValueKind& kind) const
{
  if (kind == AbsTerm::SPECIAL_VALUE_BV_ZERO)
  {
    return d_term.is_bv_value_zero();
  }
  else if (kind == SPECIAL_VALUE_BV_ONE)
  {
    return d_term.is_bv_value_one();
  }
  else if (kind == SPECIAL_VALUE_BV_ONES)
  {
    return d_term.is_bv_value_ones();
  }
  else if (kind == SPECIAL_VALUE_BV_MIN_SIGNED)
  {
    return d_term.is_bv_value_min_signed();
  }
  else if (kind == SPECIAL_VALUE_BV_MAX_SIGNED)
  {
    return d_term.is_bv_value_max_signed();
  }
  else if (kind == SPECIAL_VALUE_FP_NAN)
  {
    return d_term.is_fp_value_nan();
  }
  else if (kind == SPECIAL_VALUE_FP_POS_INF)
  {
    return d_term.is_fp_value_pos_inf();
  }
  else if (kind == SPECIAL_VALUE_FP_NEG_INF)
  {
    return d_term.is_fp_value_neg_inf();
  }
  else if (kind == SPECIAL_VALUE_FP_POS_ZERO)
  {
    return d_term.is_fp_value_pos_zero();
  }
  else if (kind == SPECIAL_VALUE_FP_NEG_ZERO)
  {
    return d_term.is_fp_value_neg_zero();
  }
  else if (kind == SPECIAL_VALUE_RM_RNA)
  {
    return d_term.is_rm_value_rna();
  }
  else if (kind == SPECIAL_VALUE_RM_RNE)
  {
    return d_term.is_rm_value_rne();
  }
  else if (kind == SPECIAL_VALUE_RM_RTN)
  {
    return d_term.is_rm_value_rtn();
  }
  else if (kind == SPECIAL_VALUE_RM_RTP)
  {
    return d_term.is_rm_value_rtp();
  }
  else if (kind == SPECIAL_VALUE_RM_RTZ)
  {
    return d_term.is_rm_value_rtz();
  }
  return AbsTerm::is_special_value(kind);
}

bool
BitwuzlaTerm::is_const() const
{
  return d_term.is_const();
}

bool
BitwuzlaTerm::is_value() const
{
  return d_term.is_value();
}

bool
BitwuzlaTerm::is_var() const
{
  return d_term.is_variable();
}

const Op::Kind&
BitwuzlaTerm::get_kind() const
{
  ::bitwuzla::Kind bzla_kind = d_term.kind();
  return s_bitwuzla_kinds_to_kinds.at(bzla_kind);
}

//! [docs-bitwuzla-term-get_children start]
std::vector<Term>
BitwuzlaTerm::get_children() const
{
  return bitwuzla_terms_to_terms(d_term.children());
}
//! [docs-bitwuzla-term-get_children end]

bool
BitwuzlaTerm::is_indexed() const
{
  return d_term.num_indices() > 0;
}

size_t
BitwuzlaTerm::get_num_indices() const
{
  return d_term.num_indices();
}

std::vector<std::string>
BitwuzlaTerm::get_indices() const
{
  assert(is_indexed());
  std::vector<std::string> res;
  std::vector<uint64_t> bzla_res = d_term.indices();
  MURXLA_TEST(bzla_res.size());
  for (uint64_t idx : bzla_res)
  {
    res.push_back(std::to_string(idx));
  }
  return res;
}

uint32_t
BitwuzlaTerm::get_bv_size() const
{
  assert(is_bv());
  return static_cast<uint32_t>(d_term.sort().bv_size());
}

uint32_t
BitwuzlaTerm::get_fp_exp_size() const
{
  assert(is_fp());
  return static_cast<uint32_t>(d_term.sort().fp_exp_size());
}

uint32_t
BitwuzlaTerm::get_fp_sig_size() const
{
  assert(is_fp());
  return static_cast<uint32_t>(d_term.sort().fp_sig_size());
}

Sort
BitwuzlaTerm::get_array_index_sort() const
{
  assert(is_array());
  const ::bitwuzla::Sort& bzla_res = d_term.sort().array_index();
  return std::shared_ptr<BitwuzlaSort>(new BitwuzlaSort(bzla_res));
}

Sort
BitwuzlaTerm::get_array_element_sort() const
{
  assert(is_array());
  const ::bitwuzla::Sort& bzla_res = d_term.sort().array_element();
  return std::shared_ptr<BitwuzlaSort>(new BitwuzlaSort(bzla_res));
}

uint32_t
BitwuzlaTerm::get_fun_arity() const
{
  assert(is_fun());
  return static_cast<uint32_t>(d_term.sort().fun_arity());
}

Sort
BitwuzlaTerm::get_fun_codomain_sort() const
{
  assert(is_fun());
  const ::bitwuzla::Sort& bzla_res = d_term.sort().fun_codomain();
  return std::shared_ptr<BitwuzlaSort>(new BitwuzlaSort(bzla_res));
}

std::vector<Sort>
BitwuzlaTerm::get_fun_domain_sorts() const
{
  assert(is_fun());
  return BitwuzlaSort::bitwuzla_sorts_to_sorts(d_term.sort().fun_domain());
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaSolver */
/* -------------------------------------------------------------------------- */

BitwuzlaSolver::~BitwuzlaSolver()
{
  if (d_solver)
  {
    d_solver.reset(nullptr);
  }
}

void
BitwuzlaSolver::new_solver()
{
  assert(d_solver == nullptr);

  // Initialize Bitwuzla options
  d_options.reset(new ::bitwuzla::Options());
  if (d_option_name_to_enum.empty())
  {
    for (size_t i = 0, n = static_cast<size_t>(::bitwuzla::Option::NUM_OPTS);
         i < n;
         ++i)
    {
      ::bitwuzla::Option opt = static_cast<::bitwuzla::Option>(i);
      ::bitwuzla::OptionInfo info(*d_options, opt);
      d_option_name_to_enum.emplace(info.lng, opt);
    }
  }
  // we cannot initialize the Bitwuzla object yet since it requires finalized
  // options
}

void
BitwuzlaSolver::delete_solver()
{
  d_solver.reset(nullptr);
}

::bitwuzla::Bitwuzla*
BitwuzlaSolver::get_solver()
{
  return d_solver.get();
}

void
BitwuzlaSolver::init_solver()
{
  if (d_solver == nullptr)
  {
    assert(d_options != nullptr);
    d_solver.reset(new ::bitwuzla::Bitwuzla(*d_options));
  }
}

bool
BitwuzlaSolver::is_initialized() const
{
  return d_options != nullptr;
}

const std::string
BitwuzlaSolver::get_name() const
{
  return "Bitwuzla";
}

const std::string
BitwuzlaSolver::get_profile() const
{
  return s_profile;
}

Sort
BitwuzlaSolver::mk_sort(SortKind kind)
{
  MURXLA_CHECK_CONFIG(kind == SORT_BOOL || kind == SORT_RM)
      << "unsupported sort kind '" << kind
      << "' as argument to BitwuzlaSolver::mk_sort, expected '" << SORT_BOOL
      << "' or '" << SORT_RM << "'";

  ::bitwuzla::Sort bzla_res =
      kind == SORT_BOOL ? ::bitwuzla::mk_bool_sort() : ::bitwuzla::mk_rm_sort();
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaSort> res(new BitwuzlaSort(bzla_res));
  assert(res);
  return res;
}

Sort
BitwuzlaSolver::mk_sort(SortKind kind, uint32_t size)
{
  MURXLA_CHECK_CONFIG(kind == SORT_BV)
      << "unsupported sort kind '" << kind
      << "' as argument to BitwuzlaSolver::mk_sort, expected '" << SORT_BV
      << "'";

  ::bitwuzla::Sort bzla_res = ::bitwuzla::mk_bv_sort(size);
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaSort> res(new BitwuzlaSort(bzla_res));
  assert(res);
  return res;
}

Sort
BitwuzlaSolver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  MURXLA_CHECK_CONFIG(kind == SORT_FP)
      << "unsupported sort kind '" << kind
      << "' as argument to BitwuzlaSolver::mk_sort, expected '" << SORT_FP
      << "'";

  ::bitwuzla::Sort bzla_res = ::bitwuzla::mk_fp_sort(esize, ssize);
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaSort> res(new BitwuzlaSort(bzla_res));
  assert(res);
  return res;
}

Sort
BitwuzlaSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  ::bitwuzla::Sort bzla_res;

  switch (kind)
  {
    case SORT_ARRAY:
      bzla_res =
          ::bitwuzla::mk_array_sort(BitwuzlaSort::get_bitwuzla_sort(sorts[0]),
                                    BitwuzlaSort::get_bitwuzla_sort(sorts[1]));
      break;

    case SORT_FUN:
    {
      ::bitwuzla::Sort codomain = BitwuzlaSort::get_bitwuzla_sort(sorts.back());
      std::vector<::bitwuzla::Sort> domain;
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        domain.push_back(BitwuzlaSort::get_bitwuzla_sort(*it));
      }
      bzla_res = ::bitwuzla::mk_fun_sort(domain, codomain);
      break;
    }

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unsupported sort kind '" << kind
          << "' as argument to BitwuzlaSolver::mk_sort, expected '"
          << SORT_ARRAY << "' or '" << SORT_FUN << "'";
  }
  std::shared_ptr<BitwuzlaSort> res(new BitwuzlaSort(bzla_res));
  MURXLA_TEST(!bzla_res.is_null());
  assert(res);
  return res;
}

Term
BitwuzlaSolver::mk_var(Sort sort, const std::string& name)
{
  std::stringstream ss;
  std::string symbol;

  /* Make sure that symbol is unique. */
  if (!name.empty())
  {
    ss << "sym" << d_num_symbols << "@" << name;
    ++d_num_symbols;
    symbol = ss.str();
  }

  ::bitwuzla::Term bzla_res =
      ::bitwuzla::mk_var(BitwuzlaSort::get_bitwuzla_sort(sort), symbol);
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaTerm> res(new BitwuzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BitwuzlaSolver::mk_const(Sort sort, const std::string& name)
{
  std::stringstream ss;
  std::string symbol;

  /* Make sure that symbol is unique. */
  if (!name.empty())
  {
    ss << "sym" << d_num_symbols << "@" << name;
    ++d_num_symbols;
    symbol = ss.str();
  }

  ::bitwuzla::Term bzla_res =
      ::bitwuzla::mk_const(BitwuzlaSort::get_bitwuzla_sort(sort), symbol);
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaTerm> res(new BitwuzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BitwuzlaSolver::mk_fun(const std::string& name,
                       const std::vector<Term>& args,
                       Term body)
{
  std::vector<::bitwuzla::Term> bzla_args =
      BitwuzlaTerm::terms_to_bitwuzla_terms(args);
  bzla_args.push_back(BitwuzlaTerm::get_bitwuzla_term(body));

  ::bitwuzla::Term bzla_res =
      ::bitwuzla::mk_term(::bitwuzla::Kind::LAMBDA, bzla_args, {});
  // bitwuzla_term_set_symbol(bzla_res, name.c_str());
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaTerm> res(new BitwuzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BitwuzlaSolver::mk_value(Sort sort, bool value)
{
  MURXLA_CHECK_CONFIG(sort->is_bool())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BitwuzlaSolver::mk_value, expected Boolean sort";

  ::bitwuzla::Term bzla_res =
      value ? ::bitwuzla::mk_true() : ::bitwuzla::mk_false();
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaTerm> res(new BitwuzlaTerm(bzla_res));
  assert(res);
  return res;
}

::bitwuzla::Term
BitwuzlaSolver::mk_value_bv_uint64(Sort sort, uint64_t value)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BitwuzlaSolver::mk_value, expected bit-vector sort";

  const ::bitwuzla::Sort& bzla_sort = BitwuzlaSort::get_bitwuzla_sort(sort);
  ::bitwuzla::Term bzla_res = ::bitwuzla::mk_bv_value_uint64(bzla_sort, value);
  MURXLA_TEST(!bzla_res.is_null());
  return bzla_res;
}

::bitwuzla::Term
BitwuzlaSolver::mk_value_bv_int64(Sort sort, int64_t value)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BitwuzlaSolver::mk_value, expected bit-vector sort";

  const ::bitwuzla::Sort& bzla_sort = BitwuzlaSort::get_bitwuzla_sort(sort);
  ::bitwuzla::Term bzla_res = ::bitwuzla::mk_bv_value_int64(bzla_sort, value);
  MURXLA_TEST(!bzla_res.is_null());
  return bzla_res;
}

Term
BitwuzlaSolver::mk_value(Sort sort, const std::string& value)
{
  MURXLA_CHECK_CONFIG(sort->is_fp())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BitwuzlaSolver::mk_value, expected floating-point "
         "sort";

  uint32_t ew = sort->get_fp_exp_size();
  uint32_t sw = sort->get_fp_sig_size();
  assert(value.size() == ew + sw);

  ::bitwuzla::Sort bzla_sort_1 = ::bitwuzla::mk_bv_sort(1);
  ::bitwuzla::Sort bzla_sort_e = ::bitwuzla::mk_bv_sort(ew);
  ::bitwuzla::Sort bzla_sort_s = ::bitwuzla::mk_bv_sort(sw - 1);
  ::bitwuzla::Term bzla_sign =
      ::bitwuzla::mk_bv_value(bzla_sort_1, value.substr(0, 1), 2);
  ::bitwuzla::Term bzla_exp =
      ::bitwuzla::mk_bv_value(bzla_sort_e, value.substr(1, ew).c_str(), 2);
  ::bitwuzla::Term bzla_sig =
      ::bitwuzla::mk_bv_value(bzla_sort_s, value.substr(1 + ew).c_str(), 2);

  ::bitwuzla::Term bzla_res =
      ::bitwuzla::mk_fp_value(bzla_sign, bzla_exp, bzla_sig);
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaTerm> res(new BitwuzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BitwuzlaSolver::mk_value(Sort sort, const std::string& value, Base base)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BitwuzlaSolver::mk_value, expected bit-vector sort";

  ::bitwuzla::Term bzla_res;
  ::bitwuzla::Sort bzla_sort = BitwuzlaSort::get_bitwuzla_sort(sort);
  uint64_t bw                = sort->get_bv_size();
  int32_t ibase              = 2;

  if (base == DEC)
  {
    ibase = 10;
  }
  else if (base == HEX)
  {
    ibase = 16;
  }

  if (bw <= 64 && d_rng.flip_coin())
  {
    if (value[0] == '-')
    {
      bzla_res = mk_value_bv_int64(sort, std::stoll(value, nullptr, ibase));
    }
    else
    {
      bzla_res = mk_value_bv_uint64(sort, std::stoull(value, nullptr, ibase));
    }
  }
  else
  {
    bzla_res =
        ::bitwuzla::mk_bv_value(bzla_sort, value, static_cast<uint8_t>(ibase));
  }
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaTerm> res(new BitwuzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BitwuzlaSolver::mk_special_value(Sort sort,
                                 const AbsTerm::SpecialValueKind& value)
{
  ::bitwuzla::Term bzla_res;
  const ::bitwuzla::Sort& bzla_sort = BitwuzlaSort::get_bitwuzla_sort(sort);
  std::string str;

  switch (sort->get_kind())
  {
    case SORT_BV:
      if (value == AbsTerm::SPECIAL_VALUE_BV_ZERO)
      {
        bzla_res = ::bitwuzla::mk_bv_zero(bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_ONE)
      {
        bzla_res = ::bitwuzla::mk_bv_one(bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_ONES)
      {
        bzla_res = ::bitwuzla::mk_bv_ones(bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED)
      {
        bzla_res = ::bitwuzla::mk_bv_min_signed(bzla_sort);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED);
        bzla_res = ::bitwuzla::mk_bv_max_signed(bzla_sort);
      }
      break;

    case SORT_FP:
    {
      if (value == AbsTerm::SPECIAL_VALUE_FP_POS_INF)
      {
        bzla_res = ::bitwuzla::mk_fp_pos_inf(bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_NEG_INF)
      {
        bzla_res = ::bitwuzla::mk_fp_neg_inf(bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_POS_ZERO)
      {
        bzla_res = ::bitwuzla::mk_fp_pos_zero(bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_NEG_ZERO)
      {
        bzla_res = ::bitwuzla::mk_fp_neg_zero(bzla_sort);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_FP_NAN);
        bzla_res = ::bitwuzla::mk_fp_nan(bzla_sort);
      }
    }
    break;

    case SORT_RM:
      if (value == AbsTerm::SPECIAL_VALUE_RM_RNA)
      {
        bzla_res = ::bitwuzla::mk_rm_value(::bitwuzla::RoundingMode::RNA);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RNE)
      {
        bzla_res = ::bitwuzla::mk_rm_value(::bitwuzla::RoundingMode::RNE);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RTN)
      {
        bzla_res = ::bitwuzla::mk_rm_value(::bitwuzla::RoundingMode::RTN);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RTP)
      {
        bzla_res = ::bitwuzla::mk_rm_value(::bitwuzla::RoundingMode::RTP);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_RM_RTZ);
        bzla_res = ::bitwuzla::mk_rm_value(::bitwuzla::RoundingMode::RTZ);
      }
      break;

    default:
      MURXLA_CHECK_CONFIG(sort->is_bv())
          << "unexpected sort of kind '" << sort->get_kind()
          << "' as argument to BitwuzlaSolver::mk_special_value, expected "
             "bit-vector, floating-point or RoundingMode sort";
  }

  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaTerm> res(new BitwuzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BitwuzlaSolver::mk_term(const Op::Kind& kind,
                        const std::vector<Term>& args,
                        const std::vector<uint32_t>& indices)
{
  MURXLA_CHECK_CONFIG(BitwuzlaTerm::s_kinds_to_bitwuzla_kinds.find(kind)
                          != BitwuzlaTerm::s_kinds_to_bitwuzla_kinds.end()
                      || kind == BitwuzlaTerm::OP_FP_TO_FP_FROM_REAL)
      << "BitwuzlaSolver: operator kind '" << kind << "' not configured";

  std::vector<::bitwuzla::Term> bzla_args =
      BitwuzlaTerm::terms_to_bitwuzla_terms(args);
  std::vector<uint64_t> bzla_indices{indices.begin(), indices.end()};
  std::vector<::bitwuzla::Term> vars;
  ::bitwuzla::Term bzla_res;

  if (kind == BitwuzlaTerm::OP_FP_TO_FP_FROM_REAL)
  {
    /* Bitwuzla only supports a very restricted version of to_fp from Real:
     * only from strings representing real or rational values. */

    const ::bitwuzla::Sort& bzla_sort = bzla_args[1].sort();
    if (d_rng.flip_coin())
    {
      bzla_res = ::bitwuzla::mk_fp_value(
          bzla_sort, bzla_args[0], d_rng.pick_real_string());
    }
    else
    {
      bzla_res = ::bitwuzla::mk_fp_value(
          bzla_sort,
          bzla_args[0],
          d_rng.pick_dec_int_string(
              d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX)),
          d_rng.pick_dec_int_string(
              d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX)));
    }
  }
  else
  {
    bzla_res =
        ::bitwuzla::mk_term(BitwuzlaTerm::s_kinds_to_bitwuzla_kinds.at(kind),
                            bzla_args,
                            bzla_indices);
  }
  MURXLA_TEST(!bzla_res.is_null());
  std::shared_ptr<BitwuzlaTerm> res(new BitwuzlaTerm(bzla_res));
  assert(res);
  return res;
}

Sort
BitwuzlaSolver::get_sort(Term term, SortKind sort_kind)
{
  (void) sort_kind;
  return std::shared_ptr<BitwuzlaSort>(
      new BitwuzlaSort(BitwuzlaTerm::get_bitwuzla_term(term).sort()));
}

void
BitwuzlaSolver::assert_formula(const Term& t)
{
  init_solver();
  d_solver->assert_formula(BitwuzlaTerm::get_bitwuzla_term(t));
}

Solver::Result
BitwuzlaSolver::check_sat()
{
  init_solver();
  ::bitwuzla::Result res = d_solver->check_sat();
  if (res == ::bitwuzla::Result::SAT) return Result::SAT;
  if (res == ::bitwuzla::Result::UNSAT) return Result::UNSAT;
  MURXLA_TEST(res == ::bitwuzla::Result::UNKNOWN);
  return Result::UNKNOWN;
}

Solver::Result
BitwuzlaSolver::check_sat_assuming(const std::vector<Term>& assumptions)
{
  init_solver();
  //::bitwuzla::Result res =
  //:d_solver->check_sat(terms_to_bitwuzla_terms(assumptions));
  // if (res == ::bitwuzla::Result::SAT) return Result::SAT;
  // if (res == ::bitwuzla::Result::UNSAT) return Result::UNSAT;
  // MURXLA_TEST(res == ::bitwuzla::Result::UNKNOWN);
  return Result::UNKNOWN;
}

std::vector<Term>
BitwuzlaSolver::get_unsat_assumptions()
{
  assert(d_solver != nullptr);
  return BitwuzlaTerm::bitwuzla_terms_to_terms(
      d_solver->get_unsat_assumptions());
}

//! [docs-bitwuzla-solver-get_unsat_core start]
std::vector<Term>
BitwuzlaSolver::get_unsat_core()
{
  assert(d_solver != nullptr);
  return BitwuzlaTerm::bitwuzla_terms_to_terms(d_solver->get_unsat_core());
}
//! [docs-bitwuzla-solver-get_unsat_core end]

std::vector<Term>
BitwuzlaSolver::get_value(const std::vector<Term>& terms)
{
  assert(d_solver != nullptr);
  std::vector<Term> res;
  std::vector<::bitwuzla::Term> bzla_res;
  std::vector<::bitwuzla::Term> bzla_terms =
      BitwuzlaTerm::terms_to_bitwuzla_terms(terms);

  for (const ::bitwuzla::Term& t : bzla_terms)
  {
    bzla_res.push_back(d_solver->get_value(t));
  }
  return BitwuzlaTerm::bitwuzla_terms_to_terms(bzla_res);
}

void
BitwuzlaSolver::push(uint32_t n_levels)
{
  init_solver();
  d_solver->push(n_levels);
}

void
BitwuzlaSolver::pop(uint32_t n_levels)
{
  init_solver();
  d_solver->pop(n_levels);
}

void
BitwuzlaSolver::print_model()
{
  init_solver();
  // d_solver->print_model(std::cout, d_rng.flip_coin() ? "btor" : "smt2");
}

void
BitwuzlaSolver::reset()
{
  d_solver.reset(nullptr);
  d_options.reset(nullptr);
  new_solver();
}

void
BitwuzlaSolver::reset_assertions()
{
  /* Bitwuzla does not support this yet */
  assert(false);
}

/* -------------------------------------------------------------------------- */

bool
BitwuzlaSolver::is_unsat_assumption(const Term& t) const
{
  assert(d_solver != nullptr);
  return d_solver->is_unsat_assumption(BitwuzlaTerm::get_bitwuzla_term(t));
}

/* -------------------------------------------------------------------------- */

void
BitwuzlaSolver::set_opt(const std::string& opt, const std::string& value)
{
  if (opt == "produce-unsat-assumptions")
  {
    /* always enabled in Bitwuzla, can not be configured via set_opt */
    return;
  }

  ::bitwuzla::Option bzla_opt;
  if (opt == "produce-models")
  {
    bzla_opt = ::bitwuzla::Option::PRODUCE_MODELS;
  }
  else if (opt == "produce-unsat-cores")
  {
    bzla_opt = ::bitwuzla::Option::PRODUCE_UNSAT_CORES;
  }
  else
  {
    auto it = d_option_name_to_enum.find(opt);
    MURXLA_CHECK_CONFIG(it != d_option_name_to_enum.end())
        << "invalid option name '" << opt;
    bzla_opt = it->second;
  }

  ::bitwuzla::OptionInfo info(*d_options, bzla_opt);

  if (d_options->is_bool(bzla_opt) || d_options->is_numeric(bzla_opt))
  {
    uint32_t val =
        value == "true"
            ? 1
            : (value == "false" ? 0 : static_cast<uint32_t>(std::stoul(value)));
    d_options->set(bzla_opt, val);
    MURXLA_TEST(val == d_options->get(bzla_opt));
  }
  else
  {
    d_options->set(bzla_opt, value);
  }
}

std::string
BitwuzlaSolver::get_option_name_incremental() const
{
  return "incremental";
}

std::string
BitwuzlaSolver::get_option_name_model_gen() const
{
  return "produce-models";
}

std::string
BitwuzlaSolver::get_option_name_unsat_assumptions() const
{
  /* always enabled in Bitwuzla, can not be configured via set_opt */
  return "produce-unsat-assumptions";
}

std::string
BitwuzlaSolver::get_option_name_unsat_cores() const
{
  return "produce-unsat-cores";
}

bool
BitwuzlaSolver::option_incremental_enabled() const
{
  return d_options->get(::bitwuzla::Option::INCREMENTAL);
}

bool
BitwuzlaSolver::option_model_gen_enabled() const
{
  return d_options->get(::bitwuzla::Option::PRODUCE_MODELS);
}

bool
BitwuzlaSolver::option_unsat_assumptions_enabled() const
{
  /* always enabled in Bitwuzla, can not be configured via set_opt */
  return true;
}

bool
BitwuzlaSolver::option_unsat_cores_enabled() const
{
  return d_options->get(::bitwuzla::Option::PRODUCE_UNSAT_CORES);
}

void
BitwuzlaSolver::check_term(Term term)
{
  const ::bitwuzla::Term& bzla_term = BitwuzlaTerm::get_bitwuzla_term(term);
  MURXLA_TEST(!(bzla_term != bzla_term));
  // MURXLA_TEST(bzla_term >= bzla_term);
  // MURXLA_TEST(bzla_term <= bzla_term);
  // MURXLA_TEST(!(bzla_term > bzla_term));
  // MURXLA_TEST(!(bzla_term < bzla_term));
  MURXLA_TEST(bzla_term.symbol() == std::nullopt
              || bzla_term.symbol() == std::nullopt);
  MURXLA_TEST(term->is_indexed() || term->get_num_indices() == 0);
  MURXLA_TEST(bzla_term.id() != 0);
}

/* -------------------------------------------------------------------------- */
/* OpKindManager configuration.                                               */
/* -------------------------------------------------------------------------- */

void
BitwuzlaSolver::configure_opmgr(OpKindManager* opmgr) const
{
  //! [docs-bitwuzla-solver-configure_opmgr_bv_dec start]
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_DEC, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  //! [docs-bitwuzla-solver-configure_opmgr_bv_dec end]
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_INC, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_ROL, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_ROR, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_REDAND, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_REDOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_REDXOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_UADDO, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_UMULO, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_USUBO, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_SADDO, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_SDIVO, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_SMULO, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BitwuzlaTerm::OP_BV_SSUBO, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);

  /* Bitwuzla only supports a very restricted version of to_fp from Real:
   * only from strings representing real or rational values. We thus define
   * this as a solver-specific operator with two arguments: a rounding mode
   * term, and an FP term (which is only needed to get an existing FP sort to
   * convert to).  This is a workaround for this very special case (we don't)
   * want to generalize it for all solvers because it is too special). */
  opmgr->add_op_kind(BitwuzlaTerm::OP_FP_TO_FP_FROM_REAL,
                     2,
                     0,
                     SORT_FP,
                     {SORT_RM, SORT_FP},
                     THEORY_FP);

  opmgr->add_op_kind(
      BitwuzlaTerm::OP_IFF, 2, 0, SORT_BOOL, {SORT_BOOL}, THEORY_BOOL);
}

/* -------------------------------------------------------------------------- */
/* Option configuration.                                                      */
/* -------------------------------------------------------------------------- */

//! [docs-bitwuzla-solver-configure_options start]
void
BitwuzlaSolver::configure_options(SolverManager* smgr) const
{
  ::bitwuzla::Options options;
  for (int32_t i = 0, n = static_cast<int32_t>(::bitwuzla::Option::NUM_OPTS);
       i < n;
       ++i)
  {
    ::bitwuzla::Option opt = static_cast<::bitwuzla::Option>(i);
    ::bitwuzla::OptionInfo info(options, opt);
    if (info.kind == ::bitwuzla::OptionInfo::Kind::BOOL)
    {
      const auto& b = std::get<::bitwuzla::OptionInfo::Bool>(info.values);
      smgr->add_option(new SolverOptionBool(info.lng, b.dflt));
    }
    else if (info.kind == ::bitwuzla::OptionInfo::Kind::NUMERIC)
    {
      const auto& num = std::get<::bitwuzla::OptionInfo::Numeric>(info.values);
      smgr->add_option(
          new SolverOptionNum<uint32_t>(info.lng,
                                        static_cast<uint32_t>(num.min),
                                        static_cast<uint32_t>(num.max),
                                        static_cast<uint32_t>(num.dflt)));
    }
    else
    {
      assert(info.kind == ::bitwuzla::OptionInfo::Kind::MODE);
      const ::bitwuzla::OptionInfo::Mode& mode =
          std::get<::bitwuzla::OptionInfo::Mode>(info.values);
      smgr->add_option(new SolverOptionList(info.lng, mode.modes, mode.dflt));
    }
  }
}
//! [docs-bitwuzla-solver-configure_options end]

/* -------------------------------------------------------------------------- */
/* FSM configuration.                                                         */
/* -------------------------------------------------------------------------- */

#if 0
class BzlaActionGetArrayValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-get-array-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionGetArrayValue(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    if (!d_smgr.has_term(SORT_ARRAY, 0)) return false;
    Term term = d_smgr.pick_term(SORT_ARRAY, 0);
    run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    run(term);
    return {};
  }

 private:
  void run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    BitwuzlaSolver& bzla_solver       = dynamic_cast<BitwuzlaSolver&>(d_solver);
    Bitwuzla* bzla                = bzla_solver.get_solver();
    const BitwuzlaTerm* bzla_term = BitwuzlaTerm::get_bzla_term(term);
    const BitwuzlaTerm **bzla_idxs, **bzla_vals, *bzla_default_val;
    size_t size;

    bitwuzla_get_array_value(
        bzla, bzla_term, &bzla_idxs, &bzla_vals, &size, &bzla_default_val);

    if (d_smgr.d_incremental)
    {
      /* assume assignment and check if result is still SAT */
      std::vector<Term> assumptions;
      for (size_t i = 0; i < size; ++i)
      {
        const BitwuzlaTerm* bzla_select = bitwuzla_mk_term2(
            bzla, BITWUZLA_KIND_ARRAY_SELECT, bzla_term, bzla_idxs[i]);
        const BitwuzlaTerm* bzla_eq = bitwuzla_mk_term2(
            bzla, BITWUZLA_KIND_EQUAL, bzla_select, bzla_vals[i]);
        assumptions.push_back(std::shared_ptr<BitwuzlaTerm>(new BitwuzlaTerm(bzla_eq)));
      }
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
  }
};
#endif

class BitwuzlaActionGetBvValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bitwuzla-get-bv-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BitwuzlaActionGetBvValue(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    if (!d_smgr.has_term(SORT_BV, 0)) return false;
    Term term = d_smgr.pick_term(SORT_BV, 0);
    run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    run(term);
    return {};
  }

 private:
  void run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    BitwuzlaSolver& bzla_solver       = dynamic_cast<BitwuzlaSolver&>(d_solver);
    const ::bitwuzla::Term& bzla_term = BitwuzlaTerm::get_bitwuzla_term(term);
    std::string bv_val = bzla_solver.get_solver()->get_bv_value(bzla_term);
    if (d_smgr.d_incremental)
    {
      /* assume assignment and check if result is still SAT */
      Term term_bv_val =
          d_solver.mk_value(term->get_sort(), bv_val, Solver::Base::BIN);
      std::vector<Term> assumptions{
          d_solver.mk_term(Op::EQUAL, {term, term_bv_val}, {})};
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
  }
};

class BitwuzlaActionGetFpValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bitwuzla-get-fp-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BitwuzlaActionGetFpValue(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    if (!d_smgr.has_term(SORT_FP, 0)) return false;
    Term term = d_smgr.pick_term(SORT_FP, 0);
    run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    run(term);
    return {};
  }

 private:
  void run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    BitwuzlaSolver& bzla_solver      = dynamic_cast<BitwuzlaSolver&>(d_solver);
    const ::bitwuzla::Term bzla_term = BitwuzlaTerm::get_bitwuzla_term(term);

    auto choice = d_rng.pick_one_of_three();
    uint8_t base;
    if (choice == RNGenerator::Choice::FIRST)
    {
      base = 2;
    }
    else if (choice == RNGenerator::Choice::SECOND)
    {
      base = 10;
    }
    else
    {
      base = 16;
    }

    std::string fp_val;
    if (d_rng.flip_coin())
    {
      std::string fp_val_sign, fp_val_exp, fp_val_sig;
      bzla_solver.get_solver()->get_fp_value(
          bzla_term, fp_val_sign, fp_val_exp, fp_val_sig, base);
      fp_val = fp_val_sign + fp_val_exp + fp_val_sig;
    }
    else
    {
      fp_val = bzla_solver.get_solver()->get_fp_value(bzla_term, base);
    }
    if (d_smgr.d_incremental)
    {
      /* assume assignment and check if result is still SAT */
      Term term_fp_val = d_solver.mk_value(term->get_sort(), fp_val);
      std::vector<Term> assumptions{
          d_solver.mk_term(Op::EQUAL, {term, term_fp_val}, {})};
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
  }
};

#if 0
class BzlaActionGetFunValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-get-fun-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionGetFunValue(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    if (!d_smgr.has_term(SORT_FUN, 0)) return false;
    Term term = d_smgr.pick_term(SORT_FUN, 0);
    run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    run(term);
    return {};
  }

 private:
  void run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    BitwuzlaSolver& bzla_solver       = dynamic_cast<BitwuzlaSolver&>(d_solver);
    Bitwuzla* bzla                = bzla_solver.get_solver();
    const BitwuzlaTerm* bzla_term = BitwuzlaTerm::get_bzla_term(term);
    const BitwuzlaTerm ***bzla_args, **bzla_vals;
    size_t arity, size;

    bitwuzla_get_fun_value(
        bzla, bzla_term, &bzla_args, &arity, &bzla_vals, &size);

    if (d_smgr.d_incremental)
    {
      /* assume assignment and check if result is still SAT */
      std::vector<Term> assumptions;
      for (size_t i = 0; i < size; ++i)
      {
        std::vector<const BitwuzlaTerm*> fun_args;
        fun_args.push_back(bzla_term);
        for (size_t j = 0; j < arity; ++j)
        {
          fun_args.push_back(bzla_args[i][j]);
        }
        const BitwuzlaTerm* bzla_apply =
            bitwuzla_mk_term(bzla,
                             BITWUZLA_KIND_APPLY,
                             static_cast<uint32_t>(fun_args.size()),
                             fun_args.data());
        const BitwuzlaTerm* bzla_eq = bitwuzla_mk_term2(
            bzla, BITWUZLA_KIND_EQUAL, bzla_apply, bzla_vals[i]);
        assumptions.push_back(std::shared_ptr<BitwuzlaTerm>(new BitwuzlaTerm(bzla_eq)));
      }
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
  }
};
#endif

class BitwuzlaActionGetRmValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bitwuzla-get-rm-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BitwuzlaActionGetRmValue(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    if (!d_smgr.has_term(SORT_RM, 0)) return false;
    Term term = d_smgr.pick_term(SORT_RM, 0);
    run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    run(term);
    return {};
  }

 private:
  void run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    BitwuzlaSolver& bzla_solver       = dynamic_cast<BitwuzlaSolver&>(d_solver);
    const ::bitwuzla::Term& bzla_term = BitwuzlaTerm::get_bitwuzla_term(term);
    ::bitwuzla::RoundingMode rm_val =
        bzla_solver.get_solver()->get_rm_value(bzla_term);
    if (d_smgr.d_incremental)
    {
      AbsTerm::SpecialValueKind value;
      if (rm_val == ::bitwuzla::RoundingMode::RNA)
      {
        value = AbsTerm::SPECIAL_VALUE_RM_RNA;
      }
      else if (rm_val == ::bitwuzla::RoundingMode::RNE)
      {
        value = AbsTerm::SPECIAL_VALUE_RM_RNE;
      }
      else if (rm_val == ::bitwuzla::RoundingMode::RTN)
      {
        value = AbsTerm::SPECIAL_VALUE_RM_RTN;
      }
      else if (rm_val == ::bitwuzla::RoundingMode::RTP)
      {
        value = AbsTerm::SPECIAL_VALUE_RM_RTP;
      }
      else
      {
        assert(rm_val == ::bitwuzla::RoundingMode::RTZ);
        value = AbsTerm::SPECIAL_VALUE_RM_RTZ;
      }
      /* assume assignment and check if result is still SAT */
      Term term_rm_val = d_solver.mk_special_value(term->get_sort(), value);
      std::vector<Term> assumptions{
          d_solver.mk_term(Op::EQUAL, {term, term_rm_val}, {})};
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
  }
};

class BitwuzlaActionIsUnsatAssumption : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bitwuzla-is-unsat-assumption";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BitwuzlaActionIsUnsatAssumption(SolverManager& smgr)
      : Action(smgr, s_name, NONE)
  {
  }

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::UNSAT) return false;
    if (!d_smgr.d_incremental) return false;
    if (!d_smgr.has_assumed()) return false;
    Term term = d_smgr.pick_assumed_assumption();
    run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    run(term);
    return {};
  }

 private:
  void run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    BitwuzlaSolver& bzla_solver = dynamic_cast<BitwuzlaSolver&>(d_solver);
    (void) bzla_solver.get_solver()->is_unsat_assumption(
        BitwuzlaTerm::get_bitwuzla_term(term));
  }
};

#if 0
class BzlaActionSimplify : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-simplify";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionSimplify(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    BitwuzlaSolver& solver = dynamic_cast<BitwuzlaSolver&>(d_solver);
    if (solver.get_solver() == nullptr) return false;
    run();
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    run();
    return {};
  }

 private:
  void run()
  {
    MURXLA_TRACE << get_kind();
    reset_sat();
    bitwuzla_simplify(dynamic_cast<BitwuzlaSolver&>(d_solver).get_solver());
  }
};
#endif

class BitwuzlaActionSubstituteTerm : public Action
{
 public:
  /** The maximum number of terms to substitute terms in. */
  static constexpr uint32_t MAX_N_TERMS = 3;
  /** The maximum number of terms to be substituted. */
  static constexpr uint32_t MAX_N_SUBST_TERMS = 3;
  /** The name of this action. */
  inline static const Kind s_name = "bitwuzla-substitute-term";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BitwuzlaActionSubstituteTerm(SolverManager& smgr) : Action(smgr, s_name, NONE)
  {
  }

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;

    /* Pick terms. */
    uint32_t n_terms = d_rng.pick<uint32_t>(1, MAX_N_TERMS);
    std::vector<Term> terms;
    std::vector<Term> to_subst_terms;
    std::vector<Term> subst_terms;
    for (uint32_t i = 0; i < n_terms; ++i)
    {
      Term term = d_smgr.pick_term();
      terms.push_back(term);
      /* Pick term to substitute. */
      std::vector<Term> sub_terms = get_sub_terms(term);
      if (sub_terms.empty()) return false;
      size_t n_subst_terms = d_rng.pick<size_t>(
          1, std::min<size_t>(sub_terms.size(), MAX_N_SUBST_TERMS));
      for (size_t j = 0; j < n_subst_terms; ++j)
      {
        Term to_subst_term =
            d_rng.pick_from_set<decltype(sub_terms), Term>(sub_terms);
        to_subst_terms.push_back(to_subst_term);
        Sort to_subst_sort = to_subst_term->get_sort();
        Term subst_term    = d_smgr.pick_term(to_subst_sort);
        subst_terms.push_back(subst_term);
      }
    }

    run(terms, to_subst_terms, subst_terms);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS_MIN(6, "", tokens.size());

    uint32_t idx = 0;

    uint32_t n_terms = str_to_uint32(tokens[idx++]);
    std::vector<Term> terms;
    for (uint32_t i = 0; i < n_terms; ++i)
    {
      Term term = get_untraced_term(untrace_str_to_id(tokens[idx]));
      MURXLA_CHECK_TRACE_TERM(term, tokens[idx]);
      terms.push_back(term);
      idx += 1;
    }

    uint32_t n_to_subst_terms = str_to_uint32(tokens[idx++]);
    std::vector<Term> to_subst_terms;
    for (size_t i = 0; i < n_to_subst_terms; ++i)
    {
      to_subst_terms.push_back(
          get_untraced_term(untrace_str_to_id(tokens[idx])));
      MURXLA_CHECK_TRACE_TERM(to_subst_terms.back(), tokens[idx]);
      idx += 1;
    }

    uint32_t n_subst_terms = str_to_uint32(tokens[idx++]);
    std::vector<Term> subst_terms;
    for (size_t i = 0; i < n_subst_terms; ++i)
    {
      subst_terms.push_back(get_untraced_term(untrace_str_to_id(tokens[idx])));
      MURXLA_CHECK_TRACE_TERM(subst_terms.back(), tokens[idx]);
      idx += 1;
    }

    run(terms, to_subst_terms, subst_terms);
    return {};
  }

 private:
  void run(std::vector<Term> terms,
           std::vector<Term> to_subst_terms,
           std::vector<Term> subst_terms)
  {
    MURXLA_TRACE << get_kind() << " " << terms.size() << terms << " "
                 << to_subst_terms.size() << to_subst_terms << " "
                 << subst_terms.size() << subst_terms;
    d_smgr.reset_sat();
    std::vector<::bitwuzla::Term> bzla_terms =
        BitwuzlaTerm::terms_to_bitwuzla_terms(terms);

    std::unordered_map<::bitwuzla::Term, ::bitwuzla::Term> map;
    for (size_t i = 0, n = to_subst_terms.size(); i < n; ++i)
    {
      map.emplace(BitwuzlaTerm::get_bitwuzla_term(to_subst_terms[i]),
                  BitwuzlaTerm::get_bitwuzla_term(subst_terms[i]));
    }
    if (bzla_terms.size() == 1 && d_rng.flip_coin())
    {
      ::bitwuzla::Term bzla_res =
          ::bitwuzla::substitute_term(bzla_terms[0], map);
      /* Note: The substituted term 'bzla_res' may or may not be already in the
       *       term DB. Since we can't always compute the exact level, we can't
       *       add the substituted term to the term DB. */
      MURXLA_TEST(!bzla_res.is_null());
    }
    else
    {
      ::bitwuzla::substitute_terms(bzla_terms, map);
    }
  }

  /**
   * Collect all known sub terms (terms registered in the term DB) of a given
   * term. Performs a pre-order traversal over term.
   */
  std::vector<Term> get_sub_terms(Term term)
  {
    std::vector<Term> res;
    std::unordered_set<::bitwuzla::Term> bzla_res;
    const ::bitwuzla::Term bzla_term = BitwuzlaTerm::get_bitwuzla_term(term);
    std::vector<::bitwuzla::Term> to_visit{bzla_term};
    while (!to_visit.empty())
    {
      const ::bitwuzla::Term& bzla_vterm = to_visit.back();
      to_visit.pop_back();
      for (const auto& ch : bzla_vterm.children())
      {
        if (ch.is_const() && bzla_res.find(ch) == bzla_res.end())
        {
          bzla_res.insert(ch);
          to_visit.push_back(ch);
        }
      }
    }

    for (const ::bitwuzla::Term& bzla_t : bzla_res)
    {
      Sort s = std::shared_ptr<BitwuzlaSort>(new BitwuzlaSort(bzla_t.sort()));
      s      = d_smgr.find_sort(s);
      if (s->get_kind() == SORT_ANY) continue;
      Term t = std::shared_ptr<BitwuzlaTerm>(new BitwuzlaTerm(bzla_t));
      t      = d_smgr.find_term(t, s, s->get_kind());
      if (t == nullptr) continue;
      res.push_back(t);
    }
    return res;
  }
};

#if 0
class BzlaActionTermSetSymbol : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-term-set-symbol";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionTermSetSymbol(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    Term term          = d_smgr.pick_term();
    std::string symbol = d_smgr.pick_symbol();
    run(term, symbol);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    std::string symbol = str_to_str(tokens[1]);
    run(term, symbol);
    return {};
  }

 private:
  void run(Term term, std::string symbol)
  {
    MURXLA_TRACE << get_kind() << " " << term << " \"" << symbol << "\"";
    (void) bitwuzla_term_set_symbol(BitwuzlaTerm::get_bzla_term(term),
                                    symbol.c_str());
    MURXLA_TEST(
        std::string(bitwuzla_term_get_symbol(BitwuzlaTerm::get_bzla_term(term)))
        == symbol);
  }
};
#endif

class BitwuzlaActionMisc : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bitwuzla-misc";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BitwuzlaActionMisc(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    run();
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(0, tokens.size());
    run();
    return {};
  }

 private:
  void run()
  {
    MURXLA_TRACE << get_kind();

    std::string version = ::bitwuzla::version();
    MURXLA_TEST(version != "");
    std::string copyright = ::bitwuzla::copyright();
    MURXLA_TEST(copyright != "");
    std::string git_id = ::bitwuzla::git_id();
    MURXLA_TEST(git_id != "");
  }
};

/* -------------------------------------------------------------------------- */

void
BitwuzlaSolver::configure_fsm(FSM* fsm) const
{
  SolverManager& smgr = fsm->get_smgr();

  /* Retrieve existing states. */
  // State* s_assert           = fsm->get_state(State::ASSERT);
  State* s_check_sat = fsm->get_state(State::CHECK_SAT);
  // State* s_create_sorts     = fsm->get_state(State::CREATE_SORTS);
  // State* s_create_inputs    = fsm->get_state(State::CREATE_INPUTS);
  // State* s_create_terms     = fsm->get_state(State::CREATE_TERMS);
  // State* s_opt              = fsm->get_state(State::OPT);
  // State* s_push_pop         = fsm->get_state(State::PUSH_POP);
  State* s_sat = fsm->get_state(State::SAT);
  // State* s_unsat            = fsm->get_state(State::UNSAT);
  State* s_decide_sat_unsat = fsm->get_state(State::DECIDE_SAT_UNSAT);

  auto t_default = fsm->new_action<TransitionDefault>();

  /* Modify precondition of existing states. */
  s_sat->update_precondition([&smgr]() {
    return smgr.d_sat_called && smgr.d_sat_result == Solver::Result::SAT;
  });

  /* Solver-specific states. */
  State* s_unknown = fsm->new_choice_state(STATE_UNKNOWN, [&smgr]() {
    return smgr.d_sat_called && smgr.d_sat_result == Solver::Result::UNKNOWN;
  });

  /* Add solver-specific actions and reconfigure existing states. */
  s_decide_sat_unsat->add_action(t_default, 1, s_unknown);
  // bitwuzla_get_array_value
  // auto a_get_array_val = fsm->new_action<BzlaActionGetArrayValue>();
  // s_sat->add_action(a_get_array_val, 2);
  // bitwuzla_get_bv_value
  auto a_get_bv_val = fsm->new_action<BitwuzlaActionGetBvValue>();
  s_sat->add_action(a_get_bv_val, 2);
  // bitwuzla_get_fp_value
  auto a_get_fp_val = fsm->new_action<BitwuzlaActionGetFpValue>();
  s_sat->add_action(a_get_fp_val, 2);
  // bitwuzla_get_fun_value
  // auto a_get_fun_val = fsm->new_action<BzlaActionGetFunValue>();
  // s_sat->add_action(a_get_fun_val, 2);
  // bitwuzla_get_rm_value
  auto a_get_rm_val = fsm->new_action<BitwuzlaActionGetRmValue>();
  s_sat->add_action(a_get_rm_val, 2);
  // bitwuzla_is_unsat_assumption
  // auto a_failed = fsm->new_action<BitwuzlaActionIsUnsatAssumption>();
  // fsm->add_action_to_all_states(a_failed, 100);
  // bitwuzla_simplify
  // auto a_simplify = fsm->new_action<BzlaActionSimplify>();
  // s_assert->add_action(a_simplify, 10000);
  // s_create_sorts->add_action(a_simplify, 10000);
  // s_create_inputs->add_action(a_simplify, 10000);
  // s_create_terms->add_action(a_simplify, 10000);
  // s_opt->add_action(a_simplify, 10000);
  // s_push_pop->add_action(a_simplify, 10000);
  // s_check_sat->add_action(a_simplify, 10000, s_create_terms);
  // s_sat->add_action(a_simplify, 10000, s_create_terms);
  // s_unsat->add_action(a_simplify, 10000, s_create_terms);
  // bitwuzla_substitute_term
  // bitwuzla_substitute_terms
  auto a_subst_term = fsm->new_action<BitwuzlaActionSubstituteTerm>();
  fsm->add_action_to_all_states(a_subst_term, 1000);
  // bitwuzla_term_set_symbol
  // auto a_set_symbol = fsm->new_action<BzlaActionTermSetSymbol>();
  // fsm->add_action_to_all_states(a_set_symbol, 1000);

  auto a_misc = fsm->new_action<BitwuzlaActionMisc>();
  fsm->add_action_to_all_states(a_misc, 100000);

  /* Configure solver-specific states. */
  s_unknown->add_action(t_default, 1, s_check_sat);
}

void
BitwuzlaSolver::disable_unsupported_actions(FSM* fsm) const
{
  fsm->disable_action(ActionResetAssertions::s_name);
  fsm->disable_action(ActionInstantiateSort::s_name);
  fsm->disable_action(BitwuzlaActionSubstituteTerm::s_name);
}

}  // namespace bitwuzla
}  // namespace murxla

#endif
