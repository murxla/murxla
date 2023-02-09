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

#include "bzla_solver.hpp"

#include <bitset>
#include <cassert>
#include <cstdlib>

#include "action.hpp"
#include "config.hpp"
#include "except.hpp"
#include "solver/bzla/profile.hpp"
#include "solver_option.hpp"
#include "theory.hpp"
#include "util.hpp"

namespace murxla {
namespace bzla {

/* -------------------------------------------------------------------------- */
/* BzlaSort                                                                   */
/* -------------------------------------------------------------------------- */

const BitwuzlaSort*
BzlaSort::get_bzla_sort(Sort sort)
{
  return checked_cast<BzlaSort*>(sort.get())->d_sort;
}

std::vector<Sort>
BzlaSort::bzla_sorts_to_sorts(Bitwuzla* bzla,
                              const BitwuzlaSort** sorts,
                              size_t size)
{
  std::vector<Sort> res;
  for (size_t i = 0; i < size; ++i)
  {
    res.push_back(std::shared_ptr<BzlaSort>(new BzlaSort(bzla, sorts[i])));
  }
  return res;
}

BzlaSort::BzlaSort(Bitwuzla* bzla, const BitwuzlaSort* sort)
    : d_solver(bzla), d_sort(sort)
{
}

BzlaSort::~BzlaSort() {}

size_t
BzlaSort::hash() const
{
  return bitwuzla_sort_hash(d_sort);
}

std::string
BzlaSort::to_string() const
{
  FILE* tmp_file = std::tmpfile();
  bitwuzla_sort_dump(d_sort, "smt2", tmp_file);
  std::rewind(tmp_file);
  std::stringstream ss;
  int32_t ch;
  while ((ch = std::fgetc(tmp_file)) != EOF)
  {
    ss << (char) ch;
  }
  MURXLA_EXIT_ERROR(std::ferror(tmp_file))
      << "error while reading from tmp file";
  std::fclose(tmp_file);
  return ss.str();
}

bool
BzlaSort::equals(const Sort& other) const
{
  BzlaSort* bzla_sort = checked_cast<BzlaSort*>(other.get());
  if (bzla_sort)
  {
    return bitwuzla_sort_is_equal(d_sort, bzla_sort->d_sort);
  }
  return false;
}

bool
BzlaSort::is_array() const
{
  return bitwuzla_sort_is_array(d_sort);
}

bool
BzlaSort::is_bool() const
{
  const BitwuzlaSort* s = bitwuzla_mk_bool_sort(d_solver);
  bool res              = s == d_sort;
  return res && d_kind == SORT_BOOL;
}

//! [docs-bzla-sort-is_bv start]
bool
BzlaSort::is_bv() const
{
  return bitwuzla_sort_is_bv(d_sort);
}
//! [docs-bzla-sort-is_bv end]

bool
BzlaSort::is_fp() const
{
  return bitwuzla_sort_is_fp(d_sort);
}

bool
BzlaSort::is_fun() const
{
  return bitwuzla_sort_is_fun(d_sort);
}

bool
BzlaSort::is_rm() const
{
  return bitwuzla_sort_is_rm(d_sort);
}

uint32_t
BzlaSort::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = bitwuzla_sort_bv_get_size(d_sort);
  MURXLA_TEST(res);
  return res;
}

uint32_t
BzlaSort::get_fp_exp_size() const
{
  assert(is_fp());
  uint32_t res = bitwuzla_sort_fp_get_exp_size(d_sort);
  MURXLA_TEST(res);
  return res;
}

uint32_t
BzlaSort::get_fp_sig_size() const
{
  assert(is_fp());
  uint32_t res = bitwuzla_sort_fp_get_sig_size(d_sort);
  MURXLA_TEST(res);
  return res;
}

Sort
BzlaSort::get_array_index_sort() const
{
  assert(is_array());
  const BitwuzlaSort* bzla_res = bitwuzla_sort_array_get_index(d_sort);
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaSort> res(new BzlaSort(d_solver, bzla_res));
  assert(res);
  return res;
}

Sort
BzlaSort::get_array_element_sort() const
{
  assert(is_array());
  const BitwuzlaSort* bzla_res = bitwuzla_sort_array_get_element(d_sort);
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaSort> res(new BzlaSort(d_solver, bzla_res));
  assert(res);
  return res;
}

uint32_t
BzlaSort::get_fun_arity() const
{
  assert(is_fun());
  return bitwuzla_sort_fun_get_arity(d_sort);
}

Sort
BzlaSort::get_fun_codomain_sort() const
{
  assert(is_fun());
  const BitwuzlaSort* bzla_res = bitwuzla_sort_fun_get_codomain(d_sort);
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaSort> res(new BzlaSort(d_solver, bzla_res));
  assert(res);
  return res;
}

std::vector<Sort>
BzlaSort::get_fun_domain_sorts() const
{
  assert(is_fun());
  size_t size;
  const BitwuzlaSort** bzla_res =
      bitwuzla_sort_fun_get_domain_sorts(d_sort, &size);
  return bzla_sorts_to_sorts(d_solver, bzla_res, size);
}

/* -------------------------------------------------------------------------- */
/* BzlaTerm                                                                   */
/* -------------------------------------------------------------------------- */

std::unordered_map<Op::Kind, BitwuzlaKind> BzlaTerm::s_kinds_to_bzla_kinds = {
    /* Special Cases */
    {Op::DISTINCT, BITWUZLA_KIND_DISTINCT},
    {Op::EQUAL, BITWUZLA_KIND_EQUAL},
    {Op::ITE, BITWUZLA_KIND_ITE},

    /* Bool */
    {Op::AND, BITWUZLA_KIND_AND},
    {Op::OR, BITWUZLA_KIND_OR},
    {Op::NOT, BITWUZLA_KIND_NOT},
    {Op::XOR, BITWUZLA_KIND_XOR},
    {Op::IMPLIES, BITWUZLA_KIND_IMPLIES},
    {Op::IFF, BITWUZLA_KIND_IFF},

    /* Arrays */
    {Op::ARRAY_SELECT, BITWUZLA_KIND_ARRAY_SELECT},
    {Op::ARRAY_STORE, BITWUZLA_KIND_ARRAY_STORE},

    /* BV */
    {Op::BV_EXTRACT, BITWUZLA_KIND_BV_EXTRACT},
    {Op::BV_REPEAT, BITWUZLA_KIND_BV_REPEAT},
    {Op::BV_ROTATE_LEFT, BITWUZLA_KIND_BV_ROLI},
    {Op::BV_ROTATE_RIGHT, BITWUZLA_KIND_BV_RORI},
    {Op::BV_SIGN_EXTEND, BITWUZLA_KIND_BV_SIGN_EXTEND},
    {Op::BV_ZERO_EXTEND, BITWUZLA_KIND_BV_ZERO_EXTEND},

    {Op::BV_CONCAT, BITWUZLA_KIND_BV_CONCAT},
    {Op::BV_AND, BITWUZLA_KIND_BV_AND},
    {Op::BV_OR, BITWUZLA_KIND_BV_OR},
    {Op::BV_XOR, BITWUZLA_KIND_BV_XOR},
    {Op::BV_MULT, BITWUZLA_KIND_BV_MUL},
    {Op::BV_ADD, BITWUZLA_KIND_BV_ADD},
    {Op::BV_NOT, BITWUZLA_KIND_BV_NOT},
    {Op::BV_NEG, BITWUZLA_KIND_BV_NEG},
    {Op::BV_NAND, BITWUZLA_KIND_BV_NAND},
    {Op::BV_NOR, BITWUZLA_KIND_BV_NOR},
    {Op::BV_XNOR, BITWUZLA_KIND_BV_XNOR},
    {Op::BV_COMP, BITWUZLA_KIND_BV_COMP},
    {Op::BV_SUB, BITWUZLA_KIND_BV_SUB},
    {Op::BV_UDIV, BITWUZLA_KIND_BV_UDIV},
    {Op::BV_UREM, BITWUZLA_KIND_BV_UREM},
    {Op::BV_UREM, BITWUZLA_KIND_BV_UREM},
    {Op::BV_SDIV, BITWUZLA_KIND_BV_SDIV},
    {Op::BV_SREM, BITWUZLA_KIND_BV_SREM},
    {Op::BV_SMOD, BITWUZLA_KIND_BV_SMOD},
    {Op::BV_SHL, BITWUZLA_KIND_BV_SHL},
    {Op::BV_LSHR, BITWUZLA_KIND_BV_SHR},
    {Op::BV_ASHR, BITWUZLA_KIND_BV_ASHR},
    {Op::BV_ULT, BITWUZLA_KIND_BV_ULT},
    {Op::BV_ULE, BITWUZLA_KIND_BV_ULE},
    {Op::BV_UGT, BITWUZLA_KIND_BV_UGT},
    {Op::BV_UGE, BITWUZLA_KIND_BV_UGE},
    {Op::BV_SLT, BITWUZLA_KIND_BV_SLT},
    {Op::BV_SLE, BITWUZLA_KIND_BV_SLE},
    {Op::BV_SGT, BITWUZLA_KIND_BV_SGT},
    {Op::BV_SGE, BITWUZLA_KIND_BV_SGE},

    /* FP */
    {Op::FP_ABS, BITWUZLA_KIND_FP_ABS},
    {Op::FP_ADD, BITWUZLA_KIND_FP_ADD},
    {Op::FP_DIV, BITWUZLA_KIND_FP_DIV},
    {Op::FP_EQ, BITWUZLA_KIND_FP_EQ},
    {Op::FP_FMA, BITWUZLA_KIND_FP_FMA},
    {Op::FP_FP, BITWUZLA_KIND_FP_FP},
    {Op::FP_IS_NORMAL, BITWUZLA_KIND_FP_IS_NORMAL},
    {Op::FP_IS_SUBNORMAL, BITWUZLA_KIND_FP_IS_SUBNORMAL},
    {Op::FP_IS_INF, BITWUZLA_KIND_FP_IS_INF},
    {Op::FP_IS_NAN, BITWUZLA_KIND_FP_IS_NAN},
    {Op::FP_IS_NEG, BITWUZLA_KIND_FP_IS_NEG},
    {Op::FP_IS_POS, BITWUZLA_KIND_FP_IS_POS},
    {Op::FP_IS_ZERO, BITWUZLA_KIND_FP_IS_ZERO},
    {Op::FP_LT, BITWUZLA_KIND_FP_LT},
    {Op::FP_LEQ, BITWUZLA_KIND_FP_LEQ},
    {Op::FP_GT, BITWUZLA_KIND_FP_GT},
    {Op::FP_GEQ, BITWUZLA_KIND_FP_GEQ},
    {Op::FP_MAX, BITWUZLA_KIND_FP_MAX},
    {Op::FP_MIN, BITWUZLA_KIND_FP_MIN},
    {Op::FP_MUL, BITWUZLA_KIND_FP_MUL},
    {Op::FP_NEG, BITWUZLA_KIND_FP_NEG},
    {Op::FP_REM, BITWUZLA_KIND_FP_REM},
    {Op::FP_RTI, BITWUZLA_KIND_FP_RTI},
    {Op::FP_SQRT, BITWUZLA_KIND_FP_SQRT},
    {Op::FP_SUB, BITWUZLA_KIND_FP_SUB},
    {Op::FP_TO_FP_FROM_BV, BITWUZLA_KIND_FP_TO_FP_FROM_BV},
    {Op::FP_TO_FP_FROM_SBV, BITWUZLA_KIND_FP_TO_FP_FROM_SBV},
    {Op::FP_TO_FP_FROM_FP, BITWUZLA_KIND_FP_TO_FP_FROM_FP},
    {Op::FP_TO_FP_FROM_UBV, BITWUZLA_KIND_FP_TO_FP_FROM_UBV},
    {Op::FP_TO_SBV, BITWUZLA_KIND_FP_TO_SBV},
    {Op::FP_TO_UBV, BITWUZLA_KIND_FP_TO_UBV},

    /* Quantifiers */
    {Op::FORALL, BITWUZLA_KIND_FORALL},
    {Op::EXISTS, BITWUZLA_KIND_EXISTS},

    /* UF */
    {Op::UF_APPLY, BITWUZLA_KIND_APPLY},

    /* Solver-specific operators */
    {OP_BV_DEC, BITWUZLA_KIND_BV_DEC},
    {OP_BV_INC, BITWUZLA_KIND_BV_INC},
    {OP_BV_ROL, BITWUZLA_KIND_BV_ROL},
    {OP_BV_ROR, BITWUZLA_KIND_BV_ROR},
    {OP_BV_REDAND, BITWUZLA_KIND_BV_REDAND},
    {OP_BV_REDOR, BITWUZLA_KIND_BV_REDOR},
    {OP_BV_REDXOR, BITWUZLA_KIND_BV_REDXOR},
    {OP_BV_UADDO, BITWUZLA_KIND_BV_UADD_OVERFLOW},
    {OP_BV_SADDO, BITWUZLA_KIND_BV_SADD_OVERFLOW},
    {OP_BV_UMULO, BITWUZLA_KIND_BV_UMUL_OVERFLOW},
    {OP_BV_SMULO, BITWUZLA_KIND_BV_SMUL_OVERFLOW},
    {OP_BV_USUBO, BITWUZLA_KIND_BV_USUB_OVERFLOW},
    {OP_BV_SSUBO, BITWUZLA_KIND_BV_SSUB_OVERFLOW},
    {OP_BV_SDIVO, BITWUZLA_KIND_BV_SDIV_OVERFLOW},
    {OP_IFF, BITWUZLA_KIND_IFF},
    /* Special treatment, not really a Bitwuzla kind. */
    {OP_FP_TO_FP_FROM_REAL, BITWUZLA_NUM_KINDS},
};

std::unordered_map<BitwuzlaKind, Op::Kind> BzlaTerm::s_bzla_kinds_to_kinds = {
    /* Leaf Kinds */
    {BITWUZLA_KIND_CONST, Op::CONSTANT},
    {BITWUZLA_KIND_CONST_ARRAY, Op::CONST_ARRAY},
    {BITWUZLA_KIND_VAL, Op::VALUE},
    {BITWUZLA_KIND_VAR, Op::VARIABLE},
    {BITWUZLA_KIND_LAMBDA, Op::FUN},

    /* Special Cases */
    {BITWUZLA_KIND_DISTINCT, Op::DISTINCT},
    {BITWUZLA_KIND_EQUAL, Op::EQUAL},
    {BITWUZLA_KIND_ITE, Op::ITE},

    /* Bool */
    {BITWUZLA_KIND_AND, Op::AND},
    {BITWUZLA_KIND_OR, Op::OR},
    {BITWUZLA_KIND_NOT, Op::NOT},
    {BITWUZLA_KIND_XOR, Op::XOR},
    {BITWUZLA_KIND_IMPLIES, Op::IMPLIES},
    {BITWUZLA_KIND_IFF, Op::IFF},

    /* Arrays */
    {BITWUZLA_KIND_ARRAY_SELECT, Op::ARRAY_SELECT},
    {BITWUZLA_KIND_ARRAY_STORE, Op::ARRAY_STORE},

    /* BV */
    {BITWUZLA_KIND_BV_EXTRACT, Op::BV_EXTRACT},
    {BITWUZLA_KIND_BV_REPEAT, Op::BV_REPEAT},
    {BITWUZLA_KIND_BV_ROLI, Op::BV_ROTATE_LEFT},
    {BITWUZLA_KIND_BV_RORI, Op::BV_ROTATE_RIGHT},
    {BITWUZLA_KIND_BV_SIGN_EXTEND, Op::BV_SIGN_EXTEND},
    {BITWUZLA_KIND_BV_ZERO_EXTEND, Op::BV_ZERO_EXTEND},

    {BITWUZLA_KIND_BV_CONCAT, Op::BV_CONCAT},
    {BITWUZLA_KIND_BV_AND, Op::BV_AND},
    {BITWUZLA_KIND_BV_OR, Op::BV_OR},
    {BITWUZLA_KIND_BV_XOR, Op::BV_XOR},
    {BITWUZLA_KIND_BV_MUL, Op::BV_MULT},
    {BITWUZLA_KIND_BV_ADD, Op::BV_ADD},
    {BITWUZLA_KIND_BV_NOT, Op::BV_NOT},
    {BITWUZLA_KIND_BV_NEG, Op::BV_NEG},
    {BITWUZLA_KIND_BV_NAND, Op::BV_NAND},
    {BITWUZLA_KIND_BV_NOR, Op::BV_NOR},
    {BITWUZLA_KIND_BV_XNOR, Op::BV_XNOR},
    {BITWUZLA_KIND_BV_COMP, Op::BV_COMP},
    {BITWUZLA_KIND_BV_SUB, Op::BV_SUB},
    {BITWUZLA_KIND_BV_UDIV, Op::BV_UDIV},
    {BITWUZLA_KIND_BV_UREM, Op::BV_UREM},
    {BITWUZLA_KIND_BV_UREM, Op::BV_UREM},
    {BITWUZLA_KIND_BV_SDIV, Op::BV_SDIV},
    {BITWUZLA_KIND_BV_SREM, Op::BV_SREM},
    {BITWUZLA_KIND_BV_SMOD, Op::BV_SMOD},
    {BITWUZLA_KIND_BV_SHL, Op::BV_SHL},
    {BITWUZLA_KIND_BV_SHR, Op::BV_LSHR},
    {BITWUZLA_KIND_BV_ASHR, Op::BV_ASHR},
    {BITWUZLA_KIND_BV_ULT, Op::BV_ULT},
    {BITWUZLA_KIND_BV_ULE, Op::BV_ULE},
    {BITWUZLA_KIND_BV_UGT, Op::BV_UGT},
    {BITWUZLA_KIND_BV_UGE, Op::BV_UGE},
    {BITWUZLA_KIND_BV_SLT, Op::BV_SLT},
    {BITWUZLA_KIND_BV_SLE, Op::BV_SLE},
    {BITWUZLA_KIND_BV_SGT, Op::BV_SGT},
    {BITWUZLA_KIND_BV_SGE, Op::BV_SGE},

    /* FP */
    {BITWUZLA_KIND_FP_ABS, Op::FP_ABS},
    {BITWUZLA_KIND_FP_ADD, Op::FP_ADD},
    {BITWUZLA_KIND_FP_DIV, Op::FP_DIV},
    {BITWUZLA_KIND_FP_EQ, Op::FP_EQ},
    {BITWUZLA_KIND_FP_FMA, Op::FP_FMA},
    {BITWUZLA_KIND_FP_FP, Op::FP_FP},
    {BITWUZLA_KIND_FP_IS_NORMAL, Op::FP_IS_NORMAL},
    {BITWUZLA_KIND_FP_IS_SUBNORMAL, Op::FP_IS_SUBNORMAL},
    {BITWUZLA_KIND_FP_IS_INF, Op::FP_IS_INF},
    {BITWUZLA_KIND_FP_IS_NAN, Op::FP_IS_NAN},
    {BITWUZLA_KIND_FP_IS_NEG, Op::FP_IS_NEG},
    {BITWUZLA_KIND_FP_IS_POS, Op::FP_IS_POS},
    {BITWUZLA_KIND_FP_IS_ZERO, Op::FP_IS_ZERO},
    {BITWUZLA_KIND_FP_LT, Op::FP_LT},
    {BITWUZLA_KIND_FP_LEQ, Op::FP_LEQ},
    {BITWUZLA_KIND_FP_GT, Op::FP_GT},
    {BITWUZLA_KIND_FP_GEQ, Op::FP_GEQ},
    {BITWUZLA_KIND_FP_MAX, Op::FP_MAX},
    {BITWUZLA_KIND_FP_MIN, Op::FP_MIN},
    {BITWUZLA_KIND_FP_MUL, Op::FP_MUL},
    {BITWUZLA_KIND_FP_NEG, Op::FP_NEG},
    {BITWUZLA_KIND_FP_REM, Op::FP_REM},
    {BITWUZLA_KIND_FP_RTI, Op::FP_RTI},
    {BITWUZLA_KIND_FP_SQRT, Op::FP_SQRT},
    {BITWUZLA_KIND_FP_SUB, Op::FP_SUB},
    {BITWUZLA_KIND_FP_TO_FP_FROM_BV, Op::FP_TO_FP_FROM_BV},
    {BITWUZLA_KIND_FP_TO_FP_FROM_SBV, Op::FP_TO_FP_FROM_SBV},
    {BITWUZLA_KIND_FP_TO_FP_FROM_FP, Op::FP_TO_FP_FROM_FP},
    {BITWUZLA_KIND_FP_TO_FP_FROM_UBV, Op::FP_TO_FP_FROM_UBV},
    {BITWUZLA_KIND_FP_TO_SBV, Op::FP_TO_SBV},
    {BITWUZLA_KIND_FP_TO_UBV, Op::FP_TO_UBV},

    /* Quantifiers */
    {BITWUZLA_KIND_FORALL, Op::FORALL},
    {BITWUZLA_KIND_EXISTS, Op::EXISTS},

    /* UF */
    {BITWUZLA_KIND_APPLY, Op::UF_APPLY},

    /* Solver-specific operators */
    {BITWUZLA_KIND_BV_DEC, OP_BV_DEC},
    {BITWUZLA_KIND_BV_INC, OP_BV_INC},
    {BITWUZLA_KIND_BV_ROL, OP_BV_ROL},
    {BITWUZLA_KIND_BV_ROR, OP_BV_ROR},
    {BITWUZLA_KIND_BV_REDAND, OP_BV_REDAND},
    {BITWUZLA_KIND_BV_REDOR, OP_BV_REDOR},
    {BITWUZLA_KIND_BV_REDXOR, OP_BV_REDXOR},
    {BITWUZLA_KIND_BV_UADD_OVERFLOW, OP_BV_UADDO},
    {BITWUZLA_KIND_BV_SADD_OVERFLOW, OP_BV_SADDO},
    {BITWUZLA_KIND_BV_UMUL_OVERFLOW, OP_BV_UMULO},
    {BITWUZLA_KIND_BV_SMUL_OVERFLOW, OP_BV_SMULO},
    {BITWUZLA_KIND_BV_USUB_OVERFLOW, OP_BV_USUBO},
    {BITWUZLA_KIND_BV_SSUB_OVERFLOW, OP_BV_SSUBO},
    {BITWUZLA_KIND_BV_SDIV_OVERFLOW, OP_BV_SDIVO},
    {BITWUZLA_KIND_IFF, OP_IFF},
    /* Special treatment, not really a Bitwuzla kind. */
    {BITWUZLA_NUM_KINDS, OP_FP_TO_FP_FROM_REAL},
};

const BitwuzlaTerm*
BzlaTerm::get_bzla_term(Term term)
{
  return checked_cast<BzlaTerm*>(term.get())->d_term;
}

std::vector<Term>
BzlaTerm::bzla_terms_to_terms(const std::vector<const BitwuzlaTerm*>& terms)
{
  std::vector<Term> res;
  for (const BitwuzlaTerm* t : terms)
  {
    res.push_back(std::shared_ptr<BzlaTerm>(new BzlaTerm(t)));
  }
  return res;
}

//! [docs-bzla-term-bzla_terms_to_terms start]
std::vector<Term>
BzlaTerm::bzla_terms_to_terms(const BitwuzlaTerm** terms, size_t size)
{
  std::vector<Term> res;
  for (size_t i = 0; i < size; ++i)
  {
    res.push_back(std::shared_ptr<BzlaTerm>(new BzlaTerm(terms[i])));
  }
  return res;
}
//! [docs-bzla-term-bzla_terms_to_terms end]

std::vector<const BitwuzlaTerm*>
BzlaTerm::terms_to_bzla_terms(const std::vector<Term>& terms)
{
  std::vector<const BitwuzlaTerm*> res;
  for (auto& t : terms)
  {
    res.push_back(BzlaTerm::get_bzla_term(t));
  }
  return res;
}

BzlaTerm::BzlaTerm(const BitwuzlaTerm* term) : d_term(term) {}

BzlaTerm::~BzlaTerm() {}

size_t
BzlaTerm::hash() const
{
  return bitwuzla_term_hash(d_term);
}

bool
BzlaTerm::equals(const Term& other) const
{
  BzlaTerm* bzla_term = checked_cast<BzlaTerm*>(other.get());
  return d_term == bzla_term->d_term;
}

std::string
BzlaTerm::to_string() const
{
  FILE* tmp_file = std::tmpfile();
  bitwuzla_term_dump(d_term, "smt2", tmp_file);
  std::rewind(tmp_file);
  std::stringstream ss;
  int32_t ch;
  while ((ch = std::fgetc(tmp_file)) != EOF)
  {
    ss << (char) ch;
  }
  MURXLA_EXIT_ERROR(std::ferror(tmp_file))
      << "error while reading from tmp file";
  std::fclose(tmp_file);
  return ss.str();
}

bool
BzlaTerm::is_array() const
{
  return bitwuzla_term_is_array(d_term);
}

bool
BzlaTerm::is_bv() const
{
  return bitwuzla_term_is_bv(d_term);
}

bool
BzlaTerm::is_fp() const
{
  return bitwuzla_term_is_fp(d_term);
}

bool
BzlaTerm::is_fun() const
{
  return bitwuzla_term_is_fun(d_term);
}

bool
BzlaTerm::is_rm() const
{
  return bitwuzla_term_is_rm(d_term);
}

bool
BzlaTerm::is_bool_value() const
{
  return is_bool() && bitwuzla_term_is_bv_value(d_term);
}

bool
BzlaTerm::is_bv_value() const
{
  return bitwuzla_term_is_bv_value(d_term);
}

bool
BzlaTerm::is_fp_value() const
{
  return bitwuzla_term_is_fp_value(d_term);
}

bool
BzlaTerm::is_rm_value() const
{
  return bitwuzla_term_is_rm_value(d_term);
}

bool
BzlaTerm::is_special_value(const AbsTerm::SpecialValueKind& kind) const
{
  if (kind == AbsTerm::SPECIAL_VALUE_BV_ZERO)
  {
    return bitwuzla_term_is_bv_value_zero(d_term);
  }
  else if (kind == SPECIAL_VALUE_BV_ONE)
  {
    return bitwuzla_term_is_bv_value_one(d_term);
  }
  else if (kind == SPECIAL_VALUE_BV_ONES)
  {
    return bitwuzla_term_is_bv_value_ones(d_term);
  }
  else if (kind == SPECIAL_VALUE_BV_MIN_SIGNED)
  {
    return bitwuzla_term_is_bv_value_min_signed(d_term);
  }
  else if (kind == SPECIAL_VALUE_BV_MAX_SIGNED)
  {
    return bitwuzla_term_is_bv_value_max_signed(d_term);
  }
  else if (kind == SPECIAL_VALUE_FP_NAN)
  {
    return bitwuzla_term_is_fp_value_nan(d_term);
  }
  else if (kind == SPECIAL_VALUE_FP_POS_INF)
  {
    return bitwuzla_term_is_fp_value_pos_inf(d_term);
  }
  else if (kind == SPECIAL_VALUE_FP_NEG_INF)
  {
    return bitwuzla_term_is_fp_value_neg_inf(d_term);
  }
  else if (kind == SPECIAL_VALUE_FP_POS_ZERO)
  {
    return bitwuzla_term_is_fp_value_pos_zero(d_term);
  }
  else if (kind == SPECIAL_VALUE_FP_NEG_ZERO)
  {
    return bitwuzla_term_is_fp_value_neg_zero(d_term);
  }
  else if (kind == SPECIAL_VALUE_RM_RNA)
  {
    return bitwuzla_term_is_rm_value_rna(d_term);
  }
  else if (kind == SPECIAL_VALUE_RM_RNE)
  {
    return bitwuzla_term_is_rm_value_rne(d_term);
  }
  else if (kind == SPECIAL_VALUE_RM_RTN)
  {
    return bitwuzla_term_is_rm_value_rtn(d_term);
  }
  else if (kind == SPECIAL_VALUE_RM_RTP)
  {
    return bitwuzla_term_is_rm_value_rtp(d_term);
  }
  else if (kind == SPECIAL_VALUE_RM_RTZ)
  {
    return bitwuzla_term_is_rm_value_rtz(d_term);
  }
  return AbsTerm::is_special_value(kind);
}

bool
BzlaTerm::is_const() const
{
  return bitwuzla_term_is_const(d_term);
}

bool
BzlaTerm::is_value() const
{
  return bitwuzla_term_is_value(d_term);
}

bool
BzlaTerm::is_var() const
{
  return bitwuzla_term_is_var(d_term);
}

const Op::Kind&
BzlaTerm::get_kind() const
{
  BitwuzlaKind bzla_kind = bitwuzla_term_get_kind(d_term);
  return s_bzla_kinds_to_kinds.at(bzla_kind);
}

//! [docs-bzla-term-get_children start]
std::vector<Term>
BzlaTerm::get_children() const
{
  std::vector<Term> res;
  size_t size                   = 0;
  const BitwuzlaTerm** bzla_res = bitwuzla_term_get_children(d_term, &size);
  return bzla_terms_to_terms(bzla_res, size);
}
//! [docs-bzla-term-get_children end]

bool
BzlaTerm::is_indexed() const
{
  return bitwuzla_term_is_indexed(d_term);
}

size_t
BzlaTerm::get_num_indices() const
{
  size_t size;
  uint32_t* bzla_res = bitwuzla_term_get_indices(d_term, &size);
  (void) bzla_res;
  return size;
}

std::vector<std::string>
BzlaTerm::get_indices() const
{
  assert(is_indexed());
  std::vector<std::string> res;
  size_t size;
  uint32_t* bzla_res = bitwuzla_term_get_indices(d_term, &size);
  MURXLA_TEST(size);
  for (size_t i = 0; i < size; ++i)
  {
    res.push_back(std::to_string(bzla_res[i]));
  }
  return res;
}

uint32_t
BzlaTerm::get_bv_size() const
{
  assert(is_bv());
  return bitwuzla_term_bv_get_size(d_term);
}

uint32_t
BzlaTerm::get_fp_exp_size() const
{
  assert(is_fp());
  return bitwuzla_term_fp_get_exp_size(d_term);
}

uint32_t
BzlaTerm::get_fp_sig_size() const
{
  assert(is_fp());
  return bitwuzla_term_fp_get_sig_size(d_term);
}

Sort
BzlaTerm::get_array_index_sort() const
{
  assert(is_array());
  const BitwuzlaSort* bzla_res = bitwuzla_term_array_get_index_sort(d_term);
  return std::shared_ptr<BzlaSort>(
      new BzlaSort(bitwuzla_term_get_bitwuzla(d_term), bzla_res));
}

Sort
BzlaTerm::get_array_element_sort() const
{
  assert(is_array());
  const BitwuzlaSort* bzla_res = bitwuzla_term_array_get_element_sort(d_term);
  return std::shared_ptr<BzlaSort>(
      new BzlaSort(bitwuzla_term_get_bitwuzla(d_term), bzla_res));
}

uint32_t
BzlaTerm::get_fun_arity() const
{
  assert(is_fun());
  return bitwuzla_term_fun_get_arity(d_term);
}

Sort
BzlaTerm::get_fun_codomain_sort() const
{
  assert(is_fun());
  const BitwuzlaSort* bzla_res = bitwuzla_term_fun_get_codomain_sort(d_term);
  return std::shared_ptr<BzlaSort>(
      new BzlaSort(bitwuzla_term_get_bitwuzla(d_term), bzla_res));
}

std::vector<Sort>
BzlaTerm::get_fun_domain_sorts() const
{
  assert(is_fun());
  size_t size;
  const BitwuzlaSort** bzla_res =
      bitwuzla_term_fun_get_domain_sorts(d_term, &size);
  Bitwuzla* bzla = bitwuzla_term_get_bitwuzla(d_term);
  return BzlaSort::bzla_sorts_to_sorts(bzla, bzla_res, size);
}

/* -------------------------------------------------------------------------- */
/* BzlaSolver                                                                 */
/* -------------------------------------------------------------------------- */

BzlaSolver::~BzlaSolver()
{
  if (d_solver)
  {
    bitwuzla_delete(d_solver);
    d_solver = nullptr;
  }
}

void
BzlaSolver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = bitwuzla_new();

  /* Initialize Bitwuzla options */
  if (d_option_name_to_enum.empty())
  {
    for (int32_t i = 0; i < BITWUZLA_OPT_NUM_OPTS; ++i)
    {
      BitwuzlaOption opt = static_cast<BitwuzlaOption>(i);
      BitwuzlaOptionInfo info;
      bitwuzla_get_option_info(d_solver, opt, &info);
      d_option_name_to_enum.emplace(info.lng, opt);
    }
  }
}

void
BzlaSolver::delete_solver()
{
  assert(d_solver != nullptr);
  bitwuzla_delete(d_solver);
  d_solver = nullptr;
}

Bitwuzla*
BzlaSolver::get_solver()
{
  return d_solver;
}

bool
BzlaSolver::is_initialized() const
{
  return d_solver != nullptr;
}

const std::string
BzlaSolver::get_name() const
{
  return "Bitwuzla";
}

const std::string
BzlaSolver::get_profile() const
{
  return s_profile;
}

Sort
BzlaSolver::mk_sort(SortKind kind)
{
  MURXLA_CHECK_CONFIG(kind == SORT_BOOL || kind == SORT_RM)
      << "unsupported sort kind '" << kind
      << "' as argument to BzlaSolver::mk_sort, expected '" << SORT_BOOL
      << "' or '" << SORT_RM << "'";

  const BitwuzlaSort* bzla_res = kind == SORT_BOOL
                                     ? bitwuzla_mk_bool_sort(d_solver)
                                     : bitwuzla_mk_rm_sort(d_solver);
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaSort> res(new BzlaSort(d_solver, bzla_res));
  assert(res);
  return res;
}

Sort
BzlaSolver::mk_sort(SortKind kind, uint32_t size)
{
  MURXLA_CHECK_CONFIG(kind == SORT_BV)
      << "unsupported sort kind '" << kind
      << "' as argument to BzlaSolver::mk_sort, expected '" << SORT_BV << "'";

  const BitwuzlaSort* bzla_res = bitwuzla_mk_bv_sort(d_solver, size);
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaSort> res(new BzlaSort(d_solver, bzla_res));
  assert(res);
  return res;
}

Sort
BzlaSolver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  MURXLA_CHECK_CONFIG(kind == SORT_FP)
      << "unsupported sort kind '" << kind
      << "' as argument to BzlaSolver::mk_sort, expected '" << SORT_FP << "'";

  const BitwuzlaSort* bzla_res = bitwuzla_mk_fp_sort(d_solver, esize, ssize);
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaSort> res(new BzlaSort(d_solver, bzla_res));
  assert(res);
  return res;
}

Sort
BzlaSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  const BitwuzlaSort* bzla_res;

  switch (kind)
  {
    case SORT_ARRAY:
      bzla_res = bitwuzla_mk_array_sort(d_solver,
                                        BzlaSort::get_bzla_sort(sorts[0]),
                                        BzlaSort::get_bzla_sort(sorts[1]));
      break;

    case SORT_FUN:
    {
      const BitwuzlaSort* codomain = BzlaSort::get_bzla_sort(sorts.back());
      std::vector<const BitwuzlaSort*> domain;
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        domain.push_back(BzlaSort::get_bzla_sort(*it));
      }
      bzla_res = bitwuzla_mk_fun_sort(d_solver,
                                      static_cast<uint32_t>(domain.size()),
                                      domain.data(),
                                      codomain);
      break;
    }

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unsupported sort kind '" << kind
          << "' as argument to BzlaSolver::mk_sort, expected '" << SORT_ARRAY
          << "' or '" << SORT_FUN << "'";
  }
  std::shared_ptr<BzlaSort> res(new BzlaSort(d_solver, bzla_res));
  MURXLA_TEST(bzla_res);
  assert(res);
  return res;
}

Term
BzlaSolver::mk_var(Sort sort, const std::string& name)
{
  const BitwuzlaTerm* bzla_res;
  std::stringstream ss;
  std::string symbol;
  const char* cname = nullptr;

  /* Make sure that symbol is unique. */
  if (!name.empty())
  {
    ss << "sym" << d_num_symbols << "@" << name;
    ++d_num_symbols;
    symbol = ss.str();
    cname  = symbol.c_str();
  }

  bzla_res = bitwuzla_mk_var(d_solver, BzlaSort::get_bzla_sort(sort), cname);
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaTerm> res(new BzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BzlaSolver::mk_const(Sort sort, const std::string& name)
{
  const BitwuzlaTerm* bzla_res;
  std::stringstream ss;
  std::string symbol;
  const char* cname = nullptr;

  /* Make sure that symbol is unique. */
  if (!name.empty())
  {
    ss << "sym" << d_num_symbols << "@" << name;
    ++d_num_symbols;
    symbol = ss.str();
    cname  = symbol.c_str();
  }

  bzla_res = bitwuzla_mk_const(d_solver, BzlaSort::get_bzla_sort(sort), cname);
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaTerm> res(new BzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BzlaSolver::mk_fun(const std::string& name,
                   const std::vector<Term>& args,
                   Term body)
{
  std::vector<const BitwuzlaTerm*> bzla_args =
      BzlaTerm::terms_to_bzla_terms(args);
  bzla_args.push_back(BzlaTerm::get_bzla_term(body));

  const BitwuzlaTerm* bzla_res =
      bitwuzla_mk_term(d_solver,
                       BITWUZLA_KIND_LAMBDA,
                       static_cast<uint32_t>(bzla_args.size()),
                       bzla_args.data());
  bitwuzla_term_set_symbol(bzla_res, name.c_str());

  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaTerm> res(new BzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BzlaSolver::mk_value(Sort sort, bool value)
{
  MURXLA_CHECK_CONFIG(sort->is_bool())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BzlaSolver::mk_value, expected Boolean sort";

  const BitwuzlaTerm* bzla_res =
      value ? bitwuzla_mk_true(d_solver) : bitwuzla_mk_false(d_solver);
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaTerm> res(new BzlaTerm(bzla_res));
  assert(res);
  return res;
}

const BitwuzlaTerm*
BzlaSolver::mk_value_bv_uint64(Sort sort, uint64_t value)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BzlaSolver::mk_value, expected bit-vector sort";

  const BitwuzlaSort* bzla_sort = BzlaSort::get_bzla_sort(sort);
  const BitwuzlaTerm* bzla_res =
      bitwuzla_mk_bv_value_uint64(d_solver, bzla_sort, value);
  MURXLA_TEST(bzla_res);
  return bzla_res;
}

Term
BzlaSolver::mk_value(Sort sort, const std::string& value)
{
  MURXLA_CHECK_CONFIG(sort->is_fp())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BzlaSolver::mk_value, expected floating-point sort";

  uint32_t ew = sort->get_fp_exp_size();
  uint32_t sw = sort->get_fp_sig_size();
  assert(value.size() == ew + sw);

  const BitwuzlaSort* bzla_sort_1 = bitwuzla_mk_bv_sort(d_solver, 1);
  const BitwuzlaSort* bzla_sort_e = bitwuzla_mk_bv_sort(d_solver, ew);
  const BitwuzlaSort* bzla_sort_s = bitwuzla_mk_bv_sort(d_solver, sw - 1);
  const BitwuzlaTerm* bzla_sign   = bitwuzla_mk_bv_value(
      d_solver, bzla_sort_1, value.substr(0, 1).c_str(), BITWUZLA_BV_BASE_BIN);
  const BitwuzlaTerm* bzla_exp = bitwuzla_mk_bv_value(
      d_solver, bzla_sort_e, value.substr(1, ew).c_str(), BITWUZLA_BV_BASE_BIN);
  const BitwuzlaTerm* bzla_sig =
      bitwuzla_mk_bv_value(d_solver,
                           bzla_sort_s,
                           value.substr(1 + ew).c_str(),
                           BITWUZLA_BV_BASE_BIN);

  const BitwuzlaTerm* bzla_res =
      bitwuzla_mk_fp_value(d_solver, bzla_sign, bzla_exp, bzla_sig);
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaTerm> res(new BzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BzlaSolver::mk_value(Sort sort, const std::string& value, Base base)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BzlaSolver::mk_value, expected bit-vector sort";

  const BitwuzlaTerm* bzla_res;
  const BitwuzlaSort* bzla_sort = BzlaSort::get_bzla_sort(sort);
  uint32_t bw                   = sort->get_bv_size();
  int32_t ibase;
  BitwuzlaBVBase cbase;

  if (base == DEC)
  {
    ibase = 10;
    cbase = BITWUZLA_BV_BASE_DEC;
  }
  else if (base == HEX)
  {
    ibase = 16;
    cbase = BITWUZLA_BV_BASE_HEX;
  }
  else
  {
    assert(base == BIN);
    ibase = 2;
    cbase = BITWUZLA_BV_BASE_BIN;
  }

  if (bw <= 64 && d_rng.flip_coin())
  {
    bzla_res =
        mk_value_bv_uint64(sort, strtoull(value.c_str(), nullptr, ibase));
  }
  else
  {
    bzla_res = bitwuzla_mk_bv_value(d_solver, bzla_sort, value.c_str(), cbase);
  }
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaTerm> res(new BzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BzlaSolver::mk_special_value(Sort sort, const AbsTerm::SpecialValueKind& value)
{
  const BitwuzlaTerm* bzla_res  = 0;
  const BitwuzlaSort* bzla_sort = BzlaSort::get_bzla_sort(sort);
  std::string str;

  switch (sort->get_kind())
  {
    case SORT_BV:
      if (value == AbsTerm::SPECIAL_VALUE_BV_ZERO)
      {
        bzla_res = bitwuzla_mk_bv_zero(d_solver, bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_ONE)
      {
        bzla_res = bitwuzla_mk_bv_one(d_solver, bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_ONES)
      {
        bzla_res = bitwuzla_mk_bv_ones(d_solver, bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED)
      {
        bzla_res = bitwuzla_mk_bv_min_signed(d_solver, bzla_sort);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED);
        bzla_res = bitwuzla_mk_bv_max_signed(d_solver, bzla_sort);
      }
      break;

    case SORT_FP:
    {
      if (value == AbsTerm::SPECIAL_VALUE_FP_POS_INF)
      {
        bzla_res = bitwuzla_mk_fp_pos_inf(d_solver, bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_NEG_INF)
      {
        bzla_res = bitwuzla_mk_fp_neg_inf(d_solver, bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_POS_ZERO)
      {
        bzla_res = bitwuzla_mk_fp_pos_zero(d_solver, bzla_sort);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_NEG_ZERO)
      {
        bzla_res = bitwuzla_mk_fp_neg_zero(d_solver, bzla_sort);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_FP_NAN);
        bzla_res = bitwuzla_mk_fp_nan(d_solver, bzla_sort);
      }
    }
    break;

    case SORT_RM:
      if (value == AbsTerm::SPECIAL_VALUE_RM_RNA)
      {
        bzla_res = bitwuzla_mk_rm_value(d_solver, BITWUZLA_RM_RNA);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RNE)
      {
        bzla_res = bitwuzla_mk_rm_value(d_solver, BITWUZLA_RM_RNE);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RTN)
      {
        bzla_res = bitwuzla_mk_rm_value(d_solver, BITWUZLA_RM_RTN);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RTP)
      {
        bzla_res = bitwuzla_mk_rm_value(d_solver, BITWUZLA_RM_RTP);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_RM_RTZ);
        bzla_res = bitwuzla_mk_rm_value(d_solver, BITWUZLA_RM_RTZ);
      }
      break;

    default:
      MURXLA_CHECK_CONFIG(sort->is_bv())
          << "unexpected sort of kind '" << sort->get_kind()
          << "' as argument to BzlaSolver::mk_special_value, expected "
             "bit-vector, floating-point or RoundingMode sort";
  }

  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaTerm> res(new BzlaTerm(bzla_res));
  assert(res);
  return res;
}

Term
BzlaSolver::mk_term(const Op::Kind& kind,
                    const std::vector<Term>& args,
                    const std::vector<uint32_t>& indices)
{
  MURXLA_CHECK_CONFIG(BzlaTerm::s_kinds_to_bzla_kinds.find(kind)
                      != BzlaTerm::s_kinds_to_bzla_kinds.end())
      << "BzlaSolver: operator kind '" << kind << "' not configured";

  const BitwuzlaTerm* bzla_res = nullptr;
  size_t n_args                = args.size();
  size_t n_indices             = indices.size();
  BitwuzlaKind bzla_kind       = BzlaTerm::s_kinds_to_bzla_kinds.at(kind);
  std::vector<BitwuzlaTerm*> vars;
  std::vector<const BitwuzlaTerm*> bzla_args =
      BzlaTerm::terms_to_bzla_terms(args);

  if (n_indices)
  {
    if (n_args < 3 && n_indices < 3 && d_rng.flip_coin())
    {
      switch (n_args)
      {
        case 1:
          if (n_indices == 1)
          {
            bzla_res = bitwuzla_mk_term1_indexed1(
                d_solver, bzla_kind, bzla_args[0], indices[0]);
          }
          else
          {
            bzla_res = bitwuzla_mk_term1_indexed2(
                d_solver, bzla_kind, bzla_args[0], indices[0], indices[1]);
          }
          break;
        default:
          assert(n_args == 2);
          if (n_indices == 1)
          {
            bzla_res = bitwuzla_mk_term2_indexed1(
                d_solver, bzla_kind, bzla_args[0], bzla_args[1], indices[0]);
          }
          else
          {
            bzla_res = bitwuzla_mk_term2_indexed2(d_solver,
                                                  bzla_kind,
                                                  bzla_args[0],
                                                  bzla_args[1],
                                                  indices[0],
                                                  indices[1]);
          }
          break;
      }
    }
    else
    {
      bzla_res = bitwuzla_mk_term_indexed(d_solver,
                                          bzla_kind,
                                          static_cast<uint32_t>(n_args),
                                          bzla_args.data(),
                                          static_cast<uint32_t>(n_indices),
                                          indices.data());
    }
  }
  else
  {
    if (kind == BzlaTerm::OP_FP_TO_FP_FROM_REAL)
    {
      /* Bitwuzla only supports a very restricted version of to_fp from Real:
       * only from strings representing real or rational values. */

      const BitwuzlaSort* bzla_sort = bitwuzla_term_get_sort(bzla_args[1]);
      auto choice                   = d_rng.pick_one_of_three();
      if (choice == RNGenerator::Choice::FIRST)
      {
        bzla_res =
            bitwuzla_mk_fp_value_from_real(d_solver,
                                           bzla_sort,
                                           bzla_args[0],
                                           d_rng.pick_real_string().c_str());
      }
      else
      {
        bzla_res = bitwuzla_mk_fp_value_from_rational(
            d_solver,
            bzla_sort,
            bzla_args[0],
            d_rng
                .pick_dec_int_string(
                    d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX))
                .c_str(),
            d_rng
                .pick_dec_int_string(
                    d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX))
                .c_str());
      }
    }
    else
    {
      if (n_args <= 3 && d_rng.flip_coin())
      {
        switch (n_args)
        {
          case 1:
            bzla_res = bitwuzla_mk_term1(d_solver, bzla_kind, bzla_args[0]);
            break;
          case 2:
            bzla_res = bitwuzla_mk_term2(
                d_solver, bzla_kind, bzla_args[0], bzla_args[1]);
            break;
          default:
            assert(n_args == 3);
            bzla_res = bitwuzla_mk_term3(
                d_solver, bzla_kind, bzla_args[0], bzla_args[1], bzla_args[2]);
        }
      }
      else
      {
        bzla_res = bitwuzla_mk_term(d_solver,
                                    bzla_kind,
                                    static_cast<uint32_t>(n_args),
                                    bzla_args.data());
      }
    }
  }
  MURXLA_TEST(bzla_res);
  std::shared_ptr<BzlaTerm> res(new BzlaTerm(bzla_res));
  assert(res);
  return res;
}

Sort
BzlaSolver::get_sort(Term term, SortKind sort_kind)
{
  (void) sort_kind;
  return std::shared_ptr<BzlaSort>(new BzlaSort(
      d_solver, bitwuzla_term_get_sort(BzlaTerm::get_bzla_term(term))));
}

void
BzlaSolver::assert_formula(const Term& t)
{
  bitwuzla_assert(d_solver, BzlaTerm::get_bzla_term(t));
}

Solver::Result
BzlaSolver::check_sat()
{
  BitwuzlaResult res = bitwuzla_check_sat(d_solver);
  if (res == BITWUZLA_SAT) return Result::SAT;
  if (res == BITWUZLA_UNSAT) return Result::UNSAT;
  MURXLA_TEST(res == BITWUZLA_UNKNOWN);
  return Result::UNKNOWN;
}

Solver::Result
BzlaSolver::check_sat_assuming(const std::vector<Term>& assumptions)
{
  int32_t res;
  for (const Term& t : assumptions)
  {
    bitwuzla_assume(d_solver, BzlaTerm::get_bzla_term(t));
  }
  res = bitwuzla_check_sat(d_solver);
  if (res == BITWUZLA_SAT) return Result::SAT;
  if (res == BITWUZLA_UNSAT) return Result::UNSAT;
  MURXLA_TEST(res == BITWUZLA_UNKNOWN);
  return Result::UNKNOWN;
}

std::vector<Term>
BzlaSolver::get_unsat_assumptions()
{
  size_t n_assumptions;
  std::vector<Term> res;
  const BitwuzlaTerm** bzla_res =
      bitwuzla_get_unsat_assumptions(d_solver, &n_assumptions);
  for (uint32_t i = 0; i < n_assumptions; ++i)
  {
    res.push_back(
        std::shared_ptr<BzlaTerm>(new BzlaTerm((BitwuzlaTerm*) bzla_res[i])));
  }
  return res;
}

//! [docs-bzla-solver-get_unsat_core start]
std::vector<Term>
BzlaSolver::get_unsat_core()
{
  size_t size;
  std::vector<Term> res;
  const BitwuzlaTerm** bzla_res = bitwuzla_get_unsat_core(d_solver, &size);
  for (uint32_t i = 0; i < size; ++i)
  {
    res.push_back(
        std::shared_ptr<BzlaTerm>(new BzlaTerm((BitwuzlaTerm*) bzla_res[i])));
  }
  return res;
}
//! [docs-bzla-solver-get_unsat_core end]

std::vector<Term>
BzlaSolver::get_value(const std::vector<Term>& terms)
{
  std::vector<Term> res;
  std::vector<const BitwuzlaTerm*> bzla_res;
  std::vector<const BitwuzlaTerm*> bzla_terms =
      BzlaTerm::terms_to_bzla_terms(terms);

  for (const BitwuzlaTerm* t : bzla_terms)
  {
    bzla_res.push_back(bitwuzla_get_value(d_solver, t));
  }
  return BzlaTerm::bzla_terms_to_terms(bzla_res);
}

void
BzlaSolver::push(uint32_t n_levels)
{
  bitwuzla_push(d_solver, n_levels);
}

void
BzlaSolver::pop(uint32_t n_levels)
{
  bitwuzla_pop(d_solver, n_levels);
}

void
BzlaSolver::print_model()
{
  const char* fmt = d_rng.flip_coin() ? "btor" : "smt2";
  FILE* file      = fopen("/dev/null", "w");
  bitwuzla_print_model(d_solver, fmt, file);
  fclose(file);
}

void
BzlaSolver::reset()
{
  bitwuzla_reset(d_solver);
}

void
BzlaSolver::reset_assertions()
{
  /* Bitwuzla does not support this yet */
  assert(false);
}

/* -------------------------------------------------------------------------- */

bool
BzlaSolver::is_unsat_assumption(const Term& t) const
{
  return bitwuzla_is_unsat_assumption(d_solver, BzlaTerm::get_bzla_term(t));
}

/* -------------------------------------------------------------------------- */

namespace {
void
bzla_throw(const char* msg)
{
  throw MurxlaSolverOptionException(msg);
}
}  // namespace

void
BzlaSolver::set_opt(const std::string& opt, const std::string& value)
{
  if (opt == "produce-unsat-assumptions")
  {
    /* always enabled in Bitwuzla, can not be configured via set_opt */
    return;
  }

  BitwuzlaOption bzla_opt;
  if (opt == "produce-models")
  {
    bzla_opt = BITWUZLA_OPT_PRODUCE_MODELS;
  }
  else if (opt == "produce-unsat-cores")
  {
    bzla_opt = BITWUZLA_OPT_PRODUCE_UNSAT_CORES;
  }
  else
  {
    auto it = d_option_name_to_enum.find(opt);
    MURXLA_CHECK_CONFIG(it != d_option_name_to_enum.end())
        << "invalid option name '" << opt;
    bzla_opt = it->second;
  }

  BitwuzlaOptionInfo info;
  bitwuzla_get_option_info(d_solver, bzla_opt, &info);

  if (info.is_numeric)
  {
    uint32_t val =
        value == "true"
            ? 1
            : (value == "false" ? 0 : static_cast<uint32_t>(std::stoul(value)));

    if (bzla_opt == BITWUZLA_OPT_INCREMENTAL)
    {
      if (!val
          && bitwuzla_get_option(d_solver, BITWUZLA_OPT_PRODUCE_UNSAT_CORES))
      {
        return;
      }
    }
    bitwuzla_set_abort_callback(bzla_throw);
    bitwuzla_set_option(d_solver, bzla_opt, val);
    bitwuzla_set_abort_callback(nullptr);
    MURXLA_TEST(val == bitwuzla_get_option(d_solver, bzla_opt));
  }
  else
  {
    bitwuzla_set_abort_callback(bzla_throw);
    bitwuzla_set_option_str(d_solver, bzla_opt, value.c_str());
    bitwuzla_set_abort_callback(nullptr);
    // Note: When Bitwuzla is not built with all supported SAT solver, we'll
    // get a different value back if we want to enable a solver that is not
    // compiled in.
    if (bzla_opt != BITWUZLA_OPT_SAT_ENGINE)
    {
      MURXLA_TEST(
          !strcmp(value.c_str(), bitwuzla_get_option_str(d_solver, bzla_opt)));
    }
  }
}

std::string
BzlaSolver::get_option_name_incremental() const
{
  return "incremental";
}

std::string
BzlaSolver::get_option_name_model_gen() const
{
  return "produce-models";
}

std::string
BzlaSolver::get_option_name_unsat_assumptions() const
{
  /* always enabled in Bitwuzla, can not be configured via set_opt */
  return "produce-unsat-assumptions";
}

std::string
BzlaSolver::get_option_name_unsat_cores() const
{
  return "produce-unsat-cores";
}

bool
BzlaSolver::option_incremental_enabled() const
{
  return bitwuzla_get_option(d_solver, BITWUZLA_OPT_INCREMENTAL) > 0;
}

bool
BzlaSolver::option_model_gen_enabled() const
{
  return bitwuzla_get_option(d_solver, BITWUZLA_OPT_PRODUCE_MODELS) > 0;
}

bool
BzlaSolver::option_unsat_assumptions_enabled() const
{
  /* always enabled in Bitwuzla, can not be configured via set_opt */
  return true;
}

bool
BzlaSolver::option_unsat_cores_enabled() const
{
  return bitwuzla_get_option(d_solver, BITWUZLA_OPT_PRODUCE_UNSAT_CORES) > 0;
}

void
BzlaSolver::check_term(Term term)
{
  const BitwuzlaTerm* bzla_term = BzlaTerm::get_bzla_term(term);
  MURXLA_TEST(bitwuzla_term_get_bitwuzla(bzla_term) == d_solver);
}

/* -------------------------------------------------------------------------- */
/* OpKindManager configuration.                                               */
/* -------------------------------------------------------------------------- */

void
BzlaSolver::configure_opmgr(OpKindManager* opmgr) const
{
//! [docs-bzla-solver-configure_opmgr_bv_dec start]
  opmgr->add_op_kind(BzlaTerm::OP_BV_DEC, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
//! [docs-bzla-solver-configure_opmgr_bv_dec end]
  opmgr->add_op_kind(BzlaTerm::OP_BV_INC, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(
      BzlaTerm::OP_BV_REDAND, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BzlaTerm::OP_BV_REDOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BzlaTerm::OP_BV_REDXOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(
      BzlaTerm::OP_BV_UADDO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BzlaTerm::OP_BV_UMULO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BzlaTerm::OP_BV_USUBO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(BzlaTerm::OP_BV_ROL, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(BzlaTerm::OP_BV_ROR, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BzlaTerm::OP_BV_SADDO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BzlaTerm::OP_BV_SDIVO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BzlaTerm::OP_BV_SMULO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      BzlaTerm::OP_BV_SSUBO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  /* Bitwuzla only supports a very restricted version of to_fp from Real:
   * only from strings representing real or rational values. We thus define
   * this as a solver-specific operator with two arguments: a rounding mode
   * term, and an FP term (which is only needed to get an existing FP sort to
   * convert to).  This is a workaround for this very special case (we don't)
   * want to generalize it for all solvers because it is too special). */
  opmgr->add_op_kind(BzlaTerm::OP_FP_TO_FP_FROM_REAL,
                     2,
                     0,
                     SORT_FP,
                     {SORT_RM, SORT_FP},
                     THEORY_FP);

  opmgr->add_op_kind(
      BzlaTerm::OP_IFF, 2, 0, SORT_BOOL, {SORT_BOOL}, THEORY_BOOL);
}

/* -------------------------------------------------------------------------- */
/* Option configuration.                                                      */
/* -------------------------------------------------------------------------- */

//! [docs-bzla-solver-configure_options start]
void
BzlaSolver::configure_options(SolverManager* smgr) const
{
  Bitwuzla* bzla = bitwuzla_new();
  BitwuzlaOptionInfo info;
  for (int32_t i = 0; i < BITWUZLA_OPT_NUM_OPTS; ++i)
  {
    BitwuzlaOption opt = static_cast<BitwuzlaOption>(i);
    bitwuzla_get_option_info(bzla, opt, &info);
    if (info.is_numeric)
    {
      smgr->add_option(new SolverOptionNum<uint32_t>(info.lng,
                                                     info.numeric.min_val,
                                                     info.numeric.max_val,
                                                     info.numeric.def_val));
    }
    else
    {
      std::vector<std::string> values;
      for (size_t j = 0; j < info.string.num_values; ++j)
      {
        values.emplace_back(info.string.values[j]);
      }
      smgr->add_option(
          new SolverOptionList(info.lng, values, info.string.def_val));
    }
  }
  bitwuzla_delete(bzla);
}
//! [docs-bzla-solver-configure_options end]

/* -------------------------------------------------------------------------- */
/* FSM configuration.                                                         */
/* -------------------------------------------------------------------------- */

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
    BzlaSolver& bzla_solver       = dynamic_cast<BzlaSolver&>(d_solver);
    Bitwuzla* bzla                = bzla_solver.get_solver();
    const BitwuzlaTerm* bzla_term = BzlaTerm::get_bzla_term(term);
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
        assumptions.push_back(std::shared_ptr<BzlaTerm>(new BzlaTerm(bzla_eq)));
      }
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
  }
};

class BzlaActionGetBvValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-get-bv-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionGetBvValue(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

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
    BzlaSolver& bzla_solver       = dynamic_cast<BzlaSolver&>(d_solver);
    Bitwuzla* bzla                = bzla_solver.get_solver();
    const BitwuzlaTerm* bzla_term = BzlaTerm::get_bzla_term(term);
    const char* bv_val            = bitwuzla_get_bv_value(bzla, bzla_term);
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

class BzlaActionGetFpValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-get-fp-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionGetFpValue(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

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
    BzlaSolver& bzla_solver       = dynamic_cast<BzlaSolver&>(d_solver);
    Bitwuzla* bzla                = bzla_solver.get_solver();
    const BitwuzlaTerm* bzla_term = BzlaTerm::get_bzla_term(term);
    const char *fp_val_sign, *fp_val_exp, *fp_val_sig;
    bitwuzla_get_fp_value(
        bzla, bzla_term, &fp_val_sign, &fp_val_exp, &fp_val_sig);
    if (d_smgr.d_incremental)
    {
      /* assume assignment and check if result is still SAT */
      std::string fp_val(std::string(fp_val_sign) + std::string(fp_val_exp)
                         + std::string(fp_val_sig));
      Term term_fp_val = d_solver.mk_value(term->get_sort(), fp_val);
      std::vector<Term> assumptions{
          d_solver.mk_term(Op::EQUAL, {term, term_fp_val}, {})};
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
  }
};

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
    BzlaSolver& bzla_solver       = dynamic_cast<BzlaSolver&>(d_solver);
    Bitwuzla* bzla                = bzla_solver.get_solver();
    const BitwuzlaTerm* bzla_term = BzlaTerm::get_bzla_term(term);
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
        assumptions.push_back(std::shared_ptr<BzlaTerm>(new BzlaTerm(bzla_eq)));
      }
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
  }
};

class BzlaActionGetRmValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-get-rm-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionGetRmValue(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

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
    BzlaSolver& bzla_solver       = dynamic_cast<BzlaSolver&>(d_solver);
    Bitwuzla* bzla                = bzla_solver.get_solver();
    const BitwuzlaTerm* bzla_term = BzlaTerm::get_bzla_term(term);
    std::string rm_val(bitwuzla_get_rm_value(bzla, bzla_term));
    if (d_smgr.d_incremental)
    {
      AbsTerm::SpecialValueKind value;
      if (rm_val == "RNA")
      {
        value = AbsTerm::SPECIAL_VALUE_RM_RNA;
      }
      else if (rm_val == "RNE")
      {
        value = AbsTerm::SPECIAL_VALUE_RM_RNE;
      }
      else if (rm_val == "RTN")
      {
        value = AbsTerm::SPECIAL_VALUE_RM_RTN;
      }
      else if (rm_val == "RTP")
      {
        value = AbsTerm::SPECIAL_VALUE_RM_RTP;
      }
      else
      {
        assert(rm_val == "RTZ");
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

class BzlaActionIsUnsatAssumption : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-is-unsat-assumption";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionIsUnsatAssumption(SolverManager& smgr) : Action(smgr, s_name, NONE)
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
    BzlaSolver& bzla_solver = dynamic_cast<BzlaSolver&>(d_solver);
    (void) bitwuzla_is_unsat_assumption(bzla_solver.get_solver(),
                                        BzlaTerm::get_bzla_term(term));
  }
};

class BzlaActionFixateAssumptions : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-fixate-assumptions";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionFixateAssumptions(SolverManager& smgr) : Action(smgr, s_name, NONE)
  {
  }

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_incremental) return false;
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
    bitwuzla_fixate_assumptions(
        dynamic_cast<BzlaSolver&>(d_solver).get_solver());
  }
};

class BzlaActionResetAssumptions : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-reset-assumptions";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionResetAssumptions(SolverManager& smgr) : Action(smgr, s_name, NONE)
  {
  }

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_incremental) return false;
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
    d_smgr.clear_assumptions();
    bitwuzla_reset_assumptions(
        dynamic_cast<BzlaSolver&>(d_solver).get_solver());
  }
};

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
    BzlaSolver& solver = dynamic_cast<BzlaSolver&>(d_solver);
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
    bitwuzla_simplify(dynamic_cast<BzlaSolver&>(d_solver).get_solver());
  }
};

class BzlaActionSubstituteTerm : public Action
{
 public:
  /** The maximum number of terms to substitute terms in. */
  static constexpr uint32_t MAX_N_TERMS = 3;
  /** The maximum number of terms to be substituted. */
  static constexpr uint32_t MAX_N_SUBST_TERMS = 3;
  /** The name of this action. */
  inline static const Kind s_name = "bzla-substitute-term";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionSubstituteTerm(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

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
    BzlaSolver& bzla_solver = dynamic_cast<BzlaSolver&>(d_solver);
    Bitwuzla* bzla          = bzla_solver.get_solver();
    std::vector<const BitwuzlaTerm*> bzla_terms =
        BzlaTerm::terms_to_bzla_terms(terms);
    std::vector<const BitwuzlaTerm*> bzla_to_subst_terms =
        BzlaTerm::terms_to_bzla_terms(to_subst_terms);
    std::vector<const BitwuzlaTerm*> bzla_subst_terms =
        BzlaTerm::terms_to_bzla_terms(subst_terms);

    if (bzla_terms.size() == 1 && d_rng.flip_coin())
    {
      const BitwuzlaTerm* bzla_res =
          bitwuzla_substitute_term(bzla,
                                   bzla_terms[0],
                                   bzla_to_subst_terms.size(),
                                   bzla_to_subst_terms.data(),
                                   bzla_subst_terms.data());
      /* Note: The substituted term 'bzla_res' may or may not be already in the
       *       term DB. Since we can't always compute the exact level, we can't
       *       add the substituted term to the term DB. */
      MURXLA_TEST(bzla_res);
    }
    else
    {
      bitwuzla_substitute_terms(bzla,
                                bzla_terms.size(),
                                bzla_terms.data(),
                                bzla_to_subst_terms.size(),
                                bzla_to_subst_terms.data(),
                                bzla_subst_terms.data());
    }
  }

  /**
   * Collect all known sub terms (terms registered in the term DB) of a given
   * term. Performs a pre-order traversal over term.
   */
  std::vector<Term> get_sub_terms(Term term)
  {
    std::vector<Term> res;
    std::unordered_set<const BitwuzlaTerm*> bzla_res;
    const BitwuzlaTerm* bzla_term = BzlaTerm::get_bzla_term(term);
    std::vector<const BitwuzlaTerm*> to_visit{bzla_term};
    while (!to_visit.empty())
    {
      const BitwuzlaTerm* bzla_vterm = to_visit.back();
      to_visit.pop_back();
      size_t size = 0;
      const BitwuzlaTerm** bzla_children =
          bitwuzla_term_get_children(bzla_vterm, &size);
      for (size_t i = 0; i < size; ++i)
      {
        if (bitwuzla_term_is_const(bzla_children[i])
            && bzla_res.find(bzla_children[i]) == bzla_res.end())
        {
          bzla_res.insert(bzla_children[i]);
          to_visit.push_back(bzla_children[i]);
        }
      }
    }

    Bitwuzla* bzla =
        dynamic_cast<BzlaSolver&>(d_smgr.get_solver()).get_solver();
    for (const BitwuzlaTerm* bzla_t : bzla_res)
    {
      Sort s = std::shared_ptr<BzlaSort>(
          new BzlaSort(bzla, bitwuzla_term_get_sort(bzla_t)));
      s = d_smgr.find_sort(s);
      if (s->get_kind() == SORT_ANY) continue;
      Term t = std::shared_ptr<BzlaTerm>(new BzlaTerm(bzla_t));
      t      = d_smgr.find_term(t, s, s->get_kind());
      if (t == nullptr) continue;
      res.push_back(t);
    }
    return res;
  }
};

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
    (void) bitwuzla_term_set_symbol(BzlaTerm::get_bzla_term(term),
                                    symbol.c_str());
    MURXLA_TEST(
        std::string(bitwuzla_term_get_symbol(BzlaTerm::get_bzla_term(term)))
        == symbol);
  }
};

class BzlaActionTermIsEqualSort : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-term-is-equal-sort";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionTermIsEqualSort(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    Term term0 = d_smgr.pick_term();
    Term term1 = d_smgr.pick_term();
    run(term0, term1);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
    Term term0 = get_untraced_term(untrace_str_to_id(tokens[0]));
    Term term1 = get_untraced_term(untrace_str_to_id(tokens[1]));
    MURXLA_CHECK_TRACE_TERM(term0, tokens[0]);
    MURXLA_CHECK_TRACE_TERM(term1, tokens[1]);
    run(term0, term1);
    return {};
  }

 private:
  //! [docs-bzla-action-termisequalsort-run start]
  void run(Term term0, Term term1)
  {
    MURXLA_TRACE << get_kind() << " " << term0 << " " << term1;
    const BitwuzlaTerm* bzla_term0 = BzlaTerm::get_bzla_term(term0);
    const BitwuzlaTerm* bzla_term1 = BzlaTerm::get_bzla_term(term1);
    if (term0->get_sort()->equals(term1->get_sort()))
    {
      MURXLA_TEST(bitwuzla_term_is_equal_sort(bzla_term0, bzla_term1));
    }
  }
  //! [docs-bzla-action-termisequalsort-run end]
};

class BzlaActionMisc : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "bzla-misc";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BzlaActionMisc(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

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
    BzlaSolver& bzla_solver = dynamic_cast<BzlaSolver&>(d_smgr.get_solver());
    Bitwuzla* bzla          = bzla_solver.get_solver();

    const char* version = bitwuzla_version(bzla);
    MURXLA_TEST(version && std::string(version) != "");
    const char* copyright = bitwuzla_copyright(bzla);
    MURXLA_TEST(copyright && std::string(copyright) != "");
    const char* git_id = bitwuzla_git_id(bzla);
    MURXLA_TEST(git_id && std::string(git_id) != "");
  }
};

/* -------------------------------------------------------------------------- */

void
BzlaSolver::configure_fsm(FSM* fsm) const
{
  SolverManager& smgr = fsm->get_smgr();

  /* Retrieve existing states. */
  State* s_assert           = fsm->get_state(State::ASSERT);
  State* s_check_sat        = fsm->get_state(State::CHECK_SAT);
  State* s_create_sorts     = fsm->get_state(State::CREATE_SORTS);
  State* s_create_inputs    = fsm->get_state(State::CREATE_INPUTS);
  State* s_create_terms     = fsm->get_state(State::CREATE_TERMS);
  State* s_opt              = fsm->get_state(State::OPT);
  State* s_push_pop         = fsm->get_state(State::PUSH_POP);
  State* s_sat              = fsm->get_state(State::SAT);
  State* s_unsat            = fsm->get_state(State::UNSAT);
  State* s_decide_sat_unsat = fsm->get_state(State::DECIDE_SAT_UNSAT);

  auto t_default = fsm->new_action<TransitionDefault>();

  /* Modify precondition of existing states. */
  s_sat->update_precondition([&smgr]() {
    return smgr.d_sat_called && smgr.d_sat_result == Solver::Result::SAT;
  });

  /* Solver-specific states. */
  State* s_fix_reset_assumptions = fsm->new_state(STATE_FIX_RESET_ASSUMPTIONS);
  State* s_unknown = fsm->new_choice_state(STATE_UNKNOWN, [&smgr]() {
    return smgr.d_sat_called && smgr.d_sat_result == Solver::Result::UNKNOWN;
  });

  /* Add solver-specific actions and reconfigure existing states. */
  s_decide_sat_unsat->add_action(t_default, 1, s_unknown);
  // bitwuzla_get_array_value
  auto a_get_array_val = fsm->new_action<BzlaActionGetArrayValue>();
  s_sat->add_action(a_get_array_val, 2);
  // bitwuzla_get_bv_value
  auto a_get_bv_val = fsm->new_action<BzlaActionGetBvValue>();
  s_sat->add_action(a_get_bv_val, 2);
  // bitwuzla_get_fp_value
  auto a_get_fp_val = fsm->new_action<BzlaActionGetFpValue>();
  s_sat->add_action(a_get_fp_val, 2);
  // bitwuzla_get_fun_value
  auto a_get_fun_val = fsm->new_action<BzlaActionGetFunValue>();
  ;
  s_sat->add_action(a_get_fun_val, 2);
  // bitwuzla_get_rm_value
  auto a_get_rm_val = fsm->new_action<BzlaActionGetRmValue>();
  s_sat->add_action(a_get_rm_val, 2);
  // bitwuzla_is_unsat_assumption
  auto a_failed = fsm->new_action<BzlaActionIsUnsatAssumption>();
  fsm->add_action_to_all_states(a_failed, 100);
  // bitwuzla_fixate_assumptions
  // bitwuzla_reset_assumptions
  auto a_fix_assumptions   = fsm->new_action<BzlaActionFixateAssumptions>();
  auto a_reset_assumptions = fsm->new_action<BzlaActionResetAssumptions>();
  s_fix_reset_assumptions->add_action(a_fix_assumptions, 5);
  s_fix_reset_assumptions->add_action(a_reset_assumptions, 5);
  s_fix_reset_assumptions->add_action(t_default, 1, s_assert);
  fsm->add_action_to_all_states_next(t_default, 2, s_fix_reset_assumptions);
  // bitwuzla_simplify
  auto a_simplify = fsm->new_action<BzlaActionSimplify>();
  s_assert->add_action(a_simplify, 10000);
  s_create_sorts->add_action(a_simplify, 10000);
  s_create_inputs->add_action(a_simplify, 10000);
  s_create_terms->add_action(a_simplify, 10000);
  s_opt->add_action(a_simplify, 10000);
  s_push_pop->add_action(a_simplify, 10000);
  s_check_sat->add_action(a_simplify, 10000, s_create_terms);
  s_sat->add_action(a_simplify, 10000, s_create_terms);
  s_unsat->add_action(a_simplify, 10000, s_create_terms);
  // bitwuzla_substitute_term
  // bitwuzla_substitute_terms
  auto a_subst_term = fsm->new_action<BzlaActionSubstituteTerm>();
  fsm->add_action_to_all_states(a_subst_term, 1000);
  // bitwuzla_term_set_symbol
  auto a_set_symbol = fsm->new_action<BzlaActionTermSetSymbol>();
  fsm->add_action_to_all_states(a_set_symbol, 1000);
  // bitwuzla_term_is_equal_sort
  auto a_term_is_equal_sort = fsm->new_action<BzlaActionTermIsEqualSort>();
  s_create_inputs->add_action(a_term_is_equal_sort, 1000);
  s_create_terms->add_action(a_term_is_equal_sort, 1000);

  auto a_misc = fsm->new_action<BzlaActionMisc>();
  fsm->add_action_to_all_states(a_misc, 100000);

  /* Configure solver-specific states. */
  s_unknown->add_action(t_default, 1, s_check_sat);
}

void
BzlaSolver::disable_unsupported_actions(FSM* fsm) const
{
  fsm->disable_action(ActionResetAssertions::s_name);
  fsm->disable_action(ActionInstantiateSort::s_name);
}

}  // namespace bzla
}  // namespace murxla

#endif
