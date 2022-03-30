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

#include "cvc5_solver.hpp"

#include <algorithm>
#include <cassert>

#include "action.hpp"
#include "config.hpp"
#include "except.hpp"
#include "solver/cvc5/profile.hpp"
#include "solver_option.hpp"
#include "theory.hpp"

namespace murxla {
namespace cvc5 {

#define TRACE_SOLVER(FUNC, ...)                            \
  d_tracer(                                                \
      [](Tracer<Cvc5TracerData>& tracer, auto&&... args) { \
        tracer << "solver." << #FUNC;                      \
      },                                                   \
      [this](auto&&... args) {                             \
        return d_solver->FUNC(args...);                    \
      } __VA_OPT__(, ) __VA_ARGS__)

#define TRACE_METHOD(FUNC, FIRST, ...)                      \
  d_tracer(                                                 \
      [=](Tracer<Cvc5TracerData>& tracer, auto&&... args) { \
        tracer << FIRST << "." << #FUNC;                    \
      },                                                    \
      [=](auto&&... args) mutable {                         \
        return FIRST.FUNC(args...);                         \
      } __VA_OPT__(, ) __VA_ARGS__)

/* -------------------------------------------------------------------------- */
/* Cvc5Sort                                                                   */
/* -------------------------------------------------------------------------- */

::cvc5::Sort&
Cvc5Sort::get_cvc5_sort(Sort sort)
{
  return checked_cast<Cvc5Sort*>(sort.get())->d_sort;
}

size_t
Cvc5Sort::hash() const
{
  return std::hash<::cvc5::Sort>{}(d_sort);
}

bool
Cvc5Sort::equals(const Sort& other) const
{
  Cvc5Sort* cvc5_sort = checked_cast<Cvc5Sort*>(other.get());
  if (cvc5_sort)
  {
    return d_sort == cvc5_sort->d_sort;
  }
  return false;
}

bool
Cvc5Sort::not_equals(const Sort& other) const
{
  Cvc5Sort* cvc5_sort = checked_cast<Cvc5Sort*>(other.get());
  if (cvc5_sort)
  {
    return d_sort != cvc5_sort->d_sort;
  }
  return true;
}

std::string
Cvc5Sort::to_string() const
{
  return d_sort.toString();
}

bool
Cvc5Sort::is_array() const
{
  return d_sort.isArray();
}

bool
Cvc5Sort::is_bag() const
{
  return d_sort.isBag();
}

bool
Cvc5Sort::is_bool() const
{
  return d_sort.isBoolean();
}

bool
Cvc5Sort::is_bv() const
{
  return d_sort.isBitVector();
}

bool
Cvc5Sort::is_dt() const
{
  return d_sort.isDatatype();
}

bool
Cvc5Sort::is_dt_parametric() const
{
  if (d_sort.isDatatype())
  {
    return d_sort.getDatatype().isParametric();
  }
  return false;
}

bool
Cvc5Sort::is_dt_well_founded() const
{
  return d_sort.isDatatype() && d_sort.getDatatype().isWellFounded();
}

bool
Cvc5Sort::is_fp() const
{
  return d_sort.isFloatingPoint();
}

bool
Cvc5Sort::is_fun() const
{
  return d_sort.isFunction();
}

bool
Cvc5Sort::is_int() const
{
  return d_sort.isInteger();
}

bool
Cvc5Sort::is_real() const
{
  return d_sort.isReal();
}

bool
Cvc5Sort::is_rm() const
{
  return d_sort.isRoundingMode();
}

bool
Cvc5Sort::is_string() const
{
  return d_sort.isString();
}

bool
Cvc5Sort::is_uninterpreted() const
{
  return d_sort.isUninterpretedSort();
}

bool
Cvc5Sort::is_reglan() const
{
  return d_sort.isRegExp();
}

bool
Cvc5Sort::is_seq() const
{
  return d_sort.isSequence();
}

bool
Cvc5Sort::is_set() const
{
  return d_sort.isSet();
}

uint32_t
Cvc5Sort::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = d_sort.getBitVectorSize();
  MURXLA_TEST(res);
  return res;
}

uint32_t
Cvc5Sort::get_fp_exp_size() const
{
  assert(is_fp());
  uint32_t res = d_sort.getFloatingPointExponentSize();
  MURXLA_TEST(res);
  return res;
}

uint32_t
Cvc5Sort::get_fp_sig_size() const
{
  assert(is_fp());
  uint32_t res = d_sort.getFloatingPointSignificandSize();
  MURXLA_TEST(res);
  return res;
}

std::string
Cvc5Sort::get_dt_name() const
{
  assert(is_dt());
  return d_sort.getDatatype().getName();
}

uint32_t
Cvc5Sort::get_dt_num_cons() const
{
  return static_cast<uint32_t>(d_sort.getDatatype().getNumConstructors());
}

std::vector<std::string>
Cvc5Sort::get_dt_cons_names() const
{
  assert(is_dt());
  std::vector<std::string> res;
  ::cvc5::Datatype cvc5_dt      = d_sort.getDatatype();
  uint32_t n_ctors              = get_dt_num_cons();
  for (uint32_t i = 0; i < n_ctors; ++i)
  {
    res.push_back(cvc5_dt[i].getName());
  }
  return res;
}

uint32_t
Cvc5Sort::get_dt_cons_num_sels(const std::string& name) const
{
  assert(is_dt());
  ::cvc5::DatatypeConstructor cvc5_cons =
      d_sort.getDatatype().getConstructor(name);
  return static_cast<uint32_t>(cvc5_cons.getNumSelectors());
}

std::vector<std::string>
Cvc5Sort::get_dt_cons_sel_names(const std::string& name) const
{
  assert(is_dt());
  std::vector<std::string> res;
  ::cvc5::DatatypeConstructor cvc5_cons =
      d_sort.getDatatype().getConstructor(name);
  uint32_t n_sels = get_dt_cons_num_sels(name);
  for (uint32_t i = 0; i < n_sels; ++i)
  {
    res.push_back(cvc5_cons[i].getName());
  }
  return res;
}

Sort
Cvc5Sort::get_array_index_sort() const
{
  assert(is_array());
  ::cvc5::Sort cvc5_res = d_sort.getArrayIndexSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

Sort
Cvc5Sort::get_array_element_sort() const
{
  assert(is_array());
  ::cvc5::Sort cvc5_res = d_sort.getArrayElementSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

Sort
Cvc5Sort::get_bag_element_sort() const
{
  ::cvc5::Sort cvc5_res = d_sort.getBagElementSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

uint32_t
Cvc5Sort::get_fun_arity() const
{
  assert(is_fun());
  return static_cast<uint32_t>(d_sort.getFunctionArity());
}

Sort
Cvc5Sort::get_fun_codomain_sort() const
{
  assert(is_fun());
  ::cvc5::Sort cvc5_res = d_sort.getFunctionCodomainSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

std::vector<Sort>
Cvc5Sort::get_fun_domain_sorts() const
{
  assert(is_fun());
  std::vector<::cvc5::Sort> cvc5_res = d_sort.getFunctionDomainSorts();
  return cvc5_sorts_to_sorts(d_tracer, d_solver, cvc5_res);
}

Sort
Cvc5Sort::get_seq_element_sort() const
{
  ::cvc5::Sort cvc5_res = d_sort.getSequenceElementSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

Sort
Cvc5Sort::get_set_element_sort() const
{
  ::cvc5::Sort cvc5_res = d_sort.getSetElementSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

std::vector<::cvc5::Sort>
Cvc5Sort::sorts_to_cvc5_sorts(const std::vector<Sort>& sorts)
{
  std::vector<::cvc5::Sort> res;
  for (auto& s : sorts)
  {
    res.emplace_back(get_cvc5_sort(s));
  }
  return res;
}

std::vector<Sort>
Cvc5Sort::cvc5_sorts_to_sorts(Tracer<Cvc5TracerData>& tracer,
                              ::cvc5::Solver* cvc5,
                              const std::vector<::cvc5::Sort>& sorts)
{
  std::vector<Sort> res;
  for (auto& s : sorts)
  {
    res.emplace_back(new Cvc5Sort(tracer, cvc5, s));
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Term                                                                   */
/* -------------------------------------------------------------------------- */

// ##### TODO OPS

//  LAMBDA,
//  WITNESS,
//  CARDINALITY_CONSTRAINT,
//  CARDINALITY_VALUE,
//  HO_APPLY,

//  ## Arithmetic
//  POW,
//  EXPONENTIAL,

// ## Arrays
//  EQ_RANGE,

//  ## Separation Logic
//  SEP_NIL,
//  SEP_EMP,
//  SEP_PTO,
//  SEP_STAR,
//  SEP_WAND,

//  ## Quantifiers
//  INST_CLOSURE,
//  INST_PATTERN,
//  INST_NO_PATTERN,
//  INST_ATTRIBUTE,
//  INST_PATTERN_LIST,

std::unordered_map<Op::Kind, ::cvc5::Kind> Cvc5Term::s_kinds_to_cvc5_kinds = {
    /* Special Cases */
    {Op::UNDEFINED, ::cvc5::Kind::UNDEFINED_KIND},
    {Op::DISTINCT, ::cvc5::Kind::DISTINCT},
    {Op::EQUAL, ::cvc5::Kind::EQUAL},
    {Op::ITE, ::cvc5::Kind::ITE},

    /* Bool */
    {Op::AND, ::cvc5::Kind::AND},
    {Op::OR, ::cvc5::Kind::OR},
    {Op::NOT, ::cvc5::Kind::NOT},
    {Op::XOR, ::cvc5::Kind::XOR},
    {Op::IMPLIES, ::cvc5::Kind::IMPLIES},

    /* Arrays */
    {Op::ARRAY_SELECT, ::cvc5::Kind::SELECT},
    {Op::ARRAY_STORE, ::cvc5::Kind::STORE},

    /* BV */
    {Op::BV_EXTRACT, ::cvc5::Kind::BITVECTOR_EXTRACT},
    {Op::BV_REPEAT, ::cvc5::Kind::BITVECTOR_REPEAT},
    {Op::BV_ROTATE_LEFT, ::cvc5::Kind::BITVECTOR_ROTATE_LEFT},
    {Op::BV_ROTATE_RIGHT, ::cvc5::Kind::BITVECTOR_ROTATE_RIGHT},
    {Op::BV_SIGN_EXTEND, ::cvc5::Kind::BITVECTOR_SIGN_EXTEND},
    {Op::BV_ZERO_EXTEND, ::cvc5::Kind::BITVECTOR_ZERO_EXTEND},

    {Op::BV_CONCAT, ::cvc5::Kind::BITVECTOR_CONCAT},
    {Op::BV_AND, ::cvc5::Kind::BITVECTOR_AND},
    {Op::BV_OR, ::cvc5::Kind::BITVECTOR_OR},
    {Op::BV_XOR, ::cvc5::Kind::BITVECTOR_XOR},
    {Op::BV_MULT, ::cvc5::Kind::BITVECTOR_MULT},
    {Op::BV_ADD, ::cvc5::Kind::BITVECTOR_ADD},
    {Op::BV_NOT, ::cvc5::Kind::BITVECTOR_NOT},
    {Op::BV_NEG, ::cvc5::Kind::BITVECTOR_NEG},
    {Op::BV_NAND, ::cvc5::Kind::BITVECTOR_NAND},
    {Op::BV_NOR, ::cvc5::Kind::BITVECTOR_NOR},
    {Op::BV_XNOR, ::cvc5::Kind::BITVECTOR_XNOR},
    {Op::BV_COMP, ::cvc5::Kind::BITVECTOR_COMP},
    {Op::BV_SUB, ::cvc5::Kind::BITVECTOR_SUB},
    {Op::BV_UDIV, ::cvc5::Kind::BITVECTOR_UDIV},
    {Op::BV_UREM, ::cvc5::Kind::BITVECTOR_UREM},
    {Op::BV_UREM, ::cvc5::Kind::BITVECTOR_UREM},
    {Op::BV_SDIV, ::cvc5::Kind::BITVECTOR_SDIV},
    {Op::BV_SREM, ::cvc5::Kind::BITVECTOR_SREM},
    {Op::BV_SMOD, ::cvc5::Kind::BITVECTOR_SMOD},
    {Op::BV_SHL, ::cvc5::Kind::BITVECTOR_SHL},
    {Op::BV_LSHR, ::cvc5::Kind::BITVECTOR_LSHR},
    {Op::BV_ASHR, ::cvc5::Kind::BITVECTOR_ASHR},
    {Op::BV_ULT, ::cvc5::Kind::BITVECTOR_ULT},
    {Op::BV_ULE, ::cvc5::Kind::BITVECTOR_ULE},
    {Op::BV_UGT, ::cvc5::Kind::BITVECTOR_UGT},
    {Op::BV_UGE, ::cvc5::Kind::BITVECTOR_UGE},
    {Op::BV_SLT, ::cvc5::Kind::BITVECTOR_SLT},
    {Op::BV_SLE, ::cvc5::Kind::BITVECTOR_SLE},
    {Op::BV_SGT, ::cvc5::Kind::BITVECTOR_SGT},
    {Op::BV_SGE, ::cvc5::Kind::BITVECTOR_SGE},

    /* Datatypes */
    {Op::DT_APPLY_CONS, ::cvc5::Kind::APPLY_CONSTRUCTOR},
    {Op::DT_APPLY_SEL, ::cvc5::Kind::APPLY_SELECTOR},
    {Op::DT_APPLY_TESTER, ::cvc5::Kind::APPLY_TESTER},
    {Op::DT_APPLY_UPDATER, ::cvc5::Kind::APPLY_UPDATER},
    {Op::DT_MATCH, ::cvc5::Kind::MATCH},
    {Op::DT_MATCH_BIND_CASE, ::cvc5::Kind::MATCH_BIND_CASE},
    {Op::DT_MATCH_CASE, ::cvc5::Kind::MATCH_CASE},

    /* FP */
    {Op::FP_ABS, ::cvc5::Kind::FLOATINGPOINT_ABS},
    {Op::FP_ADD, ::cvc5::Kind::FLOATINGPOINT_ADD},
    {Op::FP_DIV, ::cvc5::Kind::FLOATINGPOINT_DIV},
    {Op::FP_EQ, ::cvc5::Kind::FLOATINGPOINT_EQ},
    {Op::FP_FMA, ::cvc5::Kind::FLOATINGPOINT_FMA},
    {Op::FP_FP, ::cvc5::Kind::FLOATINGPOINT_FP},
    {Op::FP_IS_NORMAL, ::cvc5::Kind::FLOATINGPOINT_IS_NORMAL},
    {Op::FP_IS_SUBNORMAL, ::cvc5::Kind::FLOATINGPOINT_IS_SUBNORMAL},
    {Op::FP_IS_INF, ::cvc5::Kind::FLOATINGPOINT_IS_INF},
    {Op::FP_IS_NAN, ::cvc5::Kind::FLOATINGPOINT_IS_NAN},
    {Op::FP_IS_NEG, ::cvc5::Kind::FLOATINGPOINT_IS_NEG},
    {Op::FP_IS_POS, ::cvc5::Kind::FLOATINGPOINT_IS_POS},
    {Op::FP_IS_ZERO, ::cvc5::Kind::FLOATINGPOINT_IS_ZERO},
    {Op::FP_LT, ::cvc5::Kind::FLOATINGPOINT_LT},
    {Op::FP_LEQ, ::cvc5::Kind::FLOATINGPOINT_LEQ},
    {Op::FP_GT, ::cvc5::Kind::FLOATINGPOINT_GT},
    {Op::FP_GEQ, ::cvc5::Kind::FLOATINGPOINT_GEQ},
    {Op::FP_MAX, ::cvc5::Kind::FLOATINGPOINT_MAX},
    {Op::FP_MIN, ::cvc5::Kind::FLOATINGPOINT_MIN},
    {Op::FP_MUL, ::cvc5::Kind::FLOATINGPOINT_MULT},
    {Op::FP_NEG, ::cvc5::Kind::FLOATINGPOINT_NEG},
    {Op::FP_REM, ::cvc5::Kind::FLOATINGPOINT_REM},
    {Op::FP_RTI, ::cvc5::Kind::FLOATINGPOINT_RTI},
    {Op::FP_SQRT, ::cvc5::Kind::FLOATINGPOINT_SQRT},
    {Op::FP_SUB, ::cvc5::Kind::FLOATINGPOINT_SUB},
    {Op::FP_TO_FP_FROM_BV, ::cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV},
    {Op::FP_TO_FP_FROM_SBV, ::cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_SBV},
    {Op::FP_TO_FP_FROM_FP, ::cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_FP},
    {Op::FP_TO_FP_FROM_UBV, ::cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_UBV},
    {Op::FP_TO_FP_FROM_REAL, ::cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_REAL},
    {Op::FP_TO_REAL, ::cvc5::Kind::FLOATINGPOINT_TO_REAL},
    {Op::FP_TO_SBV, ::cvc5::Kind::FLOATINGPOINT_TO_SBV},
    {Op::FP_TO_UBV, ::cvc5::Kind::FLOATINGPOINT_TO_UBV},

    /* Ints */
    {Op::INT_IS_DIV, ::cvc5::Kind::DIVISIBLE},
    {Op::INT_NEG, ::cvc5::Kind::NEG},
    {Op::INT_SUB, ::cvc5::Kind::SUB},
    {Op::INT_ADD, ::cvc5::Kind::ADD},
    {Op::INT_MUL, ::cvc5::Kind::MULT},
    {Op::INT_DIV, ::cvc5::Kind::INTS_DIVISION},
    {Op::INT_MOD, ::cvc5::Kind::INTS_MODULUS},
    {Op::INT_ABS, ::cvc5::Kind::ABS},
    {Op::INT_LT, ::cvc5::Kind::LT},
    {Op::INT_LTE, ::cvc5::Kind::LEQ},
    {Op::INT_GT, ::cvc5::Kind::GT},
    {Op::INT_GTE, ::cvc5::Kind::GEQ},
    {Op::INT_TO_REAL, ::cvc5::Kind::TO_REAL},

    /* Reals */
    {Op::REAL_NEG, ::cvc5::Kind::NEG},
    {Op::REAL_SUB, ::cvc5::Kind::SUB},
    {Op::REAL_ADD, ::cvc5::Kind::ADD},
    {Op::REAL_MUL, ::cvc5::Kind::MULT},
    {Op::REAL_DIV, ::cvc5::Kind::DIVISION},
    {Op::REAL_LT, ::cvc5::Kind::LT},
    {Op::REAL_LTE, ::cvc5::Kind::LEQ},
    {Op::REAL_GT, ::cvc5::Kind::GT},
    {Op::REAL_GTE, ::cvc5::Kind::GEQ},
    {Op::REAL_IS_INT, ::cvc5::Kind::IS_INTEGER},
    {Op::REAL_TO_INT, ::cvc5::Kind::TO_INTEGER},

    /* Quantifiers */
    {Op::FORALL, ::cvc5::Kind::FORALL},
    {Op::EXISTS, ::cvc5::Kind::EXISTS},

    /* Strings */
    {Op::STR_CONCAT, ::cvc5::Kind::STRING_CONCAT},
    {Op::STR_LEN, ::cvc5::Kind::STRING_LENGTH},
    {Op::STR_LT, ::cvc5::Kind::STRING_LT},
    {Op::STR_TO_RE, ::cvc5::Kind::STRING_TO_REGEXP},
    {Op::STR_IN_RE, ::cvc5::Kind::STRING_IN_REGEXP},
    {Op::STR_LE, ::cvc5::Kind::STRING_LEQ},
    {Op::STR_AT, ::cvc5::Kind::STRING_CHARAT},
    {Op::STR_SUBSTR, ::cvc5::Kind::STRING_SUBSTR},
    {Op::STR_PREFIXOF, ::cvc5::Kind::STRING_PREFIX},
    {Op::STR_SUFFIXOF, ::cvc5::Kind::STRING_SUFFIX},
    {Op::STR_CONTAINS, ::cvc5::Kind::STRING_CONTAINS},
    {Op::STR_INDEXOF, ::cvc5::Kind::STRING_INDEXOF},
    {Op::STR_REPLACE, ::cvc5::Kind::STRING_REPLACE},
    {Op::STR_REPLACE_ALL, ::cvc5::Kind::STRING_REPLACE_ALL},
    {Op::STR_REPLACE_RE, ::cvc5::Kind::STRING_REPLACE_RE},
    {Op::STR_REPLACE_RE_ALL, ::cvc5::Kind::STRING_REPLACE_RE_ALL},
    {Op::STR_IS_DIGIT, ::cvc5::Kind::STRING_IS_DIGIT},
    {Op::STR_TO_CODE, ::cvc5::Kind::STRING_TO_CODE},
    {Op::STR_FROM_CODE, ::cvc5::Kind::STRING_FROM_CODE},
    {Op::STR_TO_INT, ::cvc5::Kind::STRING_TO_INT},
    {Op::STR_FROM_INT, ::cvc5::Kind::STRING_FROM_INT},
    {Op::RE_ALL, ::cvc5::Kind::REGEXP_ALL},
    {Op::RE_ALLCHAR, ::cvc5::Kind::REGEXP_ALLCHAR},
    {Op::RE_COMP, ::cvc5::Kind::REGEXP_COMPLEMENT},
    {Op::RE_CONCAT, ::cvc5::Kind::REGEXP_CONCAT},
    {Op::RE_DIFF, ::cvc5::Kind::REGEXP_DIFF},
    {Op::RE_INTER, ::cvc5::Kind::REGEXP_INTER},
    {Op::RE_LOOP, ::cvc5::Kind::REGEXP_LOOP},
    {Op::RE_NONE, ::cvc5::Kind::REGEXP_NONE},
    {Op::RE_OPT, ::cvc5::Kind::REGEXP_OPT},
    {Op::RE_PLUS, ::cvc5::Kind::REGEXP_PLUS},
    {Op::RE_POW, ::cvc5::Kind::REGEXP_REPEAT},
    {Op::RE_RANGE, ::cvc5::Kind::REGEXP_RANGE},
    {Op::RE_STAR, ::cvc5::Kind::REGEXP_STAR},
    {Op::RE_UNION, ::cvc5::Kind::REGEXP_UNION},

    /* Transcendentals */
    {Op::TRANS_PI, ::cvc5::Kind::PI},
    {Op::TRANS_SINE, ::cvc5::Kind::SINE},
    {Op::TRANS_COSINE, ::cvc5::Kind::COSINE},
    {Op::TRANS_TANGENT, ::cvc5::Kind::TANGENT},
    {Op::TRANS_COTANGENT, ::cvc5::Kind::COTANGENT},
    {Op::TRANS_SECANT, ::cvc5::Kind::SECANT},
    {Op::TRANS_COSECANT, ::cvc5::Kind::COSECANT},
    {Op::TRANS_ARCSINE, ::cvc5::Kind::ARCSINE},
    {Op::TRANS_ARCCOSINE, ::cvc5::Kind::ARCCOSINE},
    {Op::TRANS_ARCTANGENT, ::cvc5::Kind::ARCTANGENT},
    {Op::TRANS_ARCCOSECANT, ::cvc5::Kind::ARCCOSECANT},
    {Op::TRANS_ARCSECANT, ::cvc5::Kind::ARCSECANT},
    {Op::TRANS_ARCCOTANGENT, ::cvc5::Kind::ARCCOTANGENT},
    {Op::TRANS_SQRT, ::cvc5::Kind::SQRT},

    /* UF */
    {Op::UF_APPLY, ::cvc5::Kind::APPLY_UF},

    /* Non-standardized theories */
    // Bag
    {Op::BAG_UNION_MAX, ::cvc5::Kind::BAG_UNION_MAX},
    {Op::BAG_UNION_DISJOINT, ::cvc5::Kind::BAG_UNION_DISJOINT},
    {Op::BAG_INTERSECTION_MIN, ::cvc5::Kind::BAG_INTER_MIN},
    {Op::BAG_DIFFERENCE_SUBTRACT, ::cvc5::Kind::BAG_DIFFERENCE_SUBTRACT},
    {Op::BAG_DIFFERENCE_REMOVE, ::cvc5::Kind::BAG_DIFFERENCE_REMOVE},
    {Op::BAG_SUBBAG, ::cvc5::Kind::BAG_SUBBAG},
    {Op::BAG_COUNT, ::cvc5::Kind::BAG_COUNT},
    {Op::BAG_DUPLICATE_REMOVAL, ::cvc5::Kind::BAG_DUPLICATE_REMOVAL},
    {Op::BAG_MAKE, ::cvc5::Kind::BAG_MAKE},
    {Op::BAG_CARD, ::cvc5::Kind::BAG_CARD},
    {Op::BAG_CHOOSE, ::cvc5::Kind::BAG_CHOOSE},
    {Op::BAG_IS_SINGLETON, ::cvc5::Kind::BAG_IS_SINGLETON},
    {Op::BAG_FROM_SET, ::cvc5::Kind::BAG_FROM_SET},
    {Op::BAG_TO_SET, ::cvc5::Kind::BAG_TO_SET},
    {Op::BAG_MAP, ::cvc5::Kind::BAG_MAP},
    // Sequences
    {Op::SEQ_CONCAT, ::cvc5::Kind::SEQ_CONCAT},
    {Op::SEQ_LENGTH, ::cvc5::Kind::SEQ_LENGTH},
    {Op::SEQ_EXTRACT, ::cvc5::Kind::SEQ_EXTRACT},
    {Op::SEQ_UPDATE, ::cvc5::Kind::SEQ_UPDATE},
    {Op::SEQ_AT, ::cvc5::Kind::SEQ_AT},
    {Op::SEQ_CONTAINS, ::cvc5::Kind::SEQ_CONTAINS},
    {Op::SEQ_INDEXOF, ::cvc5::Kind::SEQ_INDEXOF},
    {Op::SEQ_REPLACE, ::cvc5::Kind::SEQ_REPLACE},
    {Op::SEQ_REPLACE_ALL, ::cvc5::Kind::SEQ_REPLACE_ALL},
    {Op::SEQ_REV, ::cvc5::Kind::SEQ_REV},
    {Op::SEQ_PREFIX, ::cvc5::Kind::SEQ_PREFIX},
    {Op::SEQ_SUFFIX, ::cvc5::Kind::SEQ_SUFFIX},
    {Op::SEQ_UNIT, ::cvc5::Kind::SEQ_UNIT},
    {Op::SEQ_NTH, ::cvc5::Kind::SEQ_NTH},
    // Sets
    {Op::SET_CARD, ::cvc5::Kind::SET_CARD},
    {Op::SET_COMPLEMENT, ::cvc5::Kind::SET_COMPLEMENT},
    {Op::SET_COMPREHENSION, ::cvc5::Kind::SET_COMPREHENSION},
    {Op::SET_CHOOSE, ::cvc5::Kind::SET_CHOOSE},
    {Op::SET_INTERSECTION, ::cvc5::Kind::SET_INTER},
    {Op::SET_INSERT, ::cvc5::Kind::SET_INSERT},
    {Op::SET_IS_SINGLETON, ::cvc5::Kind::SET_IS_SINGLETON},
    {Op::SET_UNION, ::cvc5::Kind::SET_UNION},
    {Op::SET_MEMBER, ::cvc5::Kind::SET_MEMBER},
    {Op::SET_MINUS, ::cvc5::Kind::SET_MINUS},
    {Op::SET_SINGLETON, ::cvc5::Kind::SET_SINGLETON},
    {Op::SET_SUBSET, ::cvc5::Kind::SET_SUBSET},
    //{Op::REL_JOIN, ::cvc5::Kind::RELATION_JOIN},
    //{Op::REL_JOIN_IMAGE, ::cvc5::Kind::RELATION_JOIN_IMAGE},
    //{Op::REL_IDEN, ::cvc5::Kind::RELATION_IDEN},
    //{Op::REL_PRODUCT, ::cvc5::Kind::RELATION_PRODUCT},
    //{Op::REL_TCLOSURE, ::cvc5::Kind::RELATION_TCLOSURE},
    //{Op::REL_TRANSPOSE, ::cvc5::Kind::RELATION_TRANSPOSE},

    /* Solver-specific operators */
    // BV
    {OP_BV_REDOR, ::cvc5::Kind::BITVECTOR_REDOR},
    {OP_BV_REDAND, ::cvc5::Kind::BITVECTOR_REDAND},
    {OP_BV_ULTBV, ::cvc5::Kind::BITVECTOR_ULTBV},
    {OP_BV_SLTBV, ::cvc5::Kind::BITVECTOR_SLTBV},
    {OP_BV_ITE, ::cvc5::Kind::BITVECTOR_ITE},
    // Datatypes
    {OP_DT_SIZE, ::cvc5::Kind::DT_SIZE},
    // Int
    {OP_BV_TO_NAT, ::cvc5::Kind::BITVECTOR_TO_NAT},
    {OP_INT_IAND, ::cvc5::Kind::IAND},
    {OP_INT_TO_BV, ::cvc5::Kind::INT_TO_BITVECTOR},
    {OP_INT_POW2, ::cvc5::Kind::POW2},
    // Strings
    {OP_STRING_UPDATE, ::cvc5::Kind::STRING_UPDATE},
    {OP_STRING_TOLOWER, ::cvc5::Kind::STRING_TO_LOWER},
    {OP_STRING_TOUPPER, ::cvc5::Kind::STRING_TO_UPPER},
    {OP_STRING_REV, ::cvc5::Kind::STRING_REV},
};

std::unordered_map<::cvc5::Kind, Op::Kind> Cvc5Term::s_cvc5_kinds_to_kinds = {
    {::cvc5::Kind::INTERNAL_KIND, Op::INTERNAL},
    /* Leaf Kinds */
    {::cvc5::Kind::CONSTANT, Op::CONSTANT},
    //{::cvc5::Kind::CONST_ARRAY, Op::CONST_ARRAY},
    {::cvc5::Kind::CONST_BOOLEAN, Op::VALUE},
    {::cvc5::Kind::CONST_BITVECTOR, Op::VALUE},
    {::cvc5::Kind::CONST_FLOATINGPOINT, Op::VALUE},
    {::cvc5::Kind::CONST_RATIONAL, Op::VALUE},
    {::cvc5::Kind::CONST_ROUNDINGMODE, Op::VALUE},
    {::cvc5::Kind::CONST_SEQUENCE, Op::VALUE},
    {::cvc5::Kind::CONST_STRING, Op::VALUE},
    {::cvc5::Kind::VARIABLE, Op::VARIABLE},

    /* Special Cases */
    {::cvc5::Kind::UNDEFINED_KIND, Op::UNDEFINED},
    {::cvc5::Kind::DISTINCT, Op::DISTINCT},
    {::cvc5::Kind::EQUAL, Op::EQUAL},
    {::cvc5::Kind::ITE, Op::ITE},

    /* Bool */
    {::cvc5::Kind::AND, Op::AND},
    {::cvc5::Kind::OR, Op::OR},
    {::cvc5::Kind::NOT, Op::NOT},
    {::cvc5::Kind::XOR, Op::XOR},
    {::cvc5::Kind::IMPLIES, Op::IMPLIES},

    /* Arrays */
    {::cvc5::Kind::SELECT, Op::ARRAY_SELECT},
    {::cvc5::Kind::STORE, Op::ARRAY_STORE},

    /* BV */
    {::cvc5::Kind::BITVECTOR_EXTRACT, Op::BV_EXTRACT},
    {::cvc5::Kind::BITVECTOR_REPEAT, Op::BV_REPEAT},
    {::cvc5::Kind::BITVECTOR_ROTATE_LEFT, Op::BV_ROTATE_LEFT},
    {::cvc5::Kind::BITVECTOR_ROTATE_RIGHT, Op::BV_ROTATE_RIGHT},
    {::cvc5::Kind::BITVECTOR_SIGN_EXTEND, Op::BV_SIGN_EXTEND},
    {::cvc5::Kind::BITVECTOR_ZERO_EXTEND, Op::BV_ZERO_EXTEND},

    {::cvc5::Kind::BITVECTOR_CONCAT, Op::BV_CONCAT},
    {::cvc5::Kind::BITVECTOR_AND, Op::BV_AND},
    {::cvc5::Kind::BITVECTOR_OR, Op::BV_OR},
    {::cvc5::Kind::BITVECTOR_XOR, Op::BV_XOR},
    {::cvc5::Kind::BITVECTOR_MULT, Op::BV_MULT},
    {::cvc5::Kind::BITVECTOR_ADD, Op::BV_ADD},
    {::cvc5::Kind::BITVECTOR_NOT, Op::BV_NOT},
    {::cvc5::Kind::BITVECTOR_NEG, Op::BV_NEG},
    {::cvc5::Kind::BITVECTOR_NAND, Op::BV_NAND},
    {::cvc5::Kind::BITVECTOR_NOR, Op::BV_NOR},
    {::cvc5::Kind::BITVECTOR_XNOR, Op::BV_XNOR},
    {::cvc5::Kind::BITVECTOR_COMP, Op::BV_COMP},
    {::cvc5::Kind::BITVECTOR_SUB, Op::BV_SUB},
    {::cvc5::Kind::BITVECTOR_UDIV, Op::BV_UDIV},
    {::cvc5::Kind::BITVECTOR_UREM, Op::BV_UREM},
    {::cvc5::Kind::BITVECTOR_UREM, Op::BV_UREM},
    {::cvc5::Kind::BITVECTOR_SDIV, Op::BV_SDIV},
    {::cvc5::Kind::BITVECTOR_SREM, Op::BV_SREM},
    {::cvc5::Kind::BITVECTOR_SMOD, Op::BV_SMOD},
    {::cvc5::Kind::BITVECTOR_SHL, Op::BV_SHL},
    {::cvc5::Kind::BITVECTOR_LSHR, Op::BV_LSHR},
    {::cvc5::Kind::BITVECTOR_ASHR, Op::BV_ASHR},
    {::cvc5::Kind::BITVECTOR_ULT, Op::BV_ULT},
    {::cvc5::Kind::BITVECTOR_ULE, Op::BV_ULE},
    {::cvc5::Kind::BITVECTOR_UGT, Op::BV_UGT},
    {::cvc5::Kind::BITVECTOR_UGE, Op::BV_UGE},
    {::cvc5::Kind::BITVECTOR_SLT, Op::BV_SLT},
    {::cvc5::Kind::BITVECTOR_SLE, Op::BV_SLE},
    {::cvc5::Kind::BITVECTOR_SGT, Op::BV_SGT},
    {::cvc5::Kind::BITVECTOR_SGE, Op::BV_SGE},

    /* Datatypes */
    {::cvc5::Kind::APPLY_CONSTRUCTOR, Op::DT_APPLY_CONS},
    {::cvc5::Kind::APPLY_SELECTOR, Op::DT_APPLY_SEL},
    {::cvc5::Kind::APPLY_TESTER, Op::DT_APPLY_TESTER},
    {::cvc5::Kind::APPLY_UPDATER, Op::DT_APPLY_UPDATER},
    {::cvc5::Kind::MATCH, Op::DT_MATCH},
    {::cvc5::Kind::MATCH_BIND_CASE, Op::DT_MATCH_BIND_CASE},
    {::cvc5::Kind::MATCH_CASE, Op::DT_MATCH_CASE},

    /* FP */
    {::cvc5::Kind::FLOATINGPOINT_ABS, Op::FP_ABS},
    {::cvc5::Kind::FLOATINGPOINT_ADD, Op::FP_ADD},
    {::cvc5::Kind::FLOATINGPOINT_DIV, Op::FP_DIV},
    {::cvc5::Kind::FLOATINGPOINT_EQ, Op::FP_EQ},
    {::cvc5::Kind::FLOATINGPOINT_FMA, Op::FP_FMA},
    {::cvc5::Kind::FLOATINGPOINT_FP, Op::FP_FP},
    {::cvc5::Kind::FLOATINGPOINT_IS_NORMAL, Op::FP_IS_NORMAL},
    {::cvc5::Kind::FLOATINGPOINT_IS_SUBNORMAL, Op::FP_IS_SUBNORMAL},
    {::cvc5::Kind::FLOATINGPOINT_IS_INF, Op::FP_IS_INF},
    {::cvc5::Kind::FLOATINGPOINT_IS_NAN, Op::FP_IS_NAN},
    {::cvc5::Kind::FLOATINGPOINT_IS_NEG, Op::FP_IS_NEG},
    {::cvc5::Kind::FLOATINGPOINT_IS_POS, Op::FP_IS_POS},
    {::cvc5::Kind::FLOATINGPOINT_IS_ZERO, Op::FP_IS_ZERO},
    {::cvc5::Kind::FLOATINGPOINT_LT, Op::FP_LT},
    {::cvc5::Kind::FLOATINGPOINT_LEQ, Op::FP_LEQ},
    {::cvc5::Kind::FLOATINGPOINT_GT, Op::FP_GT},
    {::cvc5::Kind::FLOATINGPOINT_GEQ, Op::FP_GEQ},
    {::cvc5::Kind::FLOATINGPOINT_MAX, Op::FP_MAX},
    {::cvc5::Kind::FLOATINGPOINT_MIN, Op::FP_MIN},
    {::cvc5::Kind::FLOATINGPOINT_MULT, Op::FP_MUL},
    {::cvc5::Kind::FLOATINGPOINT_NEG, Op::FP_NEG},
    {::cvc5::Kind::FLOATINGPOINT_REM, Op::FP_REM},
    {::cvc5::Kind::FLOATINGPOINT_RTI, Op::FP_RTI},
    {::cvc5::Kind::FLOATINGPOINT_SQRT, Op::FP_SQRT},
    {::cvc5::Kind::FLOATINGPOINT_SUB, Op::FP_SUB},
    {::cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV, Op::FP_TO_FP_FROM_BV},
    {::cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_SBV, Op::FP_TO_FP_FROM_SBV},
    {::cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_FP, Op::FP_TO_FP_FROM_FP},
    {::cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_UBV, Op::FP_TO_FP_FROM_UBV},
    {::cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_REAL, Op::FP_TO_FP_FROM_REAL},
    {::cvc5::Kind::FLOATINGPOINT_TO_REAL, Op::FP_TO_REAL},
    {::cvc5::Kind::FLOATINGPOINT_TO_SBV, Op::FP_TO_SBV},
    {::cvc5::Kind::FLOATINGPOINT_TO_UBV, Op::FP_TO_UBV},

    /* Ints */
    {::cvc5::Kind::DIVISIBLE, Op::INT_IS_DIV},
    {::cvc5::Kind::NEG, Op::INT_NEG},
    {::cvc5::Kind::SUB, Op::INT_SUB},
    {::cvc5::Kind::ADD, Op::INT_ADD},
    {::cvc5::Kind::MULT, Op::INT_MUL},
    {::cvc5::Kind::INTS_DIVISION, Op::INT_DIV},
    {::cvc5::Kind::INTS_MODULUS, Op::INT_MOD},
    {::cvc5::Kind::ABS, Op::INT_ABS},
    {::cvc5::Kind::LT, Op::INT_LT},
    {::cvc5::Kind::LEQ, Op::INT_LTE},
    {::cvc5::Kind::GT, Op::INT_GT},
    {::cvc5::Kind::GEQ, Op::INT_GTE},
    {::cvc5::Kind::TO_REAL, Op::INT_TO_REAL},

    /* Reals */
    {::cvc5::Kind::NEG, Op::REAL_NEG},
    {::cvc5::Kind::SUB, Op::REAL_SUB},
    {::cvc5::Kind::ADD, Op::REAL_ADD},
    {::cvc5::Kind::MULT, Op::REAL_MUL},
    {::cvc5::Kind::DIVISION, Op::REAL_DIV},
    {::cvc5::Kind::LT, Op::REAL_LT},
    {::cvc5::Kind::LEQ, Op::REAL_LTE},
    {::cvc5::Kind::GT, Op::REAL_GT},
    {::cvc5::Kind::GEQ, Op::REAL_GTE},
    {::cvc5::Kind::IS_INTEGER, Op::REAL_IS_INT},
    {::cvc5::Kind::TO_INTEGER, Op::REAL_TO_INT},

    /* Quantifiers */
    {::cvc5::Kind::FORALL, Op::FORALL},
    {::cvc5::Kind::EXISTS, Op::EXISTS},

    /* Strings */
    {::cvc5::Kind::STRING_CONCAT, Op::STR_CONCAT},
    {::cvc5::Kind::STRING_LENGTH, Op::STR_LEN},
    {::cvc5::Kind::STRING_LT, Op::STR_LT},
    {::cvc5::Kind::STRING_TO_REGEXP, Op::STR_TO_RE},
    {::cvc5::Kind::STRING_IN_REGEXP, Op::STR_IN_RE},
    {::cvc5::Kind::STRING_LEQ, Op::STR_LE},
    {::cvc5::Kind::STRING_CHARAT, Op::STR_AT},
    {::cvc5::Kind::STRING_SUBSTR, Op::STR_SUBSTR},
    {::cvc5::Kind::STRING_PREFIX, Op::STR_PREFIXOF},
    {::cvc5::Kind::STRING_SUFFIX, Op::STR_SUFFIXOF},
    {::cvc5::Kind::STRING_CONTAINS, Op::STR_CONTAINS},
    {::cvc5::Kind::STRING_INDEXOF, Op::STR_INDEXOF},
    {::cvc5::Kind::STRING_REPLACE, Op::STR_REPLACE},
    {::cvc5::Kind::STRING_REPLACE_ALL, Op::STR_REPLACE_ALL},
    {::cvc5::Kind::STRING_REPLACE_RE, Op::STR_REPLACE_RE},
    {::cvc5::Kind::STRING_REPLACE_RE_ALL, Op::STR_REPLACE_RE_ALL},
    {::cvc5::Kind::STRING_IS_DIGIT, Op::STR_IS_DIGIT},
    {::cvc5::Kind::STRING_TO_CODE, Op::STR_TO_CODE},
    {::cvc5::Kind::STRING_FROM_CODE, Op::STR_FROM_CODE},
    {::cvc5::Kind::STRING_TO_INT, Op::STR_TO_INT},
    {::cvc5::Kind::STRING_FROM_INT, Op::STR_FROM_INT},
    {::cvc5::Kind::REGEXP_ALL, Op::RE_ALL},
    {::cvc5::Kind::REGEXP_ALLCHAR, Op::RE_ALLCHAR},
    {::cvc5::Kind::REGEXP_COMPLEMENT, Op::RE_COMP},
    {::cvc5::Kind::REGEXP_CONCAT, Op::RE_CONCAT},
    {::cvc5::Kind::REGEXP_DIFF, Op::RE_DIFF},
    {::cvc5::Kind::REGEXP_INTER, Op::RE_INTER},
    {::cvc5::Kind::REGEXP_LOOP, Op::RE_LOOP},
    {::cvc5::Kind::REGEXP_NONE, Op::RE_NONE},
    {::cvc5::Kind::REGEXP_OPT, Op::RE_OPT},
    {::cvc5::Kind::REGEXP_PLUS, Op::RE_PLUS},
    {::cvc5::Kind::REGEXP_RANGE, Op::RE_RANGE},
    {::cvc5::Kind::REGEXP_REPEAT, Op::RE_POW},
    {::cvc5::Kind::REGEXP_STAR, Op::RE_STAR},
    {::cvc5::Kind::REGEXP_UNION, Op::RE_UNION},

    /* Transcendentals */
    {::cvc5::Kind::PI, Op::TRANS_PI},
    {::cvc5::Kind::SINE, Op::TRANS_SINE},
    {::cvc5::Kind::COSINE, Op::TRANS_COSINE},
    {::cvc5::Kind::TANGENT, Op::TRANS_TANGENT},
    {::cvc5::Kind::COTANGENT, Op::TRANS_COTANGENT},
    {::cvc5::Kind::SECANT, Op::TRANS_SECANT},
    {::cvc5::Kind::COSECANT, Op::TRANS_COSECANT},
    {::cvc5::Kind::ARCSINE, Op::TRANS_ARCSINE},
    {::cvc5::Kind::ARCCOSINE, Op::TRANS_ARCCOSINE},
    {::cvc5::Kind::ARCTANGENT, Op::TRANS_ARCTANGENT},
    {::cvc5::Kind::ARCCOSECANT, Op::TRANS_ARCCOSECANT},
    {::cvc5::Kind::ARCSECANT, Op::TRANS_ARCSECANT},
    {::cvc5::Kind::ARCCOTANGENT, Op::TRANS_ARCCOTANGENT},
    {::cvc5::Kind::SQRT, Op::TRANS_SQRT},

    /* UF */
    {::cvc5::Kind::APPLY_UF, Op::UF_APPLY},

    /* Non-standardized theories */
    // Bag
    {::cvc5::Kind::BAG_UNION_MAX, Op::BAG_UNION_MAX},
    {::cvc5::Kind::BAG_UNION_DISJOINT, Op::BAG_UNION_DISJOINT},
    {::cvc5::Kind::BAG_INTER_MIN, Op::BAG_INTERSECTION_MIN},
    {::cvc5::Kind::BAG_DIFFERENCE_SUBTRACT, Op::BAG_DIFFERENCE_SUBTRACT},
    {::cvc5::Kind::BAG_DIFFERENCE_REMOVE, Op::BAG_DIFFERENCE_REMOVE},
    {::cvc5::Kind::BAG_SUBBAG, Op::BAG_SUBBAG},
    {::cvc5::Kind::BAG_COUNT, Op::BAG_COUNT},
    {::cvc5::Kind::BAG_DUPLICATE_REMOVAL, Op::BAG_DUPLICATE_REMOVAL},
    {::cvc5::Kind::BAG_MAKE, Op::BAG_MAKE},
    {::cvc5::Kind::BAG_EMPTY, Op::BAG_EMPTY},
    {::cvc5::Kind::BAG_CARD, Op::BAG_CARD},
    {::cvc5::Kind::BAG_CHOOSE, Op::BAG_CHOOSE},
    {::cvc5::Kind::BAG_IS_SINGLETON, Op::BAG_IS_SINGLETON},
    {::cvc5::Kind::BAG_FROM_SET, Op::BAG_FROM_SET},
    {::cvc5::Kind::BAG_TO_SET, Op::BAG_TO_SET},
    {::cvc5::Kind::BAG_MAP, Op::BAG_MAP},
    // Sequences
    {::cvc5::Kind::SEQ_CONCAT, Op::SEQ_CONCAT},
    {::cvc5::Kind::SEQ_LENGTH, Op::SEQ_LENGTH},
    {::cvc5::Kind::SEQ_EXTRACT, Op::SEQ_EXTRACT},
    {::cvc5::Kind::SEQ_UPDATE, Op::SEQ_UPDATE},
    {::cvc5::Kind::SEQ_AT, Op::SEQ_AT},
    {::cvc5::Kind::SEQ_CONTAINS, Op::SEQ_CONTAINS},
    {::cvc5::Kind::SEQ_INDEXOF, Op::SEQ_INDEXOF},
    {::cvc5::Kind::SEQ_REPLACE, Op::SEQ_REPLACE},
    {::cvc5::Kind::SEQ_REPLACE_ALL, Op::SEQ_REPLACE_ALL},
    {::cvc5::Kind::SEQ_REV, Op::SEQ_REV},
    {::cvc5::Kind::SEQ_PREFIX, Op::SEQ_PREFIX},
    {::cvc5::Kind::SEQ_SUFFIX, Op::SEQ_SUFFIX},
    {::cvc5::Kind::SEQ_UNIT, Op::SEQ_UNIT},
    {::cvc5::Kind::SEQ_NTH, Op::SEQ_NTH},
    // Sets
    {::cvc5::Kind::SET_CARD, Op::SET_CARD},
    {::cvc5::Kind::SET_COMPLEMENT, Op::SET_COMPLEMENT},
    {::cvc5::Kind::SET_COMPREHENSION, Op::SET_COMPREHENSION},
    {::cvc5::Kind::SET_CHOOSE, Op::SET_CHOOSE},
    {::cvc5::Kind::SET_INTER, Op::SET_INTERSECTION},
    {::cvc5::Kind::SET_INSERT, Op::SET_INSERT},
    {::cvc5::Kind::SET_IS_SINGLETON, Op::SET_IS_SINGLETON},
    {::cvc5::Kind::SET_UNION, Op::SET_UNION},
    {::cvc5::Kind::SET_MEMBER, Op::SET_MEMBER},
    {::cvc5::Kind::SET_MINUS, Op::SET_MINUS},
    {::cvc5::Kind::SET_SINGLETON, Op::SET_SINGLETON},
    {::cvc5::Kind::SET_SUBSET, Op::SET_SUBSET},
    //{::cvc5::Kind::RELATION_JOIN, Op::REL_JOIN},
    //{::cvc5::Kind::RELATION_JOIN_IMAGE, Op::REL_JOIN_IMAGE},
    //{::cvc5::Kind::RELATION_IDEN, Op::REL_IDEN},
    //{::cvc5::Kind::RELATION_PRODUCT, Op::REL_PRODUCT},
    //{::cvc5::Kind::RELATION_TCLOSURE, Op::REL_TCLOSURE},
    //{::cvc5::Kind::RELATION_TRANSPOSE, Op::REL_TRANSPOSE},

    /* Solver-specific operators */
    {::cvc5::Kind::BITVECTOR_REDOR, OP_BV_REDOR},
    // BV
    {::cvc5::Kind::BITVECTOR_REDAND, OP_BV_REDAND},
    {::cvc5::Kind::BITVECTOR_ULTBV, OP_BV_ULTBV},
    {::cvc5::Kind::BITVECTOR_SLTBV, OP_BV_SLTBV},
    {::cvc5::Kind::BITVECTOR_ITE, OP_BV_ITE},
    // Datatypes
    {::cvc5::Kind::DT_SIZE, OP_DT_SIZE},
    // Int
    {::cvc5::Kind::BITVECTOR_TO_NAT, OP_BV_TO_NAT},
    {::cvc5::Kind::IAND, OP_INT_IAND},
    {::cvc5::Kind::INT_TO_BITVECTOR, OP_INT_TO_BV},
    {::cvc5::Kind::POW2, OP_INT_POW2},
    // Strings
    {::cvc5::Kind::STRING_UPDATE, OP_STRING_UPDATE},
    {::cvc5::Kind::STRING_TO_LOWER, OP_STRING_TOLOWER},
    {::cvc5::Kind::STRING_TO_UPPER, OP_STRING_TOUPPER},
    {::cvc5::Kind::STRING_REV, OP_STRING_REV},

    /* Special value kinds that cvc5 introduces its own node kind for,
     * only used for getKind(). */
    {::cvc5::Kind::REGEXP_STAR, OP_REGEXP_STAR},
    {::cvc5::Kind::SET_EMPTY, OP_SET_EMPTY},
    {::cvc5::Kind::SET_UNIVERSE, OP_SET_UNIVERSE},
};

::cvc5::Term&
Cvc5Term::get_cvc5_term(Term term)
{
  return checked_cast<Cvc5Term*>(term.get())->d_term;
}

std::vector<Term>
Cvc5Term::cvc5_terms_to_terms(Tracer<Cvc5TracerData>& tracer,
                              RNGenerator& rng,
                              ::cvc5::Solver* cvc5,
                              const std::vector<::cvc5::Term>& terms)
{
  std::vector<Term> res;
  for (auto& t : terms)
  {
    res.push_back(
        std::shared_ptr<Cvc5Term>(new Cvc5Term(tracer, rng, cvc5, t)));
  }
  return res;
}

std::vector<::cvc5::Term>
Cvc5Term::terms_to_cvc5_terms(const std::vector<Term>& terms)
{
  std::vector<::cvc5::Term> res;
  for (auto& t : terms)
  {
    res.push_back(get_cvc5_term(t));
  }
  return res;
}

size_t
Cvc5Term::hash() const
{
  return std::hash<::cvc5::Term>{}(d_term);
}

bool
Cvc5Term::equals(const Term& other) const
{
  Cvc5Term* cvc5_term = checked_cast<Cvc5Term*>(other.get());
  if (cvc5_term) return d_term == cvc5_term->d_term;
  return false;
}

std::string
Cvc5Term::to_string() const
{
  return d_term.toString();
}

bool
Cvc5Term::is_bool_value() const
{
  return d_term.isBooleanValue();
}

bool
Cvc5Term::is_bv_value() const
{
  return d_term.isBitVectorValue();
}

bool
Cvc5Term::is_fp_value() const
{
  return d_term.isFloatingPointValue();
}

bool
Cvc5Term::is_int_value() const
{
  return d_term.isIntegerValue();
}

bool
Cvc5Term::is_real_value() const
{
  return d_term.isRealValue();
}

bool
Cvc5Term::is_seq_value() const
{
  return d_term.isSequenceValue();
}

bool
Cvc5Term::is_set_value() const
{
  return d_term.isSetValue();
}

bool
Cvc5Term::is_string_value() const
{
  return d_term.isStringValue();
}

const Op::Kind&
Cvc5Term::get_kind() const
{
  return s_cvc5_kinds_to_kinds.at(d_term.getKind());
}

std::vector<Term>
Cvc5Term::get_children() const
{
  std::vector<Term> res;
  for (const auto& c : d_term)
  {
    res.emplace_back(new Cvc5Term(d_tracer, d_rng, d_solver, c));
  }
  return res;
}

bool
Cvc5Term::is_indexed() const
{
  if (d_term.hasOp())
  {
    return d_term.getOp().isIndexed();
  }
  return false;
}

size_t
Cvc5Term::get_num_indices() const
{
  if (d_term.hasOp())
  {
    return d_term.getOp().getNumIndices();
  }
  return 0;
}

std::vector<std::string>
Cvc5Term::get_indices() const
{
  assert(is_indexed());
  std::vector<std::string> res;
  Op::Kind kind = get_kind();
  auto op       = d_term.getOp();
  size_t n_idxs = get_num_indices();
  for (size_t i = 0; i < n_idxs; ++i)
  {
    MURXLA_TEST(op[i].isIntegerValue());
    res.push_back(op[i].getIntegerValue());
  }
  return res;
}

uint32_t
Cvc5Term::get_bv_size() const
{
  assert(is_bv());
  return d_term.getSort().getBitVectorSize();
}

uint32_t
Cvc5Term::get_fp_exp_size() const
{
  assert(is_fp());
  return d_term.getSort().getFloatingPointExponentSize();
}

uint32_t
Cvc5Term::get_fp_sig_size() const
{
  assert(is_fp());
  return d_term.getSort().getFloatingPointSignificandSize();
}

Sort
Cvc5Term::get_array_index_sort() const
{
  assert(is_array());
  return std::shared_ptr<Cvc5Sort>(
      new Cvc5Sort(d_tracer, d_solver, d_term.getSort().getArrayIndexSort()));
}

Sort
Cvc5Term::get_array_element_sort() const
{
  assert(is_array());
  return std::shared_ptr<Cvc5Sort>(
      new Cvc5Sort(d_tracer, d_solver, d_term.getSort().getArrayElementSort()));
}

uint32_t
Cvc5Term::get_fun_arity() const
{
  assert(is_fun());
  return static_cast<uint32_t>(d_term.getSort().getFunctionArity());
}

Sort
Cvc5Term::get_fun_codomain_sort() const
{
  assert(is_fun());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(
      d_tracer, d_solver, d_term.getSort().getFunctionCodomainSort()));
}

std::vector<Sort>
Cvc5Term::get_fun_domain_sorts() const
{
  assert(is_fun());
  std::vector<::cvc5::Sort> cvc5_res =
      d_term.getSort().getFunctionDomainSorts();
  return Cvc5Sort::cvc5_sorts_to_sorts(d_tracer, d_solver, cvc5_res);
}

/* -------------------------------------------------------------------------- */
/* Cvc5Solver                                                                 */
/* -------------------------------------------------------------------------- */

Cvc5Solver::~Cvc5Solver()
{
  if (d_solver)
  {
    delete d_solver;
    d_solver = nullptr;
  }
}

void
Cvc5Solver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = new ::cvc5::Solver();
  d_tracer.init();
}

void
Cvc5Solver::delete_solver()
{
  assert(d_solver != nullptr);
  delete d_solver;
  d_solver = nullptr;
}

::cvc5::Solver*
Cvc5Solver::get_solver()
{
  return d_solver;
}

bool
Cvc5Solver::is_initialized() const
{
  return d_solver != nullptr;
}

const std::string
Cvc5Solver::get_name() const
{
  return "cvc5";
}

const std::string
Cvc5Solver::get_profile() const
{
  return s_profile;
}

bool
Cvc5Solver::is_unsat_assumption(const Term& t) const
{
  return !Cvc5Term::get_cvc5_term(t).isNull();
}

/* -------------------------------------------------------------------------- */

Sort
Cvc5Solver::mk_sort(const std::string& name)
{
  ::cvc5::Sort cvc5_res = TRACE_SOLVER(mkUninterpretedSort, name);
  return std::make_shared<Cvc5Sort>(d_tracer, d_solver, cvc5_res);
}

Sort
Cvc5Solver::mk_sort(SortKind kind)
{
  ::cvc5::Sort cvc5_res;
  switch (kind)
  {
    case SORT_BOOL: cvc5_res = TRACE_SOLVER(getBooleanSort); break;
    case SORT_INT: cvc5_res = TRACE_SOLVER(getIntegerSort); break;
    case SORT_REAL: cvc5_res = TRACE_SOLVER(getRealSort); break;
    case SORT_RM: cvc5_res = TRACE_SOLVER(getRoundingModeSort); break;
    case SORT_REGLAN: cvc5_res = TRACE_SOLVER(getRegExpSort); break;
    case SORT_STRING: cvc5_res = TRACE_SOLVER(getStringSort); break;

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unsupported sort kind '" << kind
          << "' as argument to Cvc5Solver::mk_sort, expected '" << SORT_BOOL
          << "', '" << SORT_INT << "', '" << SORT_REAL << "', '" << SORT_RM
          << "', '" << SORT_REGLAN << "' or '" << SORT_STRING << "'";
  }
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
}

Sort
Cvc5Solver::mk_sort(SortKind kind, uint32_t size)
{
  MURXLA_CHECK_CONFIG(kind == SORT_BV)
      << "unsupported sort kind '" << kind
      << "' as argument to Cvc5Solver::mk_sort, expected '" << SORT_BV << "'";
  ::cvc5::Sort cvc5_res = TRACE_SOLVER(mkBitVectorSort, size);
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
}

Sort
Cvc5Solver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  MURXLA_CHECK_CONFIG(kind == SORT_FP)
      << "unsupported sort kind '" << kind
      << "' as argument to Cvc5Solver::mk_sort, expected '" << SORT_FP << "'";
  ::cvc5::Sort cvc5_res = TRACE_SOLVER(mkFloatingPointSort, esize, ssize);
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
}

Sort
Cvc5Solver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  ::cvc5::Sort cvc5_res;

  switch (kind)
  {
    case SORT_ARRAY:
      assert(sorts.size() == 2);
      cvc5_res = TRACE_SOLVER(mkArraySort,
                              Cvc5Sort::get_cvc5_sort(sorts[0]),
                              Cvc5Sort::get_cvc5_sort(sorts[1]));
      break;

    case SORT_BAG:
      assert(sorts.size() == 1);
      cvc5_res = TRACE_SOLVER(mkBagSort, Cvc5Sort::get_cvc5_sort(sorts[0]));
      break;

    case SORT_FUN:
    {
      std::vector<::cvc5::Sort> domain;
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        domain.push_back(Cvc5Sort::get_cvc5_sort(*it));
      }
      ::cvc5::Sort codomain = Cvc5Sort::get_cvc5_sort(sorts.back());

      if (codomain.isBoolean() && d_rng.flip_coin())
      {
        cvc5_res = TRACE_SOLVER(mkPredicateSort, domain);
      }
      else
      {
        if (domain.size() == 1 && d_rng.flip_coin())
        {
          // cvc5_res = TRACE_SOLVER(mkFunctionSort, domain[0], codomain);
          cvc5_res = TRACE_SOLVER(mkFunctionSort, domain[0], codomain);
        }
        else
        {
          cvc5_res = TRACE_SOLVER(mkFunctionSort, domain, codomain);
        }
      }
      break;
    }

    case SORT_SEQ:
      assert(sorts.size() == 1);
      cvc5_res =
          TRACE_SOLVER(mkSequenceSort, Cvc5Sort::get_cvc5_sort(sorts[0]));
      break;

    case SORT_SET:
      assert(sorts.size() == 1);
      cvc5_res = TRACE_SOLVER(mkSetSort, Cvc5Sort::get_cvc5_sort(sorts[0]));
      break;

    default:
      MURXLA_CHECK_CONFIG(false) << "unsupported sort kind '" << kind
                                 << "' as argument to Cvc5Solver::mk_sort, "
                                    "expected '"
                                 << SORT_ARRAY << "' or '" << SORT_FUN << "'";
  }
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
}

std::vector<Sort>
Cvc5Solver::mk_sort(
    SortKind kind,
    const std::vector<std::string>& dt_names,
    const std::vector<std::vector<Sort>>& param_sorts,
    const std::vector<AbsSort::DatatypeConstructorMap>& constructors)
{
  size_t n_dt_sorts = dt_names.size();
  assert(n_dt_sorts == param_sorts.size());
  assert(n_dt_sorts == constructors.size());

  std::vector<::cvc5::DatatypeDecl> cvc5_dtypedecls;
  std::vector<std::vector<::cvc5::DatatypeConstructorDecl>> cvc5_dtypectordecls;
  std::set<::cvc5::Sort> cvc5_usorts;

  for (size_t i = 0; i < n_dt_sorts; ++i)
  {
    const std::string& name = dt_names[i];
    const auto& psorts      = param_sorts[i];
    const auto& ctors       = constructors[i];

    bool is_parametric = !psorts.empty();
    std::unordered_map<std::string, ::cvc5::Sort> symbol_to_cvc5_psorts;
    std::unordered_map<std::string, ::cvc5::Sort> symbol_to_cvc5_usorts;
    std::vector<::cvc5::Sort> cvc5_psorts;
    for (const auto& s : psorts)
    {
      const std::string& symbol =
          checked_cast<ParamSort*>(s.get())->get_symbol();
      ::cvc5::Sort cvc5_param_sort = TRACE_SOLVER(mkParamSort, symbol);
      cvc5_psorts.push_back(cvc5_param_sort);
      assert(symbol_to_cvc5_psorts.find(symbol) == symbol_to_cvc5_psorts.end());
      symbol_to_cvc5_psorts[symbol] = cvc5_param_sort;
    }

    ::cvc5::DatatypeDecl cvc5_dtypedecl =
        is_parametric
            ? (psorts.size() == 1 && d_rng.flip_coin()
                   ? TRACE_SOLVER(mkDatatypeDecl, name, cvc5_psorts[0])
                   : TRACE_SOLVER(mkDatatypeDecl, name, cvc5_psorts))
            : TRACE_SOLVER(mkDatatypeDecl, name);
    if (d_rng.pick_with_prob(10))
    {
      MURXLA_TEST(is_parametric == cvc5_dtypedecl.isParametric());
      MURXLA_TEST(name == cvc5_dtypedecl.getName());
    }

    std::vector<::cvc5::DatatypeConstructorDecl> cvc5_ctors;
    for (const auto& c : ctors)
    {
      const auto& cname = c.first;
      const auto& sels  = c.second;

      ::cvc5::DatatypeConstructorDecl cvc5_cdecl =
          TRACE_SOLVER(mkDatatypeConstructorDecl, cname);
      cvc5_ctors.push_back(cvc5_cdecl);

      for (const auto& s : sels)
      {
        const auto& sname = s.first;
        const auto& ssort = s.second;
        if (ssort == nullptr)
        {
          TRACE_METHOD(addSelectorSelf, cvc5_cdecl, sname);
        }
        else
        {
          if (ssort->is_param_sort())
          {
            const std::string& symbol =
                checked_cast<ParamSort*>(ssort.get())->get_symbol();
            assert(symbol_to_cvc5_psorts.find(symbol)
                   != symbol_to_cvc5_psorts.end());
            TRACE_METHOD(addSelector,
                         cvc5_cdecl,
                         sname,
                         symbol_to_cvc5_psorts.at(symbol));
          }
          else if (ssort->is_unresolved_sort())
          {
            const std::string& symbol =
                checked_cast<UnresolvedSort*>(ssort.get())->get_symbol();
            const auto& it         = symbol_to_cvc5_usorts.find(symbol);
            const auto& inst_sorts = ssort->get_sorts();
            size_t arity           = inst_sorts.size();
            ::cvc5::Sort cvc5_unres_sort;
            if (it == symbol_to_cvc5_usorts.end())
            {
              if (d_rng.flip_coin())
              {
                cvc5_unres_sort = TRACE_SOLVER(mkUnresolvedSort, symbol, arity);
              }
              else
              {
                if (arity > 0)
                {
                  cvc5_unres_sort = TRACE_SOLVER(
                      mkUninterpretedSortConstructorSort, symbol, arity);
                }
                else
                {
                  cvc5_unres_sort = TRACE_SOLVER(mkUninterpretedSort, symbol);
                }
              }
              symbol_to_cvc5_usorts[symbol] = cvc5_unres_sort;
              cvc5_usorts.insert(cvc5_unres_sort);
            }
            else
            {
              cvc5_unres_sort = symbol_to_cvc5_usorts.at(symbol);
            }

            if (arity)
            {
              std::vector<::cvc5::Sort> cvc5_inst_sorts;
              for (const Sort& s : inst_sorts)
              {
                if (s->is_param_sort())
                {
                  assert(!s->is_unresolved_sort());
                  const std::string& s_symbol =
                      checked_cast<ParamSort*>(s.get())->get_symbol();
                  assert(symbol_to_cvc5_psorts.find(s_symbol)
                         != symbol_to_cvc5_psorts.end());
                  cvc5_inst_sorts.push_back(symbol_to_cvc5_psorts.at(s_symbol));
                }
                else
                {
                  cvc5_inst_sorts.push_back(Cvc5Sort::get_cvc5_sort(s));
                }
              }
              TRACE_METHOD(
                  addSelector,
                  cvc5_cdecl,
                  sname,
                  TRACE_METHOD(instantiate, cvc5_unres_sort, cvc5_inst_sorts));
            }
            else
            {
              TRACE_METHOD(addSelector, cvc5_cdecl, sname, cvc5_unres_sort);
            }
          }
          else
          {
            TRACE_METHOD(
                addSelector, cvc5_cdecl, sname, Cvc5Sort::get_cvc5_sort(ssort));
          }
        }
      }

      TRACE_METHOD(addConstructor, cvc5_dtypedecl, cvc5_cdecl);
    }
    cvc5_dtypectordecls.push_back(cvc5_ctors);
    cvc5_dtypedecls.push_back(cvc5_dtypedecl);
  }

  if (n_dt_sorts == 1 && d_rng.flip_coin())
  {
    assert(cvc5_usorts.empty());
    assert(cvc5_dtypedecls.size() == 1);
    assert(cvc5_dtypectordecls.size() == 1);
    ::cvc5::Sort cvc5_res;
    if (!param_sorts[0].empty() || d_rng.flip_coin())
    {
      cvc5_res = TRACE_SOLVER(mkDatatypeSort, cvc5_dtypedecls[0]);
    }
    else
    {
      cvc5_res =
          TRACE_SOLVER(declareDatatype, dt_names[0], cvc5_dtypectordecls[0]);
    }
    MURXLA_TEST(!cvc5_res.isNull());
    MURXLA_TEST(!cvc5_res.getDatatype().isNull());
    return {
        std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_tracer, d_solver, cvc5_res))};
  }

  std::vector<::cvc5::Sort> cvc5_res;
  if (cvc5_usorts.empty() && d_rng.flip_coin())
  {
    cvc5_res = TRACE_SOLVER(mkDatatypeSorts, cvc5_dtypedecls);
  }
  else
  {
    cvc5_res = TRACE_SOLVER(mkDatatypeSorts, cvc5_dtypedecls, cvc5_usorts);
  }
  size_t idx = d_rng.pick<size_t>(0, cvc5_res.size() - 1);
  MURXLA_TEST(!cvc5_res[idx].isNull());
  MURXLA_TEST(!cvc5_res[idx].getDatatype().isNull());
  std::vector<Sort> res(cvc5_res.size());
  std::transform(
      cvc5_res.begin(), cvc5_res.end(), res.begin(), [this](const auto& sort) {
        return std::shared_ptr<Cvc5Sort>(
            new Cvc5Sort(d_tracer, d_solver, sort));
      });
  return res;
}

Sort
Cvc5Solver::instantiate_sort(Sort param_sort, const std::vector<Sort>& sorts)
{
  ::cvc5::Sort cvc5_param_sort = Cvc5Sort::get_cvc5_sort(param_sort);
  std::vector<::cvc5::Sort> cvc5_sorts;

  for (const Sort& s : sorts)
  {
    if (s->is_param_sort())
    {
      assert(!s->is_unresolved_sort());
      assert(s->get_associated_sort());
      const std::string& s_symbol =
          checked_cast<ParamSort*>(s.get())->get_symbol();
      ::cvc5::Sort cvc5_dt_sort =
          Cvc5Sort::get_cvc5_sort(s->get_associated_sort());
      const auto& cvc5_sort_params = cvc5_dt_sort.getDatatype().getParameters();
      const auto& it               = std::find_if(
          cvc5_sort_params.begin(),
          cvc5_sort_params.end(),
          [&s_symbol](auto& sort) { return sort.getSymbol() == s_symbol; });
      assert(it != cvc5_sort_params.end());
      cvc5_sorts.push_back(*it);
    }
    else
    {
      cvc5_sorts.push_back(Cvc5Sort::get_cvc5_sort(s));
    }
  }

  ::cvc5::Sort cvc5_res =
      TRACE_METHOD(instantiate, cvc5_param_sort, cvc5_sorts);

  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_tracer, d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_const(Sort sort, const std::string& name)
{
  ::cvc5::Term cvc5_res =
      TRACE_SOLVER(mkConst, Cvc5Sort::get_cvc5_sort(sort), name);
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Term>(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_fun(const std::string& name,
                   const std::vector<Term>& args,
                   Term body)
{
  std::vector<::cvc5::Term> cvc5_args = Cvc5Term::terms_to_cvc5_terms(args);
  ::cvc5::Term cvc5_body              = Cvc5Term::get_cvc5_term(body);

  auto cvc5_res =
      TRACE_SOLVER(defineFun, name, cvc5_args, cvc5_body.getSort(), cvc5_body);
  return std::shared_ptr<Cvc5Term>(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_var(Sort sort, const std::string& name)
{
  ::cvc5::Term cvc5_res =
      TRACE_SOLVER(mkVar, Cvc5Sort::get_cvc5_sort(sort), name);
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Term>(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_value(Sort sort, bool value)
{
  MURXLA_CHECK_CONFIG(sort->is_bool())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to "
         "Cvc5Solver::mk_value, expected Boolean sort ";

  ::cvc5::Term cvc5_res;

  if (d_rng.flip_coin())
  {
    cvc5_res = value ? TRACE_SOLVER(mkTrue) : TRACE_SOLVER(mkFalse);
  }
  else
  {
    cvc5_res = TRACE_SOLVER(mkBoolean, value);
  }
  MURXLA_TEST(!cvc5_res.isNull());
  std::shared_ptr<Cvc5Term> res(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_value(Sort sort, const std::string& value)
{
  ::cvc5::Term cvc5_res;
  ::cvc5::Sort cvc5_sort      = Cvc5Sort::get_cvc5_sort(sort);
  SortKind sort_kind          = sort->get_kind();

  switch (sort_kind)
  {
    case SORT_FP:
    {
      uint32_t ew = sort->get_fp_exp_size();
      uint32_t sw = sort->get_fp_sig_size();
      cvc5_res    = TRACE_SOLVER(mkFloatingPoint,
                              ew,
                              sw,
                              TRACE_SOLVER(mkBitVector, ew + sw, value, 2));
    }
    break;

    case SORT_INT:
    {
      assert(sort->is_int());
      int64_t val64 = 0;
      bool fits64   = true;
      try
      {
        val64 = std::stoll(value);
      }
      catch (std::out_of_range& e)
      {
        fits64 = false;
      }
      if (fits64 && d_rng.flip_coin())
      {
        cvc5_res = TRACE_SOLVER(mkInteger, val64);
      }
      else
      {
        cvc5_res = TRACE_SOLVER(mkInteger, value);
      }
    }
    break;

    case SORT_REAL:
      assert(sort->is_real());
      if (value.find('.') != std::string::npos)
      {
        int64_t val64 = 0;
        bool fits64   = true;
        try
        {
          val64 = std::stoll(value);
        }
        catch (std::out_of_range& e)
        {
          fits64 = false;
        }
        if (fits64 && d_rng.flip_coin())
        {
          cvc5_res = TRACE_SOLVER(mkReal, val64);
        }
        else
        {
          cvc5_res = TRACE_SOLVER(mkReal, value);
        }
      }
      else
      {
        cvc5_res = TRACE_SOLVER(mkReal, value);
      }
      break;

    case SORT_REGLAN:
    case SORT_STRING:
      // TODO: test more mkString functions
      cvc5_res = TRACE_SOLVER(mkString, value);
      break;

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unexpected sort of kind '" << sort->get_kind()
          << "' as argument to "
             "Cvc5Solver::mk_value, expected Integer, Real, Reglan or String "
             "sort ";
  }
  MURXLA_TEST(!cvc5_res.isNull());
  std::shared_ptr<Cvc5Term> res(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_value(Sort sort, const std::string& num, const std::string& den)
{
  assert(sort->is_real());
  MURXLA_CHECK_CONFIG(sort->is_real())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to "
         "Cvc5Solver::mk_value, expected Real sort";
  ::cvc5::Term cvc5_res;

  cvc5_res =
      TRACE_SOLVER(mkReal,
                   static_cast<int64_t>(strtoull(num.c_str(), nullptr, 10)),
                   static_cast<int64_t>(strtoull(den.c_str(), nullptr, 10)));
  MURXLA_TEST(!cvc5_res.isNull());
  std::shared_ptr<Cvc5Term> res(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_value(Sort sort, const std::string& value, Base base)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to "
         "Cvc5Solver::mk_value, expected bit-vector sort";

  ::cvc5::Term cvc5_res;
  ::cvc5::Sort cvc5_sort      = Cvc5Sort::get_cvc5_sort(sort);
  uint32_t bw                 = sort->get_bv_size();

  switch (base)
  {
    case DEC:
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc5_res =
            TRACE_SOLVER(mkBitVector, bw, strtoull(value.c_str(), nullptr, 10));
      }
      else
      {
        cvc5_res = d_rng.flip_coin()
                       ? TRACE_SOLVER(mkBitVector, bw, value, 10)
                       : TRACE_SOLVER(mkBitVector, bw, value.c_str(), 10);
      }
      break;

    case HEX:
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc5_res =
            TRACE_SOLVER(mkBitVector, bw, strtoull(value.c_str(), nullptr, 16));
      }
      else
      {
        cvc5_res = d_rng.flip_coin()
                       ? TRACE_SOLVER(mkBitVector, bw, value, 16)
                       : TRACE_SOLVER(mkBitVector, bw, value.c_str(), 16);
      }
      break;

    default:
      assert(base == BIN);
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc5_res =
            TRACE_SOLVER(mkBitVector, bw, strtoull(value.c_str(), nullptr, 2));
      }
      else
      {
        cvc5_res = d_rng.flip_coin()
                       ? TRACE_SOLVER(mkBitVector, bw, value, 2)
                       : TRACE_SOLVER(mkBitVector, bw, value.c_str(), 2);
      }
  }
  MURXLA_TEST(!cvc5_res.isNull());
  std::shared_ptr<Cvc5Term> res(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_special_value(Sort sort, const AbsTerm::SpecialValueKind& value)
{
  ::cvc5::Term cvc5_res;

  switch (sort->get_kind())
  {
    case SORT_BAG:
    {
      assert(value == AbsTerm::SPECIAL_VALUE_BAG_EMPTY);
      const std::vector<Sort>& sorts = sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      cvc5_res = TRACE_SOLVER(mkEmptyBag, Cvc5Sort::get_cvc5_sort(sort));
    }
    break;

    case SORT_BV:
    {
      uint32_t bw = sort->get_bv_size();
      if (value == AbsTerm::SPECIAL_VALUE_BV_ZERO)
      {
        cvc5_res =
            d_rng.flip_coin()
                ? TRACE_SOLVER(
                    mkBitVector, bw, bv_special_value_zero_str(bw), 2)
                : TRACE_SOLVER(
                    mkBitVector, bw, bv_special_value_zero_str(bw).c_str(), 2);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_ONE)
      {
        cvc5_res =
            d_rng.flip_coin()
                ? TRACE_SOLVER(mkBitVector, bw, bv_special_value_one_str(bw), 2)
                : TRACE_SOLVER(
                    mkBitVector, bw, bv_special_value_one_str(bw).c_str(), 2);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_ONES)
      {
        cvc5_res =
            d_rng.flip_coin()
                ? TRACE_SOLVER(
                    mkBitVector, bw, bv_special_value_ones_str(bw), 2)
                : TRACE_SOLVER(
                    mkBitVector, bw, bv_special_value_ones_str(bw).c_str(), 2);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED)
      {
        cvc5_res =
            d_rng.flip_coin()
                ? TRACE_SOLVER(
                    mkBitVector, bw, bv_special_value_min_signed_str(bw), 2)
                : TRACE_SOLVER(mkBitVector,
                               bw,
                               bv_special_value_min_signed_str(bw).c_str(),
                               2);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED);
        cvc5_res =
            d_rng.flip_coin()
                ? TRACE_SOLVER(
                    mkBitVector, bw, bv_special_value_max_signed_str(bw), 2)
                : TRACE_SOLVER(mkBitVector,
                               bw,
                               bv_special_value_max_signed_str(bw).c_str(),
                               2);
      }
    }
    break;

    case SORT_FP:
    {
      uint32_t ew = sort->get_fp_exp_size();
      uint32_t sw = sort->get_fp_sig_size();
      if (value == AbsTerm::SPECIAL_VALUE_FP_POS_INF)
      {
        cvc5_res = TRACE_SOLVER(mkFloatingPointPosInf, ew, sw);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_NEG_INF)
      {
        cvc5_res = TRACE_SOLVER(mkFloatingPointNegInf, ew, sw);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_POS_ZERO)
      {
        cvc5_res = TRACE_SOLVER(mkFloatingPointPosZero, ew, sw);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_NEG_ZERO)
      {
        cvc5_res = TRACE_SOLVER(mkFloatingPointNegZero, ew, sw);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_FP_NAN);
        cvc5_res = TRACE_SOLVER(mkFloatingPointNaN, ew, sw);
      }
    }
    break;

    case SORT_RM:
      if (value == AbsTerm::SPECIAL_VALUE_RM_RNE)
      {
        cvc5_res = TRACE_SOLVER(
            mkRoundingMode, ::cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RNA)
      {
        cvc5_res = TRACE_SOLVER(
            mkRoundingMode, ::cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RTN)
      {
        cvc5_res = TRACE_SOLVER(mkRoundingMode,
                                ::cvc5::RoundingMode::ROUND_TOWARD_NEGATIVE);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RTP)
      {
        cvc5_res = TRACE_SOLVER(mkRoundingMode,
                                ::cvc5::RoundingMode::ROUND_TOWARD_POSITIVE);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_RM_RTZ);
        cvc5_res = TRACE_SOLVER(mkRoundingMode,
                                ::cvc5::RoundingMode::ROUND_TOWARD_ZERO);
      }
      break;

    case SORT_SEQ:
    {
      assert(value == AbsTerm::SPECIAL_VALUE_SEQ_EMPTY);
      const std::vector<Sort>& sorts = sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      cvc5_res =
          TRACE_SOLVER(mkEmptySequence, Cvc5Sort::get_cvc5_sort(element_sort));
    }
    break;

    case SORT_SET:
    {
      const std::vector<Sort>& sorts = sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      if (value == AbsTerm::SPECIAL_VALUE_SET_EMPTY)
      {
        cvc5_res = TRACE_SOLVER(mkEmptySet, Cvc5Sort::get_cvc5_sort(sort));
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_SET_UNIVERSE);
        cvc5_res = TRACE_SOLVER(mkUniverseSet, Cvc5Sort::get_cvc5_sort(sort));
      }
    }
    break;

    default:
      MURXLA_CHECK_CONFIG(sort->is_bv())
          << "unexpected sort of kind '" << sort->get_kind()
          << "' as argument to "
             "Cvc5Solver::mk_special_value, expected bit-vector, "
             "floating-point, "
             "RoundingMode, Real, Reglan or Sequence sort";
  }
  std::shared_ptr<Cvc5Term> res(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_term(const Op::Kind& kind,
                    const std::vector<Term>& args,
                    const std::vector<uint32_t>& indices)
{
  MURXLA_CHECK_CONFIG(Cvc5Term::s_kinds_to_cvc5_kinds.find(kind)
                      != Cvc5Term::s_kinds_to_cvc5_kinds.end())
      << "Cvc5Solver: operator kind '" << kind << "' not configured";

  ::cvc5::Term cvc5_res;
  ::cvc5::Op cvc5_opterm;
  ::cvc5::Kind cvc5_kind = Cvc5Term::s_kinds_to_cvc5_kinds.at(kind);
  std::vector<::cvc5::Term> cvc5_args = Cvc5Term::terms_to_cvc5_terms(args);

  std::vector<uint32_t> iindices = indices;  // copy to modify
  int32_t n_args                 = static_cast<int32_t>(args.size());
  size_t n_indices               = indices.size();

  if (kind == Op::FORALL || kind == Op::EXISTS)
  {
    assert(args.size() >= 2);
    std::vector<::cvc5::Term> cvc5_vars;
    for (size_t i = 0; i < args.size() - 1; ++i)
    {
      cvc5_vars.push_back(cvc5_args[i]);
    }
    ::cvc5::Term cvc5_bvl =
        d_rng.flip_coin()
            ? TRACE_SOLVER(mkTerm, ::cvc5::Kind::VARIABLE_LIST, cvc5_vars)
            : TRACE_SOLVER(mkTerm,
                           TRACE_SOLVER(mkOp, ::cvc5::Kind::VARIABLE_LIST),
                           cvc5_vars);
    ::cvc5::Term cvc5_body      = Cvc5Term::get_cvc5_term(args.back());
    cvc5_args                   = {cvc5_bvl, cvc5_body};
    n_args                      = static_cast<int32_t>(cvc5_args.size());
  }
  else if (kind == Op::RE_ALL)
  {
    cvc5_res = TRACE_SOLVER(mkRegexpAll);
    goto DONE;
  }
  else if (kind == Op::RE_ALLCHAR && d_rng.flip_coin())
  {
    cvc5_res = TRACE_SOLVER(mkRegexpAllchar);
    goto DONE;
  }
  else if (kind == Op::TRANS_PI && d_rng.flip_coin())
  {
    cvc5_res = TRACE_SOLVER(mkPi);
    goto DONE;
  }
  else if (kind == Op::RE_NONE && d_rng.flip_coin())
  {
    cvc5_res = TRACE_SOLVER(mkRegexpNone);
    goto DONE;
  }

  /* Create Op. Flip a coin for non-indexed operators. */
  switch (n_indices)
  {
    case 1:
    {
      if (kind == Cvc5Term::OP_INT_IAND || kind == Cvc5Term::OP_INT_TO_BV)
      {
        iindices[0] = uint32_to_value_in_range(iindices[0], 1, MURXLA_BW_MAX);
      }
      if (kind == Op::INT_IS_DIV && d_rng.flip_coin())
      {
        cvc5_opterm =
            TRACE_SOLVER(mkOp, cvc5_kind, std::to_string(iindices[0]));
      }
      else
      {
        cvc5_opterm = TRACE_SOLVER(mkOp, cvc5_kind, std::vector{iindices[0]});
      }
      MURXLA_TEST(!cvc5_opterm.isNull());
      MURXLA_TEST(!d_rng.pick_with_prob(1) || cvc5_opterm == cvc5_opterm);
      MURXLA_TEST(!d_rng.pick_with_prob(1) || !(cvc5_opterm != cvc5_opterm));
      MURXLA_TEST(cvc5_opterm.isIndexed());
      MURXLA_TEST(cvc5_opterm.getKind() == cvc5_kind);
      uint32_t idx = cvc5_opterm[0].getUInt32Value();
      MURXLA_TEST(idx == iindices[0]);
      break;
    }
    case 2:
    {
      cvc5_opterm =
          TRACE_SOLVER(mkOp, cvc5_kind, std::vector{iindices[0], iindices[1]});
      MURXLA_TEST(!cvc5_opterm.isNull());
      MURXLA_TEST(!d_rng.pick_with_prob(1) || cvc5_opterm == cvc5_opterm);
      MURXLA_TEST(!d_rng.pick_with_prob(1) || !(cvc5_opterm != cvc5_opterm));
      MURXLA_TEST(cvc5_opterm.isIndexed());
      MURXLA_TEST(cvc5_opterm.getKind() == cvc5_kind);
      MURXLA_TEST(cvc5_opterm[0].getUInt32Value() == iindices[0]);
      MURXLA_TEST(cvc5_opterm[1].getUInt32Value() == iindices[1]);
      break;
    }
    default:
      assert(n_indices == 0);
      if (d_rng.flip_coin())
      {
        cvc5_opterm = TRACE_SOLVER(mkOp, cvc5_kind);
      }
  }

  if (kind == Cvc5Term::OP_BV_ITE)
  {
    uint32_t size = cvc5_args[0].getSort().getBitVectorSize();
    /* if the first argument is of size greater than 1, slice random
     * bit out of it */
    if (size > 1)
    {
      uint32_t hi = d_rng.pick<uint32_t>(0, size - 1);
      uint32_t lo = hi;
      ::cvc5::Op op = TRACE_SOLVER(
          mkOp, ::cvc5::Kind::BITVECTOR_EXTRACT, std::vector{hi, lo});
      cvc5_args[0] = TRACE_SOLVER(mkTerm, op, std::vector{cvc5_args[0]});
    }
  }
  else if (kind == Op::SET_INSERT || kind == Op::SET_MEMBER)
  {
    /* cvc5 uses order <elem>+ <set> for the arguments
     * (is given as <set> <elem>+) */
    ::cvc5::Term set      = cvc5_args[0];
    size_t n              = cvc5_args.size() - 1;
    cvc5_args[0]          = cvc5_args[n];
    cvc5_args[n]          = set;
  }
  else if (kind == Op::SET_COMPREHENSION)
  {
    /* cvc5 uses order <var_list> <predicate> <term> for the arguments
     * (is given as <predicate> <term> <var>+) */
    assert(args.size() >= 3);
    std::vector<::cvc5::Term> vars;
    for (size_t i = 2; i < args.size(); ++i)
    {
      vars.push_back(cvc5_args[i]);
    }
    cvc5_args = {TRACE_SOLVER(mkTerm, ::cvc5::Kind::VARIABLE_LIST, vars),
                 cvc5_args[0],
                 cvc5_args[1]};
  }
  else if (kind == Op::BAG_COUNT || kind == Op::BAG_MAP)
  {
    /* cvc5 uses order <not bag> <bag> for the arguments (is given as <bag>
     * <not bag> ) */
    assert(args.size() == 2);
    std::swap(cvc5_args[0], cvc5_args[1]);
  }

  /* use vector with 50% probability */
  if (d_rng.flip_coin()) n_args = MURXLA_MK_TERM_N_ARGS_BIN;

  /* create term */
  switch (n_args)
  {
    case 0:
      assert(!n_indices);
      cvc5_res = cvc5_opterm.isNull() ? TRACE_SOLVER(mkTerm, cvc5_kind)
                                      : TRACE_SOLVER(mkTerm, cvc5_opterm);
      break;

    case 1:
      if (kind == Op::NOT && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = TRACE_METHOD(notTerm, cvc5_args[0]);
      }
      else
      {
        cvc5_res = cvc5_opterm.isNull()
                       ? TRACE_SOLVER(mkTerm, cvc5_kind, cvc5_args)
                       : TRACE_SOLVER(mkTerm, cvc5_opterm, cvc5_args);
      }
      break;

    case 2:
      if (kind == Op::AND && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = TRACE_METHOD(andTerm, cvc5_args[0], cvc5_args[1]);
      }
      else if (kind == Op::OR && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = TRACE_METHOD(orTerm, cvc5_args[0], cvc5_args[1]);
      }
      else if (kind == Op::XOR && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = TRACE_METHOD(xorTerm, cvc5_args[0], cvc5_args[1]);
      }
      else if (kind == Op::EQUAL && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = TRACE_METHOD(eqTerm, cvc5_args[0], cvc5_args[1]);
      }
      else if (kind == Op::IMPLIES && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = TRACE_METHOD(impTerm, cvc5_args[0], cvc5_args[1]);
      }
      else
      {
        cvc5_res = cvc5_opterm.isNull()
                       ? TRACE_SOLVER(mkTerm, cvc5_kind, cvc5_args)
                       : TRACE_SOLVER(mkTerm, cvc5_opterm, cvc5_args);
      }
      break;

    case 3:
      if (kind == Op::ITE && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res =
            TRACE_METHOD(iteTerm, cvc5_args[0], cvc5_args[1], cvc5_args[2]);
        break;
      }
      else
      {
        cvc5_res = cvc5_opterm.isNull()
                       ? TRACE_SOLVER(mkTerm, cvc5_kind, cvc5_args)
                       : TRACE_SOLVER(mkTerm, cvc5_opterm, cvc5_args);
      }
      break;

    default:
      assert(n_args == MURXLA_MK_TERM_N_ARGS_BIN || n_args > 3);
      cvc5_res = cvc5_opterm.isNull()
                     ? TRACE_SOLVER(mkTerm, cvc5_kind, cvc5_args)
                     : TRACE_SOLVER(mkTerm, cvc5_opterm, cvc5_args);
  }
DONE:
  MURXLA_TEST(!cvc5_res.isNull());
  MURXLA_TEST(cvc5_kind == cvc5_res.getKind()
              || cvc5_kind == ::cvc5::Kind::INTERNAL_KIND
              || (cvc5_res.getSort().isBoolean()
                  && cvc5_res.getKind() == ::cvc5::Kind::AND));
  return std::shared_ptr<Cvc5Term>(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
}

::cvc5::DatatypeConstructor
Cvc5Solver::getDatatypeConstructor(::cvc5::Sort dt_sort,
                                   const std::string& ctor_name)
{
  ::cvc5::Datatype dt = TRACE_METHOD(getDatatype, dt_sort);
  ::cvc5::DatatypeConstructor res;
  auto choice = d_rng.pick_one_of_three();
  if (choice == RNGenerator::Choice::FIRST)
  {
    res = TRACE_METHOD(operator[], dt, ctor_name);
  }
  else if (choice == RNGenerator::Choice::SECOND)
  {
    auto ch = d_rng.pick_one_of_four();
    ::cvc5::Datatype::const_iterator it, end;
    if (ch == RNGenerator::Choice::FIRST)
    {
      for (it = dt.begin(), end = dt.end(); it != end; ++it)
      {
        if (it->getName() == ctor_name)
        {
          res = *it;
          TRACE_METHOD(operator[], dt, ctor_name);
          break;
        }
      }
    }
    else if (ch == RNGenerator::Choice::SECOND)
    {
      for (it = dt.begin(), end = dt.end(); it != end; it++)
      {
        if (it->getName() == ctor_name)
        {
          res = *it;
          TRACE_METHOD(operator[], dt, ctor_name);
          break;
        }
      }
    }
    else if (ch == RNGenerator::Choice::THIRD)
    {
      for (it = dt.begin(), end = dt.end(); !(it == end); ++it)
      {
        if (it->getName() == ctor_name)
        {
          res = *it;
          TRACE_METHOD(operator[], dt, ctor_name);
          break;
        }
      }
    }
    else
    {
      for (it = dt.begin(), end = dt.end(); !(it == end); it++)
      {
        if (it->getName() == ctor_name)
        {
          res = *it;
          TRACE_METHOD(operator[], dt, ctor_name);
          break;
        }
      }
    }
  }
  else
  {
    res = TRACE_METHOD(getConstructor, dt, ctor_name);
  }
  MURXLA_TEST(!res.isNull());
  return res;
}

::cvc5::DatatypeSelector
Cvc5Solver::getDatatypeSelector(::cvc5::Sort dt_sort,
                                const std::string& ctor_name,
                                const std::string& sel_name)
{
  ::cvc5::DatatypeConstructor ctor = getDatatypeConstructor(dt_sort, ctor_name);
  ::cvc5::DatatypeSelector res;
  auto choice = d_rng.pick_one_of_four();
  if (choice == RNGenerator::Choice::FIRST)
  {
    res = TRACE_METHOD(operator[], ctor, sel_name);
  }
  else if (choice == RNGenerator::Choice::SECOND)
  {
    auto ch = d_rng.pick_one_of_four();
    if (ch == RNGenerator::Choice::FIRST)
    {
      for (auto it = ctor.begin(), end = ctor.end(); it != end; ++it)
      {
        if (it->getName() == sel_name)
        {
          res = TRACE_METHOD(operator[], ctor, sel_name);
          (void) *it;
          break;
        }
      }
    }
    else if (ch == RNGenerator::Choice::SECOND)
    {
      for (auto it = ctor.begin(), end = ctor.end(); it != end; it++)
      {
        if (it->getName() == sel_name)
        {
          res = TRACE_METHOD(operator[], ctor, sel_name);
          (void) *it;
          break;
        }
      }
    }
    else if (ch == RNGenerator::Choice::THIRD)
    {
      for (auto it = ctor.begin(), end = ctor.end(); !(it == end); ++it)
      {
        if (it->getName() == sel_name)
        {
          res = TRACE_METHOD(operator[], ctor, sel_name);
          (void) *it;
          break;
        }
      }
    }
    else
    {
      for (auto it = ctor.begin(), end = ctor.end(); !(it == end); it++)
      {
        if (it->getName() == sel_name)
        {
          res = TRACE_METHOD(operator[], ctor, sel_name);
          (void) *it;
          break;
        }
      }
    }
  }
  else if (choice == RNGenerator::Choice::THIRD)
  {
    res = TRACE_METHOD(getSelector, ctor, sel_name);
  }
  else
  {
    res = TRACE_METHOD(getDatatype().getSelector, dt_sort, sel_name);
  }

  MURXLA_TEST(!res.isNull());
  return res;
}

::cvc5::Term
Cvc5Solver::getDatatypeConstructorTerm(::cvc5::Sort dt_sort,
                                       const std::string& ctor_name)
{
  if (d_rng.flip_coin())
  {
    return TRACE_METHOD(getDatatype().getConstructorTerm, dt_sort, ctor_name);
  }
  auto dtc = getDatatypeConstructor(dt_sort, ctor_name);
  return TRACE_METHOD(getConstructorTerm, dtc);
}

::cvc5::Term
Cvc5Solver::getDatatypeSelectorTerm(::cvc5::Sort dt_sort,
                                    const std::string& ctor_name,
                                    const std::string& sel_name)
{
  if (d_rng.flip_coin())
  {
    auto dts = getDatatypeSelector(dt_sort, ctor_name, sel_name);
    return TRACE_METHOD(getSelectorTerm, dts);
  }
  auto dtc = getDatatypeConstructor(dt_sort, ctor_name);
  return TRACE_METHOD(getSelectorTerm, dtc, sel_name);
}

Term
Cvc5Solver::mk_term(const Op::Kind& kind,
                    const std::vector<std::string>& str_args,
                    const std::vector<Term>& args)
{
  MURXLA_CHECK_CONFIG(Cvc5Term::s_kinds_to_cvc5_kinds.find(kind)
                      != Cvc5Term::s_kinds_to_cvc5_kinds.end())
      << "Cvc5Solver: operator kind '" << kind << "' not configured";

  ::cvc5::Term cvc5_res;
  ::cvc5::Kind cvc5_kind = Cvc5Term::s_kinds_to_cvc5_kinds.at(kind);
  std::vector<::cvc5::Term> cvc5_args = Cvc5Term::terms_to_cvc5_terms(args);

  ::cvc5::Sort cvc5_dt_sort = cvc5_args[0].getSort();

  ::cvc5::Op cvc5_opterm;
  if (d_rng.flip_coin())
  {
    cvc5_opterm = TRACE_SOLVER(mkOp, cvc5_kind);
  }

  if (kind == Op::DT_APPLY_SEL)
  {
    assert(str_args.size() == 2);
    assert(args.size() == 1);

    ::cvc5::Term cvc5_sel_term =
        getDatatypeSelectorTerm(cvc5_dt_sort, str_args[0], str_args[1]);
    cvc5_res =
        cvc5_opterm.isNull()
            ? TRACE_SOLVER(
                mkTerm, cvc5_kind, std::vector{cvc5_sel_term, cvc5_args[0]})
            : TRACE_SOLVER(
                mkTerm, cvc5_opterm, std::vector{cvc5_sel_term, cvc5_args[0]});
  }
  else
  {
    if (kind == Op::DT_APPLY_TESTER)
    {
      assert(str_args.size() == 1);
      assert(args.size() == 1);
      ::cvc5::DatatypeConstructor cvc5_ctor =
          getDatatypeConstructor(cvc5_dt_sort, str_args[0]);
      cvc5_res =
          cvc5_opterm.isNull()
              ? TRACE_SOLVER(mkTerm,
                             cvc5_kind,
                             std::vector{TRACE_METHOD(getTesterTerm, cvc5_ctor),
                                         cvc5_args[0]})
              : TRACE_SOLVER(mkTerm,
                             cvc5_opterm,
                             std::vector{TRACE_METHOD(getTesterTerm, cvc5_ctor),
                                         cvc5_args[0]});
    }
    else
    {
      assert(kind == Op::DT_APPLY_UPDATER);
      assert(str_args.size() == 2);
      assert(args.size() == 2);

      ::cvc5::DatatypeSelector cvc5_sel =
          getDatatypeSelector(cvc5_dt_sort, str_args[0], str_args[1]);
      cvc5_res =
          cvc5_opterm.isNull()
              ? TRACE_SOLVER(mkTerm,
                             cvc5_kind,
                             std::vector{TRACE_METHOD(getUpdaterTerm, cvc5_sel),
                                         cvc5_args[0],
                                         cvc5_args[1]})
              : TRACE_SOLVER(mkTerm,
                             cvc5_opterm,
                             std::vector{TRACE_METHOD(getUpdaterTerm, cvc5_sel),
                                         cvc5_args[0],
                                         cvc5_args[1]});
    }
  }
  MURXLA_TEST(!cvc5_res.isNull());
  MURXLA_TEST(cvc5_kind == cvc5_res.getKind()
              || (cvc5_res.getSort().isBoolean()
                  && cvc5_res.getKind() == ::cvc5::Kind::AND));
  return std::shared_ptr<Cvc5Term>(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_term(const Op::Kind& kind,
                    Sort sort,
                    const std::vector<std::string>& str_args,
                    const std::vector<Term>& args)
{
  assert(sort);
  assert(sort->is_dt());

  ::cvc5::Term cvc5_res;
  ::cvc5::Kind cvc5_kind    = Cvc5Term::s_kinds_to_cvc5_kinds.at(kind);
  ::cvc5::Sort cvc5_dt_sort = Cvc5Sort::get_cvc5_sort(sort);
  std::vector<::cvc5::Term> cvc5_args = Cvc5Term::terms_to_cvc5_terms(args);

  if (kind == Op::DT_MATCH_BIND_CASE)
  {
    std::vector<::cvc5::Term> cvc5_vars;
    for (size_t i = 0; i < args.size() - 1; ++i)
    {
      cvc5_vars.push_back(cvc5_args[i]);
    }
    ::cvc5::Term cvc5_bvl =
        d_rng.flip_coin()
            ? TRACE_SOLVER(mkTerm, ::cvc5::Kind::VARIABLE_LIST, cvc5_vars)
            : TRACE_SOLVER(mkTerm,
                           TRACE_SOLVER(mkOp, ::cvc5::Kind::VARIABLE_LIST),
                           cvc5_vars);

    if (str_args.size() == 1)
    {
      std::vector<Term> vars{args.begin(), args.end() - 1};
      Term acons = mk_term(Op::DT_APPLY_CONS, sort, str_args, vars);
      ::cvc5::Term cvc5_acons = Cvc5Term::get_cvc5_term(acons);
      cvc5_args                    = {cvc5_bvl, cvc5_acons, cvc5_args.back()};
    }
    else
    {
      assert(cvc5_vars.size() == 1);
      cvc5_args = {cvc5_bvl, cvc5_vars[0], cvc5_args.back()};
    }
  }
  else if (kind == Op::DT_MATCH_CASE)
  {
    assert(str_args.size() == 1);
    Term acons = mk_term(Op::DT_APPLY_CONS, sort, str_args, {});
    ::cvc5::Term cvc5_acons      = Cvc5Term::get_cvc5_term(acons);
    cvc5_args                    = {cvc5_acons, cvc5_args.back()};
  }
  else
  {
    assert(kind == Op::DT_APPLY_CONS);
    assert(str_args.size() == 1);

    ::cvc5::Term cvc5_ctor_term;
    if (sort->is_dt_instantiated())
    {
      auto dt  = TRACE_METHOD(getDatatype, cvc5_dt_sort);
      auto dtc = TRACE_METHOD(getConstructor, dt, str_args[0]);
      cvc5_ctor_term =
          TRACE_METHOD(getInstantiatedConstructorTerm, dtc, cvc5_dt_sort);
    }
    else
    {
      cvc5_ctor_term = getDatatypeConstructorTerm(cvc5_dt_sort, str_args[0]);
    }
    cvc5_args.insert(cvc5_args.begin(), cvc5_ctor_term);
  }

  if (d_rng.flip_coin())
  {
    ::cvc5::Op cvc5_opterm      = TRACE_SOLVER(mkOp, cvc5_kind);
    cvc5_res                    = TRACE_SOLVER(mkTerm, cvc5_opterm, cvc5_args);
  }
  else
  {
    cvc5_res = TRACE_SOLVER(mkTerm, cvc5_kind, cvc5_args);
  }
  MURXLA_TEST(!cvc5_res.isNull());
  MURXLA_TEST(cvc5_kind == cvc5_res.getKind());
  return std::shared_ptr<Cvc5Term>(
      new Cvc5Term(d_tracer, d_rng, d_solver, cvc5_res));
}

Sort
Cvc5Solver::get_sort(Term term, SortKind sort_kind)
{
  (void) sort_kind;
  ::cvc5::Term cvc5_term = Cvc5Term::get_cvc5_term(term);
  return std::shared_ptr<Cvc5Sort>(
      new Cvc5Sort(d_tracer, d_solver, cvc5_term.getSort()));
}

void
Cvc5Solver::assert_formula(const Term& t)
{
  TRACE_SOLVER(assertFormula, Cvc5Term::get_cvc5_term(t));
}

Solver::Result
Cvc5Solver::check_sat()
{
  ::cvc5::Result res = TRACE_SOLVER(checkSat);
  MURXLA_TEST(!res.isNull());
  MURXLA_TEST(res != ::cvc5::Result());
  MURXLA_TEST(!d_rng.pick_with_prob(1) || res == res);
  if (res.isSat()) return Result::SAT;
  if (res.isUnsat()) return Result::UNSAT;
  MURXLA_TEST(res.isUnknown());
  if (d_rng.pick_with_prob(1))
  {
    (void) res.getUnknownExplanation();
  }
  return Result::UNKNOWN;
}

Solver::Result
Cvc5Solver::check_sat_assuming(const std::vector<Term>& assumptions)
{
  ::cvc5::Result res;
  std::vector<::cvc5::Term> cvc5_assumptions =
      Cvc5Term::terms_to_cvc5_terms(assumptions);

  MURXLA_TEST(assumptions.size() == cvc5_assumptions.size());

  res = cvc5_assumptions.size() == 1 && d_rng.flip_coin()
            ? TRACE_SOLVER(checkSatAssuming, cvc5_assumptions[0])
            : TRACE_SOLVER(checkSatAssuming, cvc5_assumptions);
  MURXLA_TEST(!res.isNull());
  MURXLA_TEST(!d_rng.pick_with_prob(1) || res == res);
  MURXLA_TEST(res != ::cvc5::Result());
  if (res.isSat()) return Result::SAT;
  if (res.isUnsat()) return Result::UNSAT;
  MURXLA_TEST(res.isUnknown());
  if (d_rng.pick_with_prob(1))
  {
    (void) res.getUnknownExplanation();
  }
  return Result::UNKNOWN;
}

std::vector<Term>
Cvc5Solver::get_unsat_assumptions()
{
  std::vector<Term> res;
  std::vector<::cvc5::Term> cvc5_res = TRACE_SOLVER(getUnsatAssumptions);
  return Cvc5Term::cvc5_terms_to_terms(d_tracer, d_rng, d_solver, cvc5_res);
}

std::vector<Term>
Cvc5Solver::get_unsat_core()
{
  std::vector<Term> res;
  std::vector<::cvc5::Term> cvc5_res = TRACE_SOLVER(getUnsatCore);
  return Cvc5Term::cvc5_terms_to_terms(d_tracer, d_rng, d_solver, cvc5_res);
}

std::vector<Term>
Cvc5Solver::get_value(const std::vector<Term>& terms)
{
  std::vector<Term> res;
  std::vector<::cvc5::Term> cvc5_res;
  std::vector<::cvc5::Term> cvc5_terms = Cvc5Term::terms_to_cvc5_terms(terms);

  if (d_rng.flip_coin())
  {
    cvc5_res = d_solver->getValue(cvc5_terms);
  }
  else
  {
    for (::cvc5::Term& t : cvc5_terms)
    {
      cvc5_res.push_back(d_solver->getValue(t));
    }
  }
  return Cvc5Term::cvc5_terms_to_terms(d_tracer, d_rng, d_solver, cvc5_res);
}

void
Cvc5Solver::push(uint32_t n_levels)
{
  TRACE_SOLVER(push, n_levels);
}

void
Cvc5Solver::pop(uint32_t n_levels)
{
  TRACE_SOLVER(pop, n_levels);
}

void
Cvc5Solver::print_model()
{
  /* no direct support in the API */
}

void
Cvc5Solver::set_logic(const std::string& logic)
{
  d_logic = logic;
  TRACE_SOLVER(setLogic, logic);
}

void
Cvc5Solver::reset()
{
  delete d_solver;
  d_solver = nullptr;
  new_solver();
}

void
Cvc5Solver::reset_assertions()
{
  TRACE_SOLVER(resetAssertions);
}

void
Cvc5Solver::set_opt(const std::string& opt, const std::string& value)
{
  // Check if opt=value conflicts with already enabled options.
  ::cvc5::Solver check_opt_slv;
  for (const auto& [o, v] : d_enabled_options)
  {
    check_opt_slv.setOption(o, v);
  }

  try
  {
    check_opt_slv.setLogic(d_logic);
    check_opt_slv.setOption(opt, value);
    check_opt_slv.checkSat();  // Trigger option checks
  }
  catch (const ::cvc5::CVC5ApiOptionException& e)
  {
    throw MurxlaSolverOptionException("incompatible option");
  }

  // TODO: remove after solver configuration refactor
  if ((opt == "assign-function-values" && value == "false"
       && d_solver->getOption("produce-models") == "true")
      || (opt == "produce-models" && value == "true"
          && d_solver->getOption("assign-function-values") == "false"))
  {
    throw MurxlaSolverOptionException("incompatible option");
  }

  TRACE_SOLVER(setOption, opt, value);
  d_enabled_options.emplace_back(opt, value);
}

void
Cvc5Solver::check_value(Term term)
{
  ::cvc5::Term cvc5_term = Cvc5Term::get_cvc5_term(term);

  if (cvc5_term.isFloatingPointNaN() || cvc5_term.isFloatingPointNegInf()
      || cvc5_term.isFloatingPointNegZero() || cvc5_term.isFloatingPointPosInf()
      || cvc5_term.isFloatingPointPosZero() || cvc5_term.isFloatingPointValue())
  {
    (void) cvc5_term.getFloatingPointValue();
  }
  if (cvc5_term.isInt32Value())
  {
    (void) cvc5_term.getInt32Value();
  }
  if (cvc5_term.isInt64Value())
  {
    (void) cvc5_term.getInt64Value();
  }
  if (cvc5_term.isBooleanValue())
  {
    (void) cvc5_term.getBooleanValue();
  }
  if (cvc5_term.isBitVectorValue())
  {
    auto choice = d_rng.pick_one_of_three();
    if (choice == RNGenerator::Choice::FIRST)
    {
      (void) cvc5_term.getBitVectorValue(2);
    }
    else if (choice == RNGenerator::Choice::SECOND)
    {
      (void) cvc5_term.getBitVectorValue(10);
    }
    else
    {
      (void) cvc5_term.getBitVectorValue(16);
    }
  }
  if (cvc5_term.isRealValue())
  {
    (void) cvc5_term.getRealValue();
    (void) cvc5_term.getRealOrIntegerValueSign();
  }
  if (cvc5_term.isReal32Value())
  {
    (void) cvc5_term.getReal32Value();
    (void) cvc5_term.getRealOrIntegerValueSign();
  }
  if (cvc5_term.isReal64Value())
  {
    (void) cvc5_term.getReal64Value();
    (void) cvc5_term.getRealOrIntegerValueSign();
  }
  if (cvc5_term.isUInt32Value())
  {
    (void) cvc5_term.getUInt32Value();
    (void) cvc5_term.getRealOrIntegerValueSign();
  }
  if (cvc5_term.isUInt64Value())
  {
    (void) cvc5_term.getUInt64Value();
    (void) cvc5_term.getRealOrIntegerValueSign();
  }
  if (cvc5_term.isStringValue())
  {
    (void) cvc5_term.getStringValue();
  }
  if (cvc5_term.isTupleValue())
  {
    (void) cvc5_term.getTupleValue();
  }
  if (cvc5_term.isUninterpretedSortValue())
  {
    (void) cvc5_term.getUninterpretedSortValue();
  }
}

void
Cvc5Solver::check_sort(Sort sort)
{
  ::cvc5::Sort cvc5_sort = Cvc5Sort::get_cvc5_sort(sort);

  if (cvc5_sort.isDatatype())
  {
    const auto& cons_names = sort->get_dt_cons_names();
    const std::string& ctor =
        d_rng.pick_from_set<decltype(cons_names), std::string>(cons_names);

    ::cvc5::Datatype cvc5_dt = cvc5_sort.getDatatype();
    (void) cvc5_dt.isRecord();
    if (!cvc5_dt.isParametric())
    {
      (void) cvc5_dt.isFinite();
    }
    else
    {
      auto dt_params      = sort->get_sorts();
      auto cvc5_dt_params = cvc5_dt.getParameters();
      MURXLA_TEST(dt_params.size() == cvc5_dt_params.size());
      for (size_t i = 0, n = dt_params.size(); i < n; ++i)
      {
        MURXLA_TEST(cvc5_dt_params[i].hasSymbol());
        MURXLA_TEST(checked_cast<ParamSort*>(dt_params[i].get())->get_symbol()
                    == cvc5_dt_params[i].getSymbol());
      }
      MURXLA_TEST(cvc5_dt_params == cvc5_sort.getDatatype().getParameters());
    }

    ::cvc5::Term cvc5_ctor_term =
        d_rng.flip_coin() ? cvc5_dt.getConstructorTerm(ctor)
                          : cvc5_dt.getConstructor(ctor).getConstructorTerm();
    MURXLA_TEST(cvc5_ctor_term.getSort().isConstructor());

    ::cvc5::Term cvc5_tester_term =
        cvc5_dt.getConstructor(ctor).getTesterTerm();
    MURXLA_TEST(cvc5_tester_term.getSort().isTester());
    MURXLA_TEST(cvc5_tester_term.getSort().getTesterDomainSort()
                == Cvc5Sort::get_cvc5_sort(sort));
    MURXLA_TEST(cvc5_tester_term.getSort().getTesterCodomainSort().isBoolean());

    const auto& sel_names = sort->get_dt_sel_names(ctor);

    MURXLA_TEST(sel_names.size()
                == cvc5_ctor_term.getSort().getConstructorArity());

    std::vector<Sort> ctor_domain_sorts;

    if (!sel_names.empty())
    {
      for (const auto& sel : sel_names)
      {
        ctor_domain_sorts.push_back(sort->get_dt_sel_sort(sort, ctor, sel));
      }

      const std::string& sel =
          d_rng.pick_from_set<decltype(sel_names), std::string>(sel_names);

      ::cvc5::DatatypeSelector cvc5_sel =
          d_rng.flip_coin() ? cvc5_dt.getSelector(sel)
                            : cvc5_dt.getConstructor(ctor).getSelector(sel);

      ::cvc5::Term cvc5_sel_term = cvc5_sel.getSelectorTerm();

      MURXLA_TEST(cvc5_sel_term.getSort().isSelector());

      Sort sel_codomain = sort->get_dt_sel_sort(sort, ctor, sel);
      ::cvc5::Sort cvc5_sel_codomain =
          cvc5_sel_term.getSort().getSelectorCodomainSort();
      ::cvc5::Sort cvc5_sel_domain =
          cvc5_sel_term.getSort().getSelectorDomainSort();
      MURXLA_TEST(cvc5_sel_domain == Cvc5Sort::get_cvc5_sort(sort));
      if (sel_codomain == nullptr)
      {
        MURXLA_TEST(cvc5_sel_codomain == Cvc5Sort::get_cvc5_sort(sort));
      }
      else if (!sel_codomain->is_param_sort()
               && !sel_codomain->is_unresolved_sort())
      {
        MURXLA_TEST(cvc5_sel_codomain == Cvc5Sort::get_cvc5_sort(sel_codomain));
      }

      MURXLA_TEST(cvc5_sel.getUpdaterTerm().getSort().isUpdater());
    }

    std::vector<::cvc5::Sort> cvc5_ctor_domain_sorts =
        cvc5_ctor_term.getSort().getConstructorDomainSorts();
    MURXLA_TEST(cvc5_ctor_domain_sorts.size() == ctor_domain_sorts.size());
    for (size_t i = 0, n = ctor_domain_sorts.size(); i < n; ++i)
    {
      if (ctor_domain_sorts[i] == nullptr)
      {
        MURXLA_TEST(cvc5_ctor_domain_sorts[i] == Cvc5Sort::get_cvc5_sort(sort));
      }
      else if (!ctor_domain_sorts[i]->is_param_sort()
               && !ctor_domain_sorts[i]->is_unresolved_sort())
      {
        MURXLA_TEST(cvc5_ctor_domain_sorts[i]
                    == Cvc5Sort::get_cvc5_sort(ctor_domain_sorts[i]));
      }
    }
    MURXLA_TEST(cvc5_ctor_term.getSort().getConstructorCodomainSort()
                == Cvc5Sort::get_cvc5_sort(sort));

    const auto& sorts = sort->get_sorts();
    MURXLA_TEST(sorts.size() == cvc5_sort.getDatatypeArity());
    /* Note: isParametricDatatype() returns true for both instantiated and
     *       non-instantiated datatypes. */
    if (cvc5_dt.isParametric())
    {
      if (!sorts.empty())
      {
        const auto& cvc5_param_sorts = cvc5_sort.getDatatype().getParameters();
        MURXLA_TEST(cvc5_param_sorts.size() == sorts.size());
      }
    }
  }
  else
  {
    MURXLA_TEST(!cvc5_sort.isSelector());
    MURXLA_TEST(!cvc5_sort.isTester());
    MURXLA_TEST(!cvc5_sort.isUpdater());
  }

  if (cvc5_sort.isTuple())
  {
    (void) cvc5_sort.getTupleLength();
    (void) cvc5_sort.getTupleSorts();
  }
  else if (cvc5_sort.isRecord())
  {
  }
  else if (cvc5_sort.isUninterpretedSort())
  {
  }
  else if (cvc5_sort.isUninterpretedSortConstructor())
  {
    (void) cvc5_sort.getUninterpretedSortConstructorArity();
  }
  if (cvc5_sort.isFunction())
  {
    MURXLA_TEST(!cvc5_sort.getFunctionCodomainSort().isBoolean()
                || cvc5_sort.isPredicate());
  }
  else
  {
    MURXLA_TEST(!cvc5_sort.isPredicate());
  }
  MURXLA_TEST(cvc5_sort >= cvc5_sort);
  MURXLA_TEST(cvc5_sort <= cvc5_sort);
  MURXLA_TEST(!(cvc5_sort > cvc5_sort));
  MURXLA_TEST(!(cvc5_sort < cvc5_sort));
  MURXLA_TEST(!cvc5_sort.hasSymbol() || !cvc5_sort.getSymbol().empty());
}

void
Cvc5Solver::check_term(Term term)
{
  ::cvc5::Term cvc5_term = Cvc5Term::get_cvc5_term(term);

  MURXLA_TEST(!(cvc5_term != cvc5_term));
  MURXLA_TEST(cvc5_term >= cvc5_term);
  MURXLA_TEST(cvc5_term <= cvc5_term);
  MURXLA_TEST(!(cvc5_term > cvc5_term));
  MURXLA_TEST(!(cvc5_term < cvc5_term));
  MURXLA_TEST(!cvc5_term.hasSymbol() || !cvc5_term.getSymbol().empty());
  MURXLA_TEST(!term->is_indexed() || cvc5_term.hasOp());
  MURXLA_TEST(term->is_indexed() || term->get_num_indices() == 0);
  MURXLA_TEST(cvc5_term.getId() != 0);

  /* Note: cvc5 considers empty sets and sets of the form (canonical) constant
   *       set value
   *       (union
   *         (singleton c1) ...
   *         (union (singleton c_{n-1}) (singleton c_n))))
   *       where c_1 ... c_n are values ordered by id s.t. c_1 > ... > c_n.
   *       A universe set term is not considered a set value, in fact, no
   *       term created via mk_value is.  Hence, we can't test these in
   *       check_value() but must check them here.
   */
  if (cvc5_term.isSetValue())
  {
    auto cvc5_set_value = cvc5_term.getSetValue();
    MURXLA_TEST(!cvc5_set_value.empty()
                || cvc5_term.getKind() == ::cvc5::Kind::SET_EMPTY);
    for (const auto& t : cvc5_set_value)
    {
      MURXLA_TEST(!t.isNull());
    }
  }
}

std::unordered_map<std::string, std::string>
Cvc5Solver::get_required_options(Theory theory) const
{
  std::unordered_map<std::string, std::string> reqopts;
  if (theory == THEORY_BAG)
  {
    reqopts.emplace("fmf-bound", "true");
  }
  else if (theory == THEORY_FP)
  {
    reqopts.emplace("fp-exp", "true");
  }
  else if (theory == THEORY_SET)
  {
    reqopts.emplace("sets-ext", "true");
  }
  else if (theory == THEORY_STRING || theory == THEORY_SEQ)
  {
    reqopts.emplace("strings-exp", "true");
  }
  return reqopts;
}

/* -------------------------------------------------------------------------- */

std::string
Cvc5Solver::get_option_name_incremental() const
{
  return "incremental";
}

std::string
Cvc5Solver::get_option_name_model_gen() const
{
  return "produce-models";
}

std::string
Cvc5Solver::get_option_name_unsat_assumptions() const
{
  return "produce-unsat-assumptions";
}

std::string
Cvc5Solver::get_option_name_unsat_cores() const
{
  return "produce-unsat-cores";
}

bool
Cvc5Solver::option_incremental_enabled() const
{
  return d_solver->getOption("incremental") == "true";
}

bool
Cvc5Solver::option_model_gen_enabled() const
{
  return d_solver->getOption("produce-models") == "true";
}

bool
Cvc5Solver::option_unsat_assumptions_enabled() const
{
  return d_solver->getOption("produce-unsat-assumptions") == "true";
}

bool
Cvc5Solver::option_unsat_cores_enabled() const
{
  return d_solver->getOption("produce-unsat-cores") == "true";
}

/* -------------------------------------------------------------------------- */
/* OpKindManager configuration.                                               */
/* -------------------------------------------------------------------------- */

void
Cvc5Solver::configure_opmgr(OpKindManager* opmgr) const
{
  /* Add solver-specific operators. */
  // BV
  opmgr->add_op_kind(
      Cvc5Term::OP_BV_REDAND, 1, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      Cvc5Term::OP_BV_REDOR, 1, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      Cvc5Term::OP_BV_ULTBV, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      Cvc5Term::OP_BV_SLTBV, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(Cvc5Term::OP_BV_ITE, 3, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      Cvc5Term::OP_BV_TO_NAT, 1, 0, SORT_INT, {SORT_BV}, THEORY_BV);
  // Datatypes
  opmgr->add_op_kind(
      Cvc5Term::OP_DT_SIZE, 1, 0, SORT_INT, {SORT_DT}, THEORY_DT);
  // Int
  opmgr->add_op_kind(
      Cvc5Term::OP_INT_TO_BV, 1, 1, SORT_BV, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      Cvc5Term::OP_INT_IAND, 2, 1, SORT_INT, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      Cvc5Term::OP_INT_POW2, 1, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  // Strings
  opmgr->add_op_kind(Cvc5Term::OP_STRING_UPDATE,
                     3,
                     0,
                     SORT_STRING,
                     {SORT_STRING, SORT_INT, SORT_STRING},
                     THEORY_STRING);
  opmgr->add_op_kind(Cvc5Term::OP_STRING_TOLOWER,
                     1,
                     0,
                     SORT_STRING,
                     {SORT_STRING},
                     THEORY_STRING);
  opmgr->add_op_kind(Cvc5Term::OP_STRING_TOUPPER,
                     1,
                     0,
                     SORT_STRING,
                     {SORT_STRING},
                     THEORY_STRING);
  opmgr->add_op_kind(
      Cvc5Term::OP_STRING_REV, 1, 0, SORT_STRING, {SORT_STRING}, THEORY_STRING);
}

/* -------------------------------------------------------------------------- */
/* FSM configuration.                                                         */
/* -------------------------------------------------------------------------- */

class Cvc5ActionSimplify : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "cvc5-simplify";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  Cvc5ActionSimplify(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    Term term = d_smgr.pick_term();
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
    d_smgr.reset_sat();
    Cvc5Solver& solver         = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5       = solver.get_solver();
    ::cvc5::Term cvc5_res      = cvc5->simplify(Cvc5Term::get_cvc5_term(term));
    MURXLA_TEST(!cvc5_res.isNull());

    /* Note: It is necessary for sequences to call Solver::simplify() to turn a
     *       sequence that is constructed by, e.g., concatenation of unit
     *       sequences, into a sequence value. Hence, we can't test these in
     *       check_value() but must check them here.
     */
    if (cvc5_res.isSequenceValue() && d_solver.get_rng().flip_coin())
    {
      auto cvc5_seq_value = cvc5_res.getSequenceValue();
      for (const auto& t : cvc5_seq_value)
      {
        MURXLA_TEST(!t.isNull());
      }
    }

    /* Note: The simplified term 'cvc5_res' may or may not be already in the
     *       term DB. Since we can't always compute the exact level, we can't
     *       add the simplified term to the term DB. */
  }
};

class Cvc5ActionGetDifficulty : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "cvc5-get-difficulty";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  Cvc5ActionGetDifficulty(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_sat_called) return false;
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    if (cvc5->getOption("produce-difficulty") == "false")
    {
      d_disable = true;
      return false;
    }
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
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    (void) cvc5->getDifficulty();
  }
};

class Cvc5ActionGetInterpolant : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "cvc5-get-interpolant";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  Cvc5ActionGetInterpolant(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term(SORT_BOOL, 0)) return false;
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    if (cvc5->getOption("produce-interpols") == "none")
    {
      d_disable = true;
      return false;
    }
    Term term = d_smgr.pick_term(SORT_BOOL, 0);
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
    d_smgr.reset_sat();
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    ::cvc5::Term cvc5_res;
    cvc5_res = cvc5->getInterpolant(Cvc5Term::get_cvc5_term(term));
    /* Note: We don't add the interpolant to the term db for now, since this
     *       requires refactoring untrace to support optional results. In
     *       this case we would trace "return t(nil) s(nil)" when the
     *       command was not successful (result of getInterpolant() is false),
     *       which is currently not supported by the untracer.
     */
    if (d_smgr.d_incremental && !cvc5_res.isNull())
    {
      do
      {
        cvc5_res = cvc5->getInterpolantNext();
      } while (!cvc5_res.isNull() && d_solver.get_rng().flip_coin());
    }
  }
};

class Cvc5ActionGetAbduct : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "cvc5-get-abduct";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  Cvc5ActionGetAbduct(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term(SORT_BOOL, 0)) return false;
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    if (cvc5->getOption("produce-abducts") == "false")
    {
      d_disable = true;
      return false;
    }
    Term term = d_smgr.pick_term(SORT_BOOL, 0);
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
    d_smgr.reset_sat();
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    ::cvc5::Term cvc5_res;
    cvc5_res = cvc5->getAbduct(Cvc5Term::get_cvc5_term(term));
    /* Note: We don't add the abduct to the term db for now, since this
     *       requires refactoring untrace to support optional results. In
     *       this case we would trace "return t(nil) s(nil)" when the
     *       command was not successful (result of getAbduct() is false),
     *       which is currently not supported by the untracer.
     */
    if (d_smgr.d_incremental && !cvc5_res.isNull())
    {
      do
      {
        cvc5_res = cvc5->getAbductNext();
      } while (!cvc5_res.isNull() && d_rng.flip_coin());
    }
  }
};

class Cvc5ActionBlockModel : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "cvc5-block-model";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  Cvc5ActionBlockModel(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen)
    {
      d_disable = true;
      return false;
    }
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    if (cvc5->getOption("block-models") == "none"
        || cvc5->getOption("assign-function-values") == "false")
    {
      d_disable = true;
      return false;
    }
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
    d_smgr.reset_sat();
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    cvc5->blockModel();
  }
};

class Cvc5ActionBlockModelValues : public Action
{
 public:
  /** The maximum number of model values to block. */
  static constexpr uint32_t MAX_N_VALUES = 5;
  /** The name of this action. */
  inline static const Kind s_name = "cvc5-block-model-values";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  Cvc5ActionBlockModelValues(SolverManager& smgr) : Action(smgr, s_name, NONE)
  {
  }

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term(0)) return false;
    if (!d_smgr.d_model_gen)
    {
      d_disable = true;
      return false;
    }
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    if (cvc5->getOption("produce-assertions") == "false"
        || cvc5->getOption("assign-function-values") == "false")
    {
      d_disable = true;
      return false;
    }
    uint32_t n_values = d_rng.pick<uint32_t>(1, MAX_N_VALUES);
    std::vector<Term> values;
    for (uint32_t i = 0; i < n_values; ++i)
    {
      values.push_back(d_smgr.pick_term(0));
    }
    run(values);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);
    std::vector<Term> values;
    uint32_t n_values = str_to_uint32(tokens[0]);
    for (uint32_t i = 0, idx = 1; i < n_values; ++i, ++idx)
    {
      auto id = untrace_str_to_id(tokens[idx]);
      Term t  = get_untraced_term(id);
      MURXLA_CHECK_TRACE_TERM(t, id);
      values.push_back(t);
    }
    run(values);
    return {};
  }

 private:
  void run(const std::vector<Term>& values)
  {
    MURXLA_TRACE << get_kind() << " " << values.size() << values;
    d_smgr.reset_sat();
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    std::vector<::cvc5::Term> cvc5_values =
        Cvc5Term::terms_to_cvc5_terms(values);
    cvc5->blockModelValues(cvc5_values);
  }
};

class Cvc5ActionSortSubstitute : public Action
{
 public:
  /** The maximum number of sorts to be substituted. */
  static constexpr uint32_t MAX_N_SUBST_SORTS = 3;
  /** The name of this action. */
  inline static const Kind s_name = "cvc5-sort-substitute";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  Cvc5ActionSortSubstitute(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_sort_with_sort_params()) return false;
    Sort sort = d_smgr.pick_sort_with_sort_params();
    /* Pick sort to substitute. */
    std::vector<Sort> sub_sorts = get_sub_sorts(sort);
    if (sub_sorts.empty()) return false;
    size_t n_sorts = d_rng.pick<size_t>(
        1, std::min<size_t>(sub_sorts.size(), MAX_N_SUBST_SORTS));
    std::vector<Sort> to_subst_sorts;
    std::vector<Sort> subst_sorts;
    for (uint32_t i = 0; i < n_sorts; ++i)
    {
      Sort to_subst_sort =
          d_rng.pick_from_set<decltype(sub_sorts), Sort>(sub_sorts);
      to_subst_sorts.push_back(to_subst_sort);
      Sort subst_sort = d_smgr.pick_sort();
      subst_sorts.push_back(subst_sort);
    }

    run(sort, to_subst_sorts, subst_sorts);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS_MIN(5, "", tokens.size());

    Sort sort = get_untraced_sort(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);

    uint32_t idx              = 1;
    uint32_t n_to_subst_sorts = str_to_uint32(tokens[idx++]);
    std::vector<Sort> to_subst_sorts;
    for (size_t i = 0; i < n_to_subst_sorts; ++i)
    {
      to_subst_sorts.push_back(
          get_untraced_sort(untrace_str_to_id(tokens[idx])));
      MURXLA_CHECK_TRACE_SORT(to_subst_sorts.back(), tokens[idx]);
      idx += 1;
    }

    uint32_t n_subst_sorts = str_to_uint32(tokens[idx++]);
    std::vector<Sort> subst_sorts;
    for (size_t i = 0; i < n_subst_sorts; ++i)
    {
      subst_sorts.push_back(get_untraced_sort(untrace_str_to_id(tokens[idx])));
      MURXLA_CHECK_TRACE_SORT(subst_sorts.back(), tokens[idx]);
      idx += 1;
    }

    run(sort, to_subst_sorts, subst_sorts);
    return {};
  }

 private:
  void run(Sort sort,
           std::vector<Sort> to_subst_sorts,
           std::vector<Sort> subst_sorts)
  {
    MURXLA_TRACE << get_kind() << " " << sort << " " << to_subst_sorts.size()
                 << to_subst_sorts << " " << subst_sorts.size() << subst_sorts;
    d_smgr.reset_sat();
    ::cvc5::Sort cvc5_sort = Cvc5Sort::get_cvc5_sort(sort);
    std::vector<::cvc5::Sort> cvc5_to_subst_sorts =
        Cvc5Sort::sorts_to_cvc5_sorts(to_subst_sorts);
    std::vector<::cvc5::Sort> cvc5_subst_sorts =
        Cvc5Sort::sorts_to_cvc5_sorts(subst_sorts);

    ::cvc5::Sort cvc5_res;
    if (to_subst_sorts.size() == 1 && d_solver.get_rng().flip_coin())
    {
      cvc5_res =
          cvc5_sort.substitute(cvc5_to_subst_sorts[0], cvc5_subst_sorts[0]);
    }
    else
    {
      cvc5_res = cvc5_sort.substitute(cvc5_to_subst_sorts, cvc5_subst_sorts);
    }
    MURXLA_TEST(!cvc5_res.isNull());

    // TODO add sort
  }

  /**
   * Collect all known sub sorts (sorts registered in the sort DB) of a given
   * sort. Performs a pre-order traversal over sort.
   */
  std::vector<Sort> get_sub_sorts(Sort sort)
  {
    std::vector<Sort> res;
    std::unordered_set<::cvc5::Sort> cvc5_res;
    ::cvc5::Sort cvc5_sort = Cvc5Sort::get_cvc5_sort(sort);
    std::vector<::cvc5::Sort> to_visit{cvc5_sort};
    while (!to_visit.empty())
    {
      ::cvc5::Sort cvc5_vsort = to_visit.back();
      to_visit.pop_back();
      if (cvc5_vsort.isConstructor())
      {
        auto cvc5_domain   = cvc5_vsort.getConstructorDomainSorts();
        auto cvc5_codomain = cvc5_vsort.getConstructorCodomainSort();
        cvc5_res.insert(cvc5_domain.begin(), cvc5_domain.end());
        cvc5_res.insert(cvc5_codomain);
        to_visit.insert(to_visit.end(), cvc5_domain.begin(), cvc5_domain.end());
        to_visit.push_back(cvc5_codomain);
      }
      else if (cvc5_vsort.isSelector())
      {
        auto cvc5_domain   = cvc5_vsort.getSelectorDomainSort();
        auto cvc5_codomain = cvc5_vsort.getSelectorCodomainSort();
        cvc5_res.insert(cvc5_domain);
        cvc5_res.insert(cvc5_codomain);
        to_visit.push_back(cvc5_domain);
        to_visit.push_back(cvc5_codomain);
      }
      else if (cvc5_vsort.isTester())
      {
        auto cvc5_domain   = cvc5_vsort.getTesterDomainSort();
        auto cvc5_codomain = cvc5_vsort.getTesterCodomainSort();
        cvc5_res.insert(cvc5_domain);
        cvc5_res.insert(cvc5_codomain);
        to_visit.push_back(cvc5_domain);
        to_visit.push_back(cvc5_codomain);
      }
      else if (cvc5_vsort.isFunction())
      {
        auto cvc5_domain   = cvc5_vsort.getFunctionDomainSorts();
        auto cvc5_codomain = cvc5_vsort.getFunctionCodomainSort();
        cvc5_res.insert(cvc5_domain.begin(), cvc5_domain.end());
        cvc5_res.insert(cvc5_codomain);
        to_visit.insert(to_visit.end(), cvc5_domain.begin(), cvc5_domain.end());
        to_visit.push_back(cvc5_codomain);
      }
      else if (cvc5_vsort.isArray())
      {
        auto cvc5_elem  = cvc5_vsort.getArrayElementSort();
        auto cvc5_index = cvc5_vsort.getArrayIndexSort();
        cvc5_res.insert(cvc5_elem);
        cvc5_res.insert(cvc5_index);
        to_visit.push_back(cvc5_elem);
        to_visit.push_back(cvc5_index);
      }
      else if (cvc5_vsort.isBag())
      {
        auto cvc5_elem = cvc5_vsort.getBagElementSort();
        cvc5_res.insert(cvc5_elem);
        to_visit.push_back(cvc5_elem);
      }
      else if (cvc5_vsort.isSet())
      {
        auto cvc5_elem = cvc5_vsort.getSetElementSort();
        cvc5_res.insert(cvc5_elem);
        to_visit.push_back(cvc5_elem);
      }
      else if (cvc5_vsort.isSequence())
      {
        auto cvc5_elem = cvc5_vsort.getSequenceElementSort();
        cvc5_res.insert(cvc5_elem);
        to_visit.push_back(cvc5_elem);
      }
      else if (cvc5_vsort.isTuple())
      {
        auto sorts = cvc5_vsort.getTupleSorts();
        cvc5_res.insert(sorts.begin(), sorts.end());
        to_visit.insert(to_visit.end(), sorts.begin(), sorts.end());
      }
    }

    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    for (const ::cvc5::Sort& cvc5_s : cvc5_res)
    {
      Sort s = std::shared_ptr<Cvc5Sort>(
          new Cvc5Sort(solver.get_tracer(), cvc5, cvc5_s));
      s      = d_smgr.find_sort(s);
      if (s->get_kind() == SORT_ANY) continue;
      res.push_back(s);
    }
    return res;
  }
};

class Cvc5ActionTermSubstitute : public Action
{
 public:
  /** The maximum number of terms to be substituted. */
  static constexpr uint32_t MAX_N_SUBST_TERMS = 3;
  /** The name of this action. */
  inline static const Kind s_name = "cvc5-term-substitute";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  Cvc5ActionTermSubstitute(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    Term term = d_smgr.pick_term();
    /* Pick term to substitute. */
    std::vector<Term> sub_terms = get_sub_terms(term);
    if (sub_terms.empty()) return false;
    size_t n_terms = d_rng.pick<size_t>(
        1, std::min<size_t>(sub_terms.size(), MAX_N_SUBST_TERMS));
    std::vector<Term> to_subst_terms;
    std::vector<Term> subst_terms;
    for (uint32_t i = 0; i < n_terms; ++i)
    {
      Term to_subst_term =
          d_rng.pick_from_set<decltype(sub_terms), Term>(sub_terms);
      to_subst_terms.push_back(to_subst_term);
      Sort to_subst_sort = to_subst_term->get_sort();
      Term subst_term    = d_smgr.pick_term(to_subst_sort);
      subst_terms.push_back(subst_term);
    }

    run(term, to_subst_terms, subst_terms);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS_MIN(5, "", tokens.size());

    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);

    uint32_t idx              = 1;
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

    run(term, to_subst_terms, subst_terms);
    return {};
  }

 private:
  void run(Term term,
           std::vector<Term> to_subst_terms,
           std::vector<Term> subst_terms)
  {
    MURXLA_TRACE << get_kind() << " " << term << " " << to_subst_terms.size()
                 << to_subst_terms << " " << subst_terms.size() << subst_terms;
    d_smgr.reset_sat();
    ::cvc5::Term cvc5_term = Cvc5Term::get_cvc5_term(term);
    std::vector<::cvc5::Term> cvc5_to_subst_terms =
        Cvc5Term::terms_to_cvc5_terms(to_subst_terms);
    std::vector<::cvc5::Term> cvc5_subst_terms =
        Cvc5Term::terms_to_cvc5_terms(subst_terms);

    ::cvc5::Term cvc5_res;
    if (to_subst_terms.size() == 1 && d_rng.flip_coin())
    {
      cvc5_res =
          cvc5_term.substitute(cvc5_to_subst_terms[0], cvc5_subst_terms[0]);
    }
    else
    {
      cvc5_res = cvc5_term.substitute(cvc5_to_subst_terms, cvc5_subst_terms);
    }
    MURXLA_TEST(!cvc5_res.isNull());
    /* Note: The substituted term 'cvc5_res' may or may not be already in the
     *       term DB. Since we can't always compute the exact level, we can't
     *       add the substituted term to the term DB. */
  }

  /**
   * Collect all known sub terms (terms registered in the term DB) of a given
   * term. Performs a pre-order traversal over term.
   */
  std::vector<Term> get_sub_terms(Term term)
  {
    std::vector<Term> res;
    std::unordered_set<::cvc5::Term> cvc5_res;
    ::cvc5::Term cvc5_term = Cvc5Term::get_cvc5_term(term);
    std::vector<::cvc5::Term> to_visit{cvc5_term};
    while (!to_visit.empty())
    {
      ::cvc5::Term cvc5_vterm = to_visit.back();
      to_visit.pop_back();
      auto ch = d_rng.pick_one_of_four();
      ::cvc5::Term::const_iterator it, end;
      switch (ch)
      {
        case RNGenerator::FIRST:
          for (const auto& cvc5_t : cvc5_vterm)
          {
            if (cvc5_res.find(cvc5_t) == cvc5_res.end())
            {
              cvc5_res.insert(cvc5_t);
              to_visit.push_back(cvc5_t);
            }
          }
          break;
        case RNGenerator::SECOND:
          for (size_t i = 0, n = cvc5_vterm.getNumChildren(); i < n; ++i)
          {
            ::cvc5::Term cvc5_t = cvc5_vterm[i];
            if (cvc5_res.find(cvc5_t) == cvc5_res.end())
            {
              cvc5_res.insert(cvc5_t);
              to_visit.push_back(cvc5_t);
            }
          }
          break;
        case RNGenerator::THIRD:
          if (d_rng.flip_coin())
          {
            for (it = cvc5_vterm.begin(), end = cvc5_vterm.end(); it != end;
                 ++it)
            {
              ::cvc5::Term cvc5_t = *it;
              if (cvc5_res.find(cvc5_t) == cvc5_res.end())
              {
                cvc5_res.insert(cvc5_t);
                to_visit.push_back(cvc5_t);
              }
            }
          }
          else
          {
            for (it = cvc5_vterm.begin(), end = cvc5_vterm.end(); !(it == end);
                 ++it)
            {
              ::cvc5::Term cvc5_t = *it;
              if (cvc5_res.find(cvc5_t) == cvc5_res.end())
              {
                cvc5_res.insert(cvc5_t);
                to_visit.push_back(cvc5_t);
              }
            }
          }
          break;
        default:
          if (d_rng.flip_coin())
          {
            for (it = cvc5_vterm.begin(), end = cvc5_vterm.end(); it != end;
                 it++)
            {
              ::cvc5::Term cvc5_t = *it;
              if (cvc5_res.find(cvc5_t) == cvc5_res.end())
              {
                cvc5_res.insert(cvc5_t);
                to_visit.push_back(cvc5_t);
              }
            }
          }
          else
          {
            for (it = cvc5_vterm.begin(), end = cvc5_vterm.end(); !(it == end);
                 it++)
            {
              ::cvc5::Term cvc5_t = *it;
              if (cvc5_res.find(cvc5_t) == cvc5_res.end())
              {
                cvc5_res.insert(cvc5_t);
                to_visit.push_back(cvc5_t);
              }
            }
          }
      }
    }

    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::Solver* cvc5      = solver.get_solver();
    for (const ::cvc5::Term& cvc5_t : cvc5_res)
    {
      Sort s = std::shared_ptr<Cvc5Sort>(
          new Cvc5Sort(solver.get_tracer(), cvc5, cvc5_t.getSort()));
      s      = d_smgr.find_sort(s);
      if (s->get_kind() == SORT_ANY) continue;
      Term t = std::shared_ptr<Cvc5Term>(
          new Cvc5Term(solver.get_tracer(), d_rng, cvc5, cvc5_t));
      t      = d_smgr.find_term(t, s, s->get_kind());
      if (t == nullptr) continue;
      res.push_back(t);
    }
    return res;
  }
};

/* -------------------------------------------------------------------------- */

void
Cvc5Solver::configure_fsm(FSM* fsm) const
{
  State* s_check_sat = fsm->get_state(State::CHECK_SAT);
  State* s_sat       = fsm->get_state(State::SAT);
  State* s_unsat     = fsm->get_state(State::UNSAT);

  // Sort::substitute(const Sort& sort, const Sort& subst_sort)
  auto a_sort_subst = fsm->new_action<Cvc5ActionSortSubstitute>();
  fsm->add_action_to_all_states(a_sort_subst, 1000);
  // Term::substitute(const Term& term, const Term& subst_term)
  auto a_term_subst = fsm->new_action<Cvc5ActionTermSubstitute>();
  fsm->add_action_to_all_states(a_term_subst, 1000);

  // Solver::simplify(const Term& term)
  auto a_simplify = fsm->new_action<Cvc5ActionSimplify>();
  fsm->add_action_to_all_states(a_simplify, 100);

  // Solver::blockModel()
  auto a_block_model = fsm->new_action<Cvc5ActionBlockModel>();
  s_sat->add_action(a_block_model, 4, s_check_sat);

  // Solver::blockModelModelValues(const std::vector& terms)
  auto a_block_model_values = fsm->new_action<Cvc5ActionBlockModelValues>();
  s_sat->add_action(a_block_model_values, 4, s_check_sat);

  // Solver::getInterpolant(const Term& term, Term& result)
  // Solver::getInterpolantNext(Term& result)
  auto a_get_interpol = fsm->new_action<Cvc5ActionGetInterpolant>();
  s_check_sat->add_action(a_get_interpol, 2);

  // Solver::getAbduct(const Term& term, Term& result)
  // Solver::getAbductNext(Term& result)
  auto a_get_abduct = fsm->new_action<Cvc5ActionGetAbduct>();
  s_check_sat->add_action(a_get_abduct, 2);

  // Solver::getDifficulty()
  auto a_get_diff = fsm->new_action<Cvc5ActionGetDifficulty>();
  s_sat->add_action(a_get_diff, 2);
  s_unsat->add_action(a_get_diff, 2);
}
/* -------------------------------------------------------------------------- */

void
Cvc5Solver::configure_options(SolverManager* smgr) const
{
  using namespace ::cvc5;

  ::cvc5::Solver slv;

  for (const auto& option : slv.getOptionNames())
  {
    auto info = slv.getOptionInfo(option);
    if (std::holds_alternative<OptionInfo::ValueInfo<bool>>(info.valueInfo))
    {
      smgr->add_option(new SolverOptionBool(option, info.boolValue()));
    }
    else if (std::holds_alternative<OptionInfo::NumberInfo<int64_t>>(
                 info.valueInfo))
    {
      auto num_info = std::get<OptionInfo::NumberInfo<int64_t>>(info.valueInfo);
      smgr->add_option(new SolverOptionNum<int64_t>(
          option,
          num_info.minimum.value_or(std::numeric_limits<int64_t>::min()),
          num_info.maximum.value_or(std::numeric_limits<int64_t>::max()),
          info.intValue()));
    }
    else if (std::holds_alternative<OptionInfo::NumberInfo<uint64_t>>(
                 info.valueInfo))
    {
      auto num_info =
          std::get<OptionInfo::NumberInfo<uint64_t>>(info.valueInfo);
      smgr->add_option(new SolverOptionNum<uint64_t>(
          option,
          num_info.minimum.value_or(std::numeric_limits<uint64_t>::min()),
          num_info.maximum.value_or(std::numeric_limits<uint64_t>::max()),
          info.uintValue()));
    }
    else if (std::holds_alternative<OptionInfo::ModeInfo>(info.valueInfo))
    {
      auto mode_info = std::get<OptionInfo::ModeInfo>(info.valueInfo);
      smgr->add_option(new SolverOptionList(
          option, mode_info.modes, mode_info.defaultValue));
    }
    else if (std::holds_alternative<OptionInfo::NumberInfo<double>>(
                 info.valueInfo))
    {
      auto num_info = std::get<OptionInfo::NumberInfo<double>>(info.valueInfo);
      smgr->add_option(new SolverOptionNum<double>(
          option,
          num_info.minimum.value_or(std::numeric_limits<double>::min()),
          num_info.maximum.value_or(std::numeric_limits<double>::max()),
          info.doubleValue()));
    }
  }
}

}  // namespace cvc5
}  // namespace murxla

#endif
