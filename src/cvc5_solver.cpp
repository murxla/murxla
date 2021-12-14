#ifdef MURXLA_USE_CVC5

#include "cvc5_solver.hpp"

#include <cassert>

#include "action.hpp"
#include "config.hpp"
#include "except.hpp"
#include "solver_option.hpp"
#include "theory.hpp"

namespace murxla {
namespace cvc5 {

#define MURXLA_CVC5_MAX_N_TERMS_CHECK_ENTAILED 5

/* -------------------------------------------------------------------------- */
/* Cvc5Sort                                                                   */
/* -------------------------------------------------------------------------- */

::cvc5::api::Sort&
Cvc5Sort::get_cvc5_sort(Sort sort)
{
  return static_cast<Cvc5Sort*>(sort.get())->d_sort;
}

size_t
Cvc5Sort::hash() const
{
  return std::hash<::cvc5::api::Sort>{}(d_sort);
}

bool
Cvc5Sort::equals(const Sort& other) const
{
  Cvc5Sort* cvc5_sort = dynamic_cast<Cvc5Sort*>(other.get());
  if (cvc5_sort)
  {
    return d_sort == cvc5_sort->d_sort;
  }
  return false;
}

bool
Cvc5Sort::not_equals(const Sort& other) const
{
  Cvc5Sort* cvc5_sort = dynamic_cast<Cvc5Sort*>(other.get());
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
  return d_sort.isParametricDatatype();
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
  return d_sort.getDatatype().getNumConstructors();
}

std::vector<std::string>
Cvc5Sort::get_dt_cons_names() const
{
  assert(is_dt());
  std::vector<std::string> res;
  ::cvc5::api::Datatype cvc5_dt = d_sort.getDatatype();
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
  ::cvc5::api::DatatypeConstructor cvc5_cons =
      d_sort.getDatatype().getConstructor(name);
  return cvc5_cons.getNumSelectors();
}

std::vector<std::string>
Cvc5Sort::get_dt_cons_sel_names(const std::string& name) const
{
  assert(is_dt());
  std::vector<std::string> res;
  ::cvc5::api::DatatypeConstructor cvc5_cons =
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
  ::cvc5::api::Sort cvc5_res = d_sort.getArrayIndexSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

Sort
Cvc5Sort::get_array_element_sort() const
{
  assert(is_array());
  ::cvc5::api::Sort cvc5_res = d_sort.getArrayElementSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

Sort
Cvc5Sort::get_bag_element_sort() const
{
  ::cvc5::api::Sort cvc5_res = d_sort.getBagElementSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

uint32_t
Cvc5Sort::get_fun_arity() const
{
  assert(is_fun());
  return d_sort.getFunctionArity();
}

Sort
Cvc5Sort::get_fun_codomain_sort() const
{
  assert(is_fun());
  ::cvc5::api::Sort cvc5_res = d_sort.getFunctionCodomainSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

std::vector<Sort>
Cvc5Sort::get_fun_domain_sorts() const
{
  assert(is_fun());
  std::vector<::cvc5::api::Sort> cvc5_res = d_sort.getFunctionDomainSorts();
  return cvc5_sorts_to_sorts(d_solver, cvc5_res);
}

Sort
Cvc5Sort::get_seq_element_sort() const
{
  ::cvc5::api::Sort cvc5_res = d_sort.getSequenceElementSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

Sort
Cvc5Sort::get_set_element_sort() const
{
  ::cvc5::api::Sort cvc5_res = d_sort.getSetElementSort();
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_solver, cvc5_res));
  MURXLA_TEST(res);
  return res;
}

std::vector<::cvc5::api::Sort>
Cvc5Sort::sorts_to_cvc5_sorts(const std::vector<Sort>& sorts)
{
  std::vector<::cvc5::api::Sort> res;
  for (auto& s : sorts)
  {
    res.emplace_back(get_cvc5_sort(s));
  }
  return res;
}

std::vector<Sort>
Cvc5Sort::cvc5_sorts_to_sorts(::cvc5::api::Solver* cvc5,
                              const std::vector<::cvc5::api::Sort>& sorts)
{
  std::vector<Sort> res;
  for (auto& s : sorts)
  {
    res.emplace_back(new Cvc5Sort(cvc5, s));
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Term                                                                   */
/* -------------------------------------------------------------------------- */

// ##### TODO OPS

//  ABSTRACT_VALUE,
//  LAMBDA,
//  WITNESS,
//  CARDINALITY_CONSTRAINT,
//  CARDINALITY_VALUE,
//  HO_APPLY,

//  ## Arithmetic
//  POW,
//  EXPONENTIAL,
//  TO_INTEGER,
//  TO_REAL,

// ## Arithmetic transcendental
//  SINE,
//  COSINE,
//  TANGENT,
//  COSECANT,
//  SECANT,
//  COTANGENT,
//  ARCSINE,
//  ARCCOSINE,
//  ARCTANGENT,
//  ARCCOSECANT,
//  ARCSECANT,
//  ARCCOTANGENT,
//  SQRT,

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

std::unordered_map<Op::Kind, ::cvc5::api::Kind>
    Cvc5Term::s_kinds_to_cvc5_kinds = {
        /* Special Cases */
        {Op::UNDEFINED, ::cvc5::api::Kind::UNDEFINED_KIND},
        {Op::DISTINCT, ::cvc5::api::Kind::DISTINCT},
        {Op::EQUAL, ::cvc5::api::Kind::EQUAL},
        {Op::ITE, ::cvc5::api::Kind::ITE},

        /* Bool */
        {Op::AND, ::cvc5::api::Kind::AND},
        {Op::OR, ::cvc5::api::Kind::OR},
        {Op::NOT, ::cvc5::api::Kind::NOT},
        {Op::XOR, ::cvc5::api::Kind::XOR},
        {Op::IMPLIES, ::cvc5::api::Kind::IMPLIES},

        /* Arrays */
        {Op::ARRAY_SELECT, ::cvc5::api::Kind::SELECT},
        {Op::ARRAY_STORE, ::cvc5::api::Kind::STORE},

        /* BV */
        {Op::BV_EXTRACT, ::cvc5::api::Kind::BITVECTOR_EXTRACT},
        {Op::BV_REPEAT, ::cvc5::api::Kind::BITVECTOR_REPEAT},
        {Op::BV_ROTATE_LEFT, ::cvc5::api::Kind::BITVECTOR_ROTATE_LEFT},
        {Op::BV_ROTATE_RIGHT, ::cvc5::api::Kind::BITVECTOR_ROTATE_RIGHT},
        {Op::BV_SIGN_EXTEND, ::cvc5::api::Kind::BITVECTOR_SIGN_EXTEND},
        {Op::BV_ZERO_EXTEND, ::cvc5::api::Kind::BITVECTOR_ZERO_EXTEND},

        {Op::BV_CONCAT, ::cvc5::api::Kind::BITVECTOR_CONCAT},
        {Op::BV_AND, ::cvc5::api::Kind::BITVECTOR_AND},
        {Op::BV_OR, ::cvc5::api::Kind::BITVECTOR_OR},
        {Op::BV_XOR, ::cvc5::api::Kind::BITVECTOR_XOR},
        {Op::BV_MULT, ::cvc5::api::Kind::BITVECTOR_MULT},
        {Op::BV_ADD, ::cvc5::api::Kind::BITVECTOR_ADD},
        {Op::BV_NOT, ::cvc5::api::Kind::BITVECTOR_NOT},
        {Op::BV_NEG, ::cvc5::api::Kind::BITVECTOR_NEG},
        {Op::BV_NAND, ::cvc5::api::Kind::BITVECTOR_NAND},
        {Op::BV_NOR, ::cvc5::api::Kind::BITVECTOR_NOR},
        {Op::BV_XNOR, ::cvc5::api::Kind::BITVECTOR_XNOR},
        {Op::BV_COMP, ::cvc5::api::Kind::BITVECTOR_COMP},
        {Op::BV_SUB, ::cvc5::api::Kind::BITVECTOR_SUB},
        {Op::BV_UDIV, ::cvc5::api::Kind::BITVECTOR_UDIV},
        {Op::BV_UREM, ::cvc5::api::Kind::BITVECTOR_UREM},
        {Op::BV_UREM, ::cvc5::api::Kind::BITVECTOR_UREM},
        {Op::BV_SDIV, ::cvc5::api::Kind::BITVECTOR_SDIV},
        {Op::BV_SREM, ::cvc5::api::Kind::BITVECTOR_SREM},
        {Op::BV_SMOD, ::cvc5::api::Kind::BITVECTOR_SMOD},
        {Op::BV_SHL, ::cvc5::api::Kind::BITVECTOR_SHL},
        {Op::BV_LSHR, ::cvc5::api::Kind::BITVECTOR_LSHR},
        {Op::BV_ASHR, ::cvc5::api::Kind::BITVECTOR_ASHR},
        {Op::BV_ULT, ::cvc5::api::Kind::BITVECTOR_ULT},
        {Op::BV_ULE, ::cvc5::api::Kind::BITVECTOR_ULE},
        {Op::BV_UGT, ::cvc5::api::Kind::BITVECTOR_UGT},
        {Op::BV_UGE, ::cvc5::api::Kind::BITVECTOR_UGE},
        {Op::BV_SLT, ::cvc5::api::Kind::BITVECTOR_SLT},
        {Op::BV_SLE, ::cvc5::api::Kind::BITVECTOR_SLE},
        {Op::BV_SGT, ::cvc5::api::Kind::BITVECTOR_SGT},
        {Op::BV_SGE, ::cvc5::api::Kind::BITVECTOR_SGE},

        /* Datatypes */
        {Op::DT_APPLY_CONS, ::cvc5::api::Kind::APPLY_CONSTRUCTOR},
        {Op::DT_APPLY_SEL, ::cvc5::api::Kind::APPLY_SELECTOR},
        {Op::DT_APPLY_TESTER, ::cvc5::api::Kind::APPLY_TESTER},
        {Op::DT_APPLY_UPDATER, ::cvc5::api::Kind::APPLY_UPDATER},
        {Op::DT_MATCH, ::cvc5::api::Kind::MATCH},
        {Op::DT_MATCH_BIND_CASE, ::cvc5::api::Kind::MATCH_BIND_CASE},
        {Op::DT_MATCH_CASE, ::cvc5::api::Kind::MATCH_CASE},

        /* FP */
        {Op::FP_ABS, ::cvc5::api::Kind::FLOATINGPOINT_ABS},
        {Op::FP_ADD, ::cvc5::api::Kind::FLOATINGPOINT_ADD},
        {Op::FP_DIV, ::cvc5::api::Kind::FLOATINGPOINT_DIV},
        {Op::FP_EQ, ::cvc5::api::Kind::FLOATINGPOINT_EQ},
        {Op::FP_FMA, ::cvc5::api::Kind::FLOATINGPOINT_FMA},
        {Op::FP_FP, ::cvc5::api::Kind::FLOATINGPOINT_FP},
        {Op::FP_IS_NORMAL, ::cvc5::api::Kind::FLOATINGPOINT_ISN},
        {Op::FP_IS_SUBNORMAL, ::cvc5::api::Kind::FLOATINGPOINT_ISSN},
        {Op::FP_IS_INF, ::cvc5::api::Kind::FLOATINGPOINT_ISINF},
        {Op::FP_IS_NAN, ::cvc5::api::Kind::FLOATINGPOINT_ISNAN},
        {Op::FP_IS_NEG, ::cvc5::api::Kind::FLOATINGPOINT_ISNEG},
        {Op::FP_IS_POS, ::cvc5::api::Kind::FLOATINGPOINT_ISPOS},
        {Op::FP_IS_ZERO, ::cvc5::api::Kind::FLOATINGPOINT_ISZ},
        {Op::FP_LT, ::cvc5::api::Kind::FLOATINGPOINT_LT},
        {Op::FP_LEQ, ::cvc5::api::Kind::FLOATINGPOINT_LEQ},
        {Op::FP_GT, ::cvc5::api::Kind::FLOATINGPOINT_GT},
        {Op::FP_GEQ, ::cvc5::api::Kind::FLOATINGPOINT_GEQ},
        {Op::FP_MAX, ::cvc5::api::Kind::FLOATINGPOINT_MAX},
        {Op::FP_MIN, ::cvc5::api::Kind::FLOATINGPOINT_MIN},
        {Op::FP_MUL, ::cvc5::api::Kind::FLOATINGPOINT_MULT},
        {Op::FP_NEG, ::cvc5::api::Kind::FLOATINGPOINT_NEG},
        {Op::FP_REM, ::cvc5::api::Kind::FLOATINGPOINT_REM},
        {Op::FP_RTI, ::cvc5::api::Kind::FLOATINGPOINT_RTI},
        {Op::FP_SQRT, ::cvc5::api::Kind::FLOATINGPOINT_SQRT},
        {Op::FP_SUB, ::cvc5::api::Kind::FLOATINGPOINT_SUB},
        {Op::FP_TO_FP_FROM_BV,
         ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR},
        {Op::FP_TO_FP_FROM_SBV,
         ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
        {Op::FP_TO_FP_FROM_FP,
         ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT},
        {Op::FP_TO_FP_FROM_UBV,
         ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
        {Op::FP_TO_FP_FROM_REAL, ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_REAL},
        {Op::FP_TO_REAL, ::cvc5::api::Kind::FLOATINGPOINT_TO_REAL},
        {Op::FP_TO_SBV, ::cvc5::api::Kind::FLOATINGPOINT_TO_SBV},
        {Op::FP_TO_UBV, ::cvc5::api::Kind::FLOATINGPOINT_TO_UBV},

        /* Ints */
        {Op::INT_IS_DIV, ::cvc5::api::Kind::DIVISIBLE},
        {Op::INT_NEG, ::cvc5::api::Kind::UMINUS},
        {Op::INT_SUB, ::cvc5::api::Kind::MINUS},
        {Op::INT_ADD, ::cvc5::api::Kind::PLUS},
        {Op::INT_MUL, ::cvc5::api::Kind::MULT},
        {Op::INT_DIV, ::cvc5::api::Kind::INTS_DIVISION},
        {Op::INT_MOD, ::cvc5::api::Kind::INTS_MODULUS},
        {Op::INT_ABS, ::cvc5::api::Kind::ABS},
        {Op::INT_LT, ::cvc5::api::Kind::LT},
        {Op::INT_LTE, ::cvc5::api::Kind::LEQ},
        {Op::INT_GT, ::cvc5::api::Kind::GT},
        {Op::INT_GTE, ::cvc5::api::Kind::GEQ},
        {Op::INT_IS_INT, ::cvc5::api::Kind::IS_INTEGER},

        /* Reals */
        {Op::REAL_NEG, ::cvc5::api::Kind::UMINUS},
        {Op::REAL_SUB, ::cvc5::api::Kind::MINUS},
        {Op::REAL_ADD, ::cvc5::api::Kind::PLUS},
        {Op::REAL_MUL, ::cvc5::api::Kind::MULT},
        {Op::REAL_DIV, ::cvc5::api::Kind::DIVISION},
        {Op::REAL_LT, ::cvc5::api::Kind::LT},
        {Op::REAL_LTE, ::cvc5::api::Kind::LEQ},
        {Op::REAL_GT, ::cvc5::api::Kind::GT},
        {Op::REAL_GTE, ::cvc5::api::Kind::GEQ},
        {Op::REAL_IS_INT, ::cvc5::api::Kind::IS_INTEGER},

        /* Quantifiers */
        {Op::FORALL, ::cvc5::api::Kind::FORALL},
        {Op::EXISTS, ::cvc5::api::Kind::EXISTS},

        /* Strings */
        {Op::STR_CONCAT, ::cvc5::api::Kind::STRING_CONCAT},
        {Op::STR_LEN, ::cvc5::api::Kind::STRING_LENGTH},
        {Op::STR_LT, ::cvc5::api::Kind::STRING_LT},
        {Op::STR_TO_RE, ::cvc5::api::Kind::STRING_TO_REGEXP},
        {Op::STR_IN_RE, ::cvc5::api::Kind::STRING_IN_REGEXP},
        {Op::STR_LE, ::cvc5::api::Kind::STRING_LEQ},
        {Op::STR_AT, ::cvc5::api::Kind::STRING_CHARAT},
        {Op::STR_SUBSTR, ::cvc5::api::Kind::STRING_SUBSTR},
        {Op::STR_PREFIXOF, ::cvc5::api::Kind::STRING_PREFIX},
        {Op::STR_SUFFIXOF, ::cvc5::api::Kind::STRING_SUFFIX},
        {Op::STR_CONTAINS, ::cvc5::api::Kind::STRING_CONTAINS},
        {Op::STR_INDEXOF, ::cvc5::api::Kind::STRING_INDEXOF},
        {Op::STR_REPLACE, ::cvc5::api::Kind::STRING_REPLACE},
        {Op::STR_REPLACE_ALL, ::cvc5::api::Kind::STRING_REPLACE_ALL},
        {Op::STR_REPLACE_RE, ::cvc5::api::Kind::STRING_REPLACE_RE},
        {Op::STR_REPLACE_RE_ALL, ::cvc5::api::Kind::STRING_REPLACE_RE_ALL},
        {Op::STR_IS_DIGIT, ::cvc5::api::Kind::STRING_IS_DIGIT},
        {Op::STR_TO_CODE, ::cvc5::api::Kind::STRING_TO_CODE},
        {Op::STR_FROM_CODE, ::cvc5::api::Kind::STRING_FROM_CODE},
        {Op::STR_TO_INT, ::cvc5::api::Kind::STRING_TO_INT},
        {Op::STR_FROM_INT, ::cvc5::api::Kind::STRING_FROM_INT},
        {Op::RE_ALL, ::cvc5::api::Kind::REGEXP_STAR},
        {Op::RE_ALLCHAR, ::cvc5::api::Kind::REGEXP_ALLCHAR},
        {Op::RE_COMP, ::cvc5::api::Kind::REGEXP_COMPLEMENT},
        {Op::RE_CONCAT, ::cvc5::api::Kind::REGEXP_CONCAT},
        {Op::RE_DIFF, ::cvc5::api::Kind::REGEXP_DIFF},
        {Op::RE_INTER, ::cvc5::api::Kind::REGEXP_INTER},
        {Op::RE_LOOP, ::cvc5::api::Kind::REGEXP_LOOP},
        {Op::RE_NONE, ::cvc5::api::Kind::REGEXP_NONE},
        {Op::RE_OPT, ::cvc5::api::Kind::REGEXP_OPT},
        {Op::RE_PLUS, ::cvc5::api::Kind::REGEXP_PLUS},
        {Op::RE_POW, ::cvc5::api::Kind::REGEXP_REPEAT},
        {Op::RE_RANGE, ::cvc5::api::Kind::REGEXP_RANGE},
        {Op::RE_STAR, ::cvc5::api::Kind::REGEXP_STAR},
        {Op::RE_UNION, ::cvc5::api::Kind::REGEXP_UNION},

        /* UF */
        {Op::UF_APPLY, ::cvc5::api::Kind::APPLY_UF},

        /* Non-standardized theories */
        // Bag
        {Op::BAG_UNION_MAX, ::cvc5::api::Kind::BAG_UNION_MAX},
        {Op::BAG_UNION_DISJOINT, ::cvc5::api::Kind::BAG_UNION_DISJOINT},
        {Op::BAG_INTERSECTION_MIN, ::cvc5::api::Kind::BAG_INTER_MIN},
        {Op::BAG_DIFFERENCE_SUBTRACT,
         ::cvc5::api::Kind::BAG_DIFFERENCE_SUBTRACT},
        {Op::BAG_DIFFERENCE_REMOVE, ::cvc5::api::Kind::BAG_DIFFERENCE_REMOVE},
        {Op::BAG_SUBBAG, ::cvc5::api::Kind::BAG_SUBBAG},
        {Op::BAG_COUNT, ::cvc5::api::Kind::BAG_COUNT},
        {Op::BAG_DUPLICATE_REMOVAL, ::cvc5::api::Kind::BAG_DUPLICATE_REMOVAL},
        {Op::BAG_MAKE, ::cvc5::api::Kind::BAG_MAKE},
        {Op::BAG_CARD, ::cvc5::api::Kind::BAG_CARD},
        {Op::BAG_CHOOSE, ::cvc5::api::Kind::BAG_CHOOSE},
        {Op::BAG_IS_SINGLETON, ::cvc5::api::Kind::BAG_IS_SINGLETON},
        {Op::BAG_FROM_SET, ::cvc5::api::Kind::BAG_FROM_SET},
        {Op::BAG_TO_SET, ::cvc5::api::Kind::BAG_TO_SET},
        {Op::BAG_MAP, ::cvc5::api::Kind::BAG_MAP},
        // Sequences
        {Op::SEQ_CONCAT, ::cvc5::api::Kind::SEQ_CONCAT},
        {Op::SEQ_LENGTH, ::cvc5::api::Kind::SEQ_LENGTH},
        {Op::SEQ_EXTRACT, ::cvc5::api::Kind::SEQ_EXTRACT},
        {Op::SEQ_UPDATE, ::cvc5::api::Kind::SEQ_UPDATE},
        {Op::SEQ_AT, ::cvc5::api::Kind::SEQ_AT},
        {Op::SEQ_CONTAINS, ::cvc5::api::Kind::SEQ_CONTAINS},
        {Op::SEQ_INDEXOF, ::cvc5::api::Kind::SEQ_INDEXOF},
        {Op::SEQ_REPLACE, ::cvc5::api::Kind::SEQ_REPLACE},
        {Op::SEQ_REPLACE_ALL, ::cvc5::api::Kind::SEQ_REPLACE_ALL},
        {Op::SEQ_REV, ::cvc5::api::Kind::SEQ_REV},
        {Op::SEQ_PREFIX, ::cvc5::api::Kind::SEQ_PREFIX},
        {Op::SEQ_SUFFIX, ::cvc5::api::Kind::SEQ_SUFFIX},
        {Op::SEQ_UNIT, ::cvc5::api::Kind::SEQ_UNIT},
        {Op::SEQ_NTH, ::cvc5::api::Kind::SEQ_NTH},
        // Sets
        {Op::SET_CARD, ::cvc5::api::Kind::SET_CARD},
        {Op::SET_COMPLEMENT, ::cvc5::api::Kind::SET_COMPLEMENT},
        {Op::SET_COMPREHENSION, ::cvc5::api::Kind::SET_COMPREHENSION},
        {Op::SET_CHOOSE, ::cvc5::api::Kind::SET_CHOOSE},
        {Op::SET_INTERSECTION, ::cvc5::api::Kind::SET_INTER},
        {Op::SET_INSERT, ::cvc5::api::Kind::SET_INSERT},
        {Op::SET_IS_SINGLETON, ::cvc5::api::Kind::SET_IS_SINGLETON},
        {Op::SET_UNION, ::cvc5::api::Kind::SET_UNION},
        {Op::SET_MEMBER, ::cvc5::api::Kind::SET_MEMBER},
        {Op::SET_MINUS, ::cvc5::api::Kind::SET_MINUS},
        {Op::SET_SINGLETON, ::cvc5::api::Kind::SET_SINGLETON},
        {Op::SET_SUBSET, ::cvc5::api::Kind::SET_SUBSET},
        {Op::REL_JOIN, ::cvc5::api::Kind::RELATION_JOIN},
        {Op::REL_JOIN_IMAGE, ::cvc5::api::Kind::RELATION_JOIN_IMAGE},
        {Op::REL_IDEN, ::cvc5::api::Kind::RELATION_IDEN},
        {Op::REL_PRODUCT, ::cvc5::api::Kind::RELATION_PRODUCT},
        {Op::REL_TCLOSURE, ::cvc5::api::Kind::RELATION_TCLOSURE},
        {Op::REL_TRANSPOSE, ::cvc5::api::Kind::RELATION_TRANSPOSE},

        /* Solver-specific operators */
        // BV
        {OP_BV_REDOR, ::cvc5::api::Kind::BITVECTOR_REDOR},
        {OP_BV_REDAND, ::cvc5::api::Kind::BITVECTOR_REDAND},
        {OP_BV_ULTBV, ::cvc5::api::Kind::BITVECTOR_ULTBV},
        {OP_BV_SLTBV, ::cvc5::api::Kind::BITVECTOR_SLTBV},
        {OP_BV_ITE, ::cvc5::api::Kind::BITVECTOR_ITE},
        // Datatypes
        {OP_DT_SIZE, ::cvc5::api::Kind::DT_SIZE},
        // Int
        {OP_BV_TO_NAT, ::cvc5::api::Kind::BITVECTOR_TO_NAT},
        {OP_INT_IAND, ::cvc5::api::Kind::IAND},
        {OP_INT_TO_BV, ::cvc5::api::Kind::INT_TO_BITVECTOR},
        {OP_INT_POW2, ::cvc5::api::Kind::POW2},
        // Real
        {OP_REAL_PI, ::cvc5::api::Kind::PI},
        // Strings
        {OP_STRING_UPDATE, ::cvc5::api::Kind::STRING_UPDATE},
        {OP_STRING_TOLOWER, ::cvc5::api::Kind::STRING_TOLOWER},
        {OP_STRING_TOUPPER, ::cvc5::api::Kind::STRING_TOUPPER},
        {OP_STRING_REV, ::cvc5::api::Kind::STRING_REV},
};

std::unordered_map<::cvc5::api::Kind, Op::Kind>
    Cvc5Term::s_cvc5_kinds_to_kinds = {
        {::cvc5::api::Kind::INTERNAL_KIND, Op::INTERNAL},
        /* Leaf Kinds */
        {::cvc5::api::Kind::CONSTANT, Op::CONSTANT},
        {::cvc5::api::Kind::CONST_ARRAY, Op::CONST_ARRAY},
        {::cvc5::api::Kind::CONST_BOOLEAN, Op::VALUE},
        {::cvc5::api::Kind::CONST_BITVECTOR, Op::VALUE},
        {::cvc5::api::Kind::CONST_FLOATINGPOINT, Op::VALUE},
        {::cvc5::api::Kind::CONST_RATIONAL, Op::VALUE},
        {::cvc5::api::Kind::CONST_ROUNDINGMODE, Op::VALUE},
        {::cvc5::api::Kind::CONST_SEQUENCE, Op::VALUE},
        {::cvc5::api::Kind::CONST_STRING, Op::VALUE},
        {::cvc5::api::Kind::VARIABLE, Op::VARIABLE},

        /* Special Cases */
        {::cvc5::api::Kind::UNDEFINED_KIND, Op::UNDEFINED},
        {::cvc5::api::Kind::DISTINCT, Op::DISTINCT},
        {::cvc5::api::Kind::EQUAL, Op::EQUAL},
        {::cvc5::api::Kind::ITE, Op::ITE},

        /* Bool */
        {::cvc5::api::Kind::AND, Op::AND},
        {::cvc5::api::Kind::OR, Op::OR},
        {::cvc5::api::Kind::NOT, Op::NOT},
        {::cvc5::api::Kind::XOR, Op::XOR},
        {::cvc5::api::Kind::IMPLIES, Op::IMPLIES},

        /* Arrays */
        {::cvc5::api::Kind::SELECT, Op::ARRAY_SELECT},
        {::cvc5::api::Kind::STORE, Op::ARRAY_STORE},

        /* BV */
        {::cvc5::api::Kind::BITVECTOR_EXTRACT, Op::BV_EXTRACT},
        {::cvc5::api::Kind::BITVECTOR_REPEAT, Op::BV_REPEAT},
        {::cvc5::api::Kind::BITVECTOR_ROTATE_LEFT, Op::BV_ROTATE_LEFT},
        {::cvc5::api::Kind::BITVECTOR_ROTATE_RIGHT, Op::BV_ROTATE_RIGHT},
        {::cvc5::api::Kind::BITVECTOR_SIGN_EXTEND, Op::BV_SIGN_EXTEND},
        {::cvc5::api::Kind::BITVECTOR_ZERO_EXTEND, Op::BV_ZERO_EXTEND},

        {::cvc5::api::Kind::BITVECTOR_CONCAT, Op::BV_CONCAT},
        {::cvc5::api::Kind::BITVECTOR_AND, Op::BV_AND},
        {::cvc5::api::Kind::BITVECTOR_OR, Op::BV_OR},
        {::cvc5::api::Kind::BITVECTOR_XOR, Op::BV_XOR},
        {::cvc5::api::Kind::BITVECTOR_MULT, Op::BV_MULT},
        {::cvc5::api::Kind::BITVECTOR_ADD, Op::BV_ADD},
        {::cvc5::api::Kind::BITVECTOR_NOT, Op::BV_NOT},
        {::cvc5::api::Kind::BITVECTOR_NEG, Op::BV_NEG},
        {::cvc5::api::Kind::BITVECTOR_NAND, Op::BV_NAND},
        {::cvc5::api::Kind::BITVECTOR_NOR, Op::BV_NOR},
        {::cvc5::api::Kind::BITVECTOR_XNOR, Op::BV_XNOR},
        {::cvc5::api::Kind::BITVECTOR_COMP, Op::BV_COMP},
        {::cvc5::api::Kind::BITVECTOR_SUB, Op::BV_SUB},
        {::cvc5::api::Kind::BITVECTOR_UDIV, Op::BV_UDIV},
        {::cvc5::api::Kind::BITVECTOR_UREM, Op::BV_UREM},
        {::cvc5::api::Kind::BITVECTOR_UREM, Op::BV_UREM},
        {::cvc5::api::Kind::BITVECTOR_SDIV, Op::BV_SDIV},
        {::cvc5::api::Kind::BITVECTOR_SREM, Op::BV_SREM},
        {::cvc5::api::Kind::BITVECTOR_SMOD, Op::BV_SMOD},
        {::cvc5::api::Kind::BITVECTOR_SHL, Op::BV_SHL},
        {::cvc5::api::Kind::BITVECTOR_LSHR, Op::BV_LSHR},
        {::cvc5::api::Kind::BITVECTOR_ASHR, Op::BV_ASHR},
        {::cvc5::api::Kind::BITVECTOR_ULT, Op::BV_ULT},
        {::cvc5::api::Kind::BITVECTOR_ULE, Op::BV_ULE},
        {::cvc5::api::Kind::BITVECTOR_UGT, Op::BV_UGT},
        {::cvc5::api::Kind::BITVECTOR_UGE, Op::BV_UGE},
        {::cvc5::api::Kind::BITVECTOR_SLT, Op::BV_SLT},
        {::cvc5::api::Kind::BITVECTOR_SLE, Op::BV_SLE},
        {::cvc5::api::Kind::BITVECTOR_SGT, Op::BV_SGT},
        {::cvc5::api::Kind::BITVECTOR_SGE, Op::BV_SGE},

        /* Datatypes */
        {::cvc5::api::Kind::APPLY_CONSTRUCTOR, Op::DT_APPLY_CONS},
        {::cvc5::api::Kind::APPLY_SELECTOR, Op::DT_APPLY_SEL},
        {::cvc5::api::Kind::APPLY_TESTER, Op::DT_APPLY_TESTER},
        {::cvc5::api::Kind::APPLY_UPDATER, Op::DT_APPLY_UPDATER},
        {::cvc5::api::Kind::MATCH, Op::DT_MATCH},
        {::cvc5::api::Kind::MATCH_BIND_CASE, Op::DT_MATCH_BIND_CASE},
        {::cvc5::api::Kind::MATCH_CASE, Op::DT_MATCH_CASE},

        /* FP */
        {::cvc5::api::Kind::FLOATINGPOINT_ABS, Op::FP_ABS},
        {::cvc5::api::Kind::FLOATINGPOINT_ADD, Op::FP_ADD},
        {::cvc5::api::Kind::FLOATINGPOINT_DIV, Op::FP_DIV},
        {::cvc5::api::Kind::FLOATINGPOINT_EQ, Op::FP_EQ},
        {::cvc5::api::Kind::FLOATINGPOINT_FMA, Op::FP_FMA},
        {::cvc5::api::Kind::FLOATINGPOINT_FP, Op::FP_FP},
        {::cvc5::api::Kind::FLOATINGPOINT_ISN, Op::FP_IS_NORMAL},
        {::cvc5::api::Kind::FLOATINGPOINT_ISSN, Op::FP_IS_SUBNORMAL},
        {::cvc5::api::Kind::FLOATINGPOINT_ISINF, Op::FP_IS_INF},
        {::cvc5::api::Kind::FLOATINGPOINT_ISNAN, Op::FP_IS_NAN},
        {::cvc5::api::Kind::FLOATINGPOINT_ISNEG, Op::FP_IS_NEG},
        {::cvc5::api::Kind::FLOATINGPOINT_ISPOS, Op::FP_IS_POS},
        {::cvc5::api::Kind::FLOATINGPOINT_ISZ, Op::FP_IS_ZERO},
        {::cvc5::api::Kind::FLOATINGPOINT_LT, Op::FP_LT},
        {::cvc5::api::Kind::FLOATINGPOINT_LEQ, Op::FP_LEQ},
        {::cvc5::api::Kind::FLOATINGPOINT_GT, Op::FP_GT},
        {::cvc5::api::Kind::FLOATINGPOINT_GEQ, Op::FP_GEQ},
        {::cvc5::api::Kind::FLOATINGPOINT_MAX, Op::FP_MAX},
        {::cvc5::api::Kind::FLOATINGPOINT_MIN, Op::FP_MIN},
        {::cvc5::api::Kind::FLOATINGPOINT_MULT, Op::FP_MUL},
        {::cvc5::api::Kind::FLOATINGPOINT_NEG, Op::FP_NEG},
        {::cvc5::api::Kind::FLOATINGPOINT_REM, Op::FP_REM},
        {::cvc5::api::Kind::FLOATINGPOINT_RTI, Op::FP_RTI},
        {::cvc5::api::Kind::FLOATINGPOINT_SQRT, Op::FP_SQRT},
        {::cvc5::api::Kind::FLOATINGPOINT_SUB, Op::FP_SUB},
        {::cvc5::api::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
         Op::FP_TO_FP_FROM_BV},
        {::cvc5::api::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
         Op::FP_TO_FP_FROM_SBV},
        {::cvc5::api::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT,
         Op::FP_TO_FP_FROM_FP},
        {::cvc5::api::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
         Op::FP_TO_FP_FROM_UBV},
        {::cvc5::api::Kind::FLOATINGPOINT_TO_FP_REAL, Op::FP_TO_FP_FROM_REAL},
        {::cvc5::api::Kind::FLOATINGPOINT_TO_FP_GENERIC, Op::INTERNAL},
        {::cvc5::api::Kind::FLOATINGPOINT_TO_REAL, Op::FP_TO_REAL},
        {::cvc5::api::Kind::FLOATINGPOINT_TO_SBV, Op::FP_TO_SBV},
        {::cvc5::api::Kind::FLOATINGPOINT_TO_UBV, Op::FP_TO_UBV},

        /* Ints */
        {::cvc5::api::Kind::DIVISIBLE, Op::INT_IS_DIV},
        {::cvc5::api::Kind::UMINUS, Op::INT_NEG},
        {::cvc5::api::Kind::MINUS, Op::INT_SUB},
        {::cvc5::api::Kind::PLUS, Op::INT_ADD},
        {::cvc5::api::Kind::MULT, Op::INT_MUL},
        {::cvc5::api::Kind::INTS_DIVISION, Op::INT_DIV},
        {::cvc5::api::Kind::INTS_MODULUS, Op::INT_MOD},
        {::cvc5::api::Kind::ABS, Op::INT_ABS},
        {::cvc5::api::Kind::LT, Op::INT_LT},
        {::cvc5::api::Kind::LEQ, Op::INT_LTE},
        {::cvc5::api::Kind::GT, Op::INT_GT},
        {::cvc5::api::Kind::GEQ, Op::INT_GTE},
        {::cvc5::api::Kind::IS_INTEGER, Op::INT_IS_INT},

        /* Reals */
        {::cvc5::api::Kind::UMINUS, Op::REAL_NEG},
        {::cvc5::api::Kind::MINUS, Op::REAL_SUB},
        {::cvc5::api::Kind::PLUS, Op::REAL_ADD},
        {::cvc5::api::Kind::MULT, Op::REAL_MUL},
        {::cvc5::api::Kind::DIVISION, Op::REAL_DIV},
        {::cvc5::api::Kind::LT, Op::REAL_LT},
        {::cvc5::api::Kind::LEQ, Op::REAL_LTE},
        {::cvc5::api::Kind::GT, Op::REAL_GT},
        {::cvc5::api::Kind::GEQ, Op::REAL_GTE},
        {::cvc5::api::Kind::IS_INTEGER, Op::REAL_IS_INT},

        /* Quantifiers */
        {::cvc5::api::Kind::FORALL, Op::FORALL},
        {::cvc5::api::Kind::EXISTS, Op::EXISTS},

        /* Strings */
        {::cvc5::api::Kind::STRING_CONCAT, Op::STR_CONCAT},
        {::cvc5::api::Kind::STRING_LENGTH, Op::STR_LEN},
        {::cvc5::api::Kind::STRING_LT, Op::STR_LT},
        {::cvc5::api::Kind::STRING_TO_REGEXP, Op::STR_TO_RE},
        {::cvc5::api::Kind::STRING_IN_REGEXP, Op::STR_IN_RE},
        {::cvc5::api::Kind::STRING_LEQ, Op::STR_LE},
        {::cvc5::api::Kind::STRING_CHARAT, Op::STR_AT},
        {::cvc5::api::Kind::STRING_SUBSTR, Op::STR_SUBSTR},
        {::cvc5::api::Kind::STRING_PREFIX, Op::STR_PREFIXOF},
        {::cvc5::api::Kind::STRING_SUFFIX, Op::STR_SUFFIXOF},
        {::cvc5::api::Kind::STRING_CONTAINS, Op::STR_CONTAINS},
        {::cvc5::api::Kind::STRING_INDEXOF, Op::STR_INDEXOF},
        {::cvc5::api::Kind::STRING_REPLACE, Op::STR_REPLACE},
        {::cvc5::api::Kind::STRING_REPLACE_ALL, Op::STR_REPLACE_ALL},
        {::cvc5::api::Kind::STRING_REPLACE_RE, Op::STR_REPLACE_RE},
        {::cvc5::api::Kind::STRING_REPLACE_RE_ALL, Op::STR_REPLACE_RE_ALL},
        {::cvc5::api::Kind::STRING_IS_DIGIT, Op::STR_IS_DIGIT},
        {::cvc5::api::Kind::STRING_TO_CODE, Op::STR_TO_CODE},
        {::cvc5::api::Kind::STRING_FROM_CODE, Op::STR_FROM_CODE},
        {::cvc5::api::Kind::STRING_TO_INT, Op::STR_TO_INT},
        {::cvc5::api::Kind::STRING_FROM_INT, Op::STR_FROM_INT},
        {::cvc5::api::Kind::REGEXP_ALLCHAR, Op::RE_ALLCHAR},
        {::cvc5::api::Kind::REGEXP_COMPLEMENT, Op::RE_COMP},
        {::cvc5::api::Kind::REGEXP_CONCAT, Op::RE_CONCAT},
        {::cvc5::api::Kind::REGEXP_DIFF, Op::RE_DIFF},
        {::cvc5::api::Kind::REGEXP_INTER, Op::RE_INTER},
        {::cvc5::api::Kind::REGEXP_LOOP, Op::RE_LOOP},
        {::cvc5::api::Kind::REGEXP_NONE, Op::RE_NONE},
        {::cvc5::api::Kind::REGEXP_OPT, Op::RE_OPT},
        {::cvc5::api::Kind::REGEXP_PLUS, Op::RE_PLUS},
        {::cvc5::api::Kind::REGEXP_RANGE, Op::RE_RANGE},
        {::cvc5::api::Kind::REGEXP_REPEAT, Op::RE_POW},
        {::cvc5::api::Kind::REGEXP_STAR, Op::RE_STAR},
        {::cvc5::api::Kind::REGEXP_UNION, Op::RE_UNION},

        /* UF */
        {::cvc5::api::Kind::APPLY_UF, Op::UF_APPLY},

        /* Non-standardized theories */
        // Bag
        {::cvc5::api::Kind::BAG_UNION_MAX, Op::BAG_UNION_MAX},
        {::cvc5::api::Kind::BAG_UNION_DISJOINT, Op::BAG_UNION_DISJOINT},
        {::cvc5::api::Kind::BAG_INTER_MIN, Op::BAG_INTERSECTION_MIN},
        {::cvc5::api::Kind::BAG_DIFFERENCE_SUBTRACT,
         Op::BAG_DIFFERENCE_SUBTRACT},
        {::cvc5::api::Kind::BAG_DIFFERENCE_REMOVE, Op::BAG_DIFFERENCE_REMOVE},
        {::cvc5::api::Kind::BAG_SUBBAG, Op::BAG_SUBBAG},
        {::cvc5::api::Kind::BAG_COUNT, Op::BAG_COUNT},
        {::cvc5::api::Kind::BAG_DUPLICATE_REMOVAL, Op::BAG_DUPLICATE_REMOVAL},
        {::cvc5::api::Kind::BAG_MAKE, Op::BAG_MAKE},
        {::cvc5::api::Kind::BAG_EMPTY, Op::BAG_EMPTY},
        {::cvc5::api::Kind::BAG_CARD, Op::BAG_CARD},
        {::cvc5::api::Kind::BAG_CHOOSE, Op::BAG_CHOOSE},
        {::cvc5::api::Kind::BAG_IS_SINGLETON, Op::BAG_IS_SINGLETON},
        {::cvc5::api::Kind::BAG_FROM_SET, Op::BAG_FROM_SET},
        {::cvc5::api::Kind::BAG_TO_SET, Op::BAG_TO_SET},
        {::cvc5::api::Kind::BAG_MAP, Op::BAG_MAP},
        // Sequences
        {::cvc5::api::Kind::SEQ_CONCAT, Op::SEQ_CONCAT},
        {::cvc5::api::Kind::SEQ_LENGTH, Op::SEQ_LENGTH},
        {::cvc5::api::Kind::SEQ_EXTRACT, Op::SEQ_EXTRACT},
        {::cvc5::api::Kind::SEQ_UPDATE, Op::SEQ_UPDATE},
        {::cvc5::api::Kind::SEQ_AT, Op::SEQ_AT},
        {::cvc5::api::Kind::SEQ_CONTAINS, Op::SEQ_CONTAINS},
        {::cvc5::api::Kind::SEQ_INDEXOF, Op::SEQ_INDEXOF},
        {::cvc5::api::Kind::SEQ_REPLACE, Op::SEQ_REPLACE},
        {::cvc5::api::Kind::SEQ_REPLACE_ALL, Op::SEQ_REPLACE_ALL},
        {::cvc5::api::Kind::SEQ_REV, Op::SEQ_REV},
        {::cvc5::api::Kind::SEQ_PREFIX, Op::SEQ_PREFIX},
        {::cvc5::api::Kind::SEQ_SUFFIX, Op::SEQ_SUFFIX},
        {::cvc5::api::Kind::SEQ_UNIT, Op::SEQ_UNIT},
        {::cvc5::api::Kind::SEQ_NTH, Op::SEQ_NTH},
        // Sets
        {::cvc5::api::Kind::SET_CARD, Op::SET_CARD},
        {::cvc5::api::Kind::SET_COMPLEMENT, Op::SET_COMPLEMENT},
        {::cvc5::api::Kind::SET_COMPREHENSION, Op::SET_COMPREHENSION},
        {::cvc5::api::Kind::SET_CHOOSE, Op::SET_CHOOSE},
        {::cvc5::api::Kind::SET_INTER, Op::SET_INTERSECTION},
        {::cvc5::api::Kind::SET_INSERT, Op::SET_INSERT},
        {::cvc5::api::Kind::SET_IS_SINGLETON, Op::SET_IS_SINGLETON},
        {::cvc5::api::Kind::SET_UNION, Op::SET_UNION},
        {::cvc5::api::Kind::SET_MEMBER, Op::SET_MEMBER},
        {::cvc5::api::Kind::SET_MINUS, Op::SET_MINUS},
        {::cvc5::api::Kind::SET_SINGLETON, Op::SET_SINGLETON},
        {::cvc5::api::Kind::SET_SUBSET, Op::SET_SUBSET},
        {::cvc5::api::Kind::RELATION_JOIN, Op::REL_JOIN},
        {::cvc5::api::Kind::RELATION_JOIN_IMAGE, Op::REL_JOIN_IMAGE},
        {::cvc5::api::Kind::RELATION_IDEN, Op::REL_IDEN},
        {::cvc5::api::Kind::RELATION_PRODUCT, Op::REL_PRODUCT},
        {::cvc5::api::Kind::RELATION_TCLOSURE, Op::REL_TCLOSURE},
        {::cvc5::api::Kind::RELATION_TRANSPOSE, Op::REL_TRANSPOSE},

        /* Solver-specific operators */
        {::cvc5::api::Kind::BITVECTOR_REDOR, OP_BV_REDOR},
        // BV
        {::cvc5::api::Kind::BITVECTOR_REDAND, OP_BV_REDAND},
        {::cvc5::api::Kind::BITVECTOR_ULTBV, OP_BV_ULTBV},
        {::cvc5::api::Kind::BITVECTOR_SLTBV, OP_BV_SLTBV},
        {::cvc5::api::Kind::BITVECTOR_ITE, OP_BV_ITE},
        // Datatypes
        {::cvc5::api::Kind::DT_SIZE, OP_DT_SIZE},
        // Int
        {::cvc5::api::Kind::BITVECTOR_TO_NAT, OP_BV_TO_NAT},
        {::cvc5::api::Kind::IAND, OP_INT_IAND},
        {::cvc5::api::Kind::INT_TO_BITVECTOR, OP_INT_TO_BV},
        {::cvc5::api::Kind::POW2, OP_INT_POW2},
        // Strings
        {::cvc5::api::Kind::STRING_UPDATE, OP_STRING_UPDATE},
        {::cvc5::api::Kind::STRING_TOLOWER, OP_STRING_TOLOWER},
        {::cvc5::api::Kind::STRING_TOUPPER, OP_STRING_TOUPPER},
        {::cvc5::api::Kind::STRING_REV, OP_STRING_REV},

        /* Special value kinds that cvc5 introduces its own node kind for,
         * only used for getKind(). */
        {::cvc5::api::Kind::PI, OP_REAL_PI},
        {::cvc5::api::Kind::REGEXP_STAR, OP_REGEXP_STAR},
        {::cvc5::api::Kind::SET_EMPTY, OP_SET_EMPTY},
        {::cvc5::api::Kind::SET_UNIVERSE, OP_SET_UNIVERSE},
};

::cvc5::api::Term&
Cvc5Term::get_cvc5_term(Term term)
{
  return static_cast<Cvc5Term*>(term.get())->d_term;
}

std::vector<Term>
Cvc5Term::cvc5_terms_to_terms(RNGenerator& rng,
                              ::cvc5::api::Solver* cvc5,
                              const std::vector<::cvc5::api::Term>& terms)
{
  std::vector<Term> res;
  for (auto& t : terms)
  {
    res.push_back(std::shared_ptr<Cvc5Term>(new Cvc5Term(rng, cvc5, t)));
  }
  return res;
}

std::vector<::cvc5::api::Term>
Cvc5Term::terms_to_cvc5_terms(const std::vector<Term>& terms)
{
  std::vector<::cvc5::api::Term> res;
  for (auto& t : terms)
  {
    res.push_back(get_cvc5_term(t));
  }
  return res;
}

size_t
Cvc5Term::hash() const
{
  return std::hash<::cvc5::api::Term>{}(d_term);
}

bool
Cvc5Term::equals(const Term& other) const
{
  Cvc5Term* cvc5_term = dynamic_cast<Cvc5Term*>(other.get());
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
  ::cvc5::api::Kind cvc5_kind = d_term.getKind();
  if (cvc5_kind == ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_GENERIC)
  {
    if (d_term.getNumChildren() == 1)
    {
      return Op::FP_TO_FP_FROM_BV;
    }
    if (d_term[1].getSort().isFloatingPoint())
    {
      return Op::FP_TO_FP_FROM_FP;
    }
    return Op::FP_TO_FP_FROM_SBV;
  }
  return s_cvc5_kinds_to_kinds.at(cvc5_kind);
}

std::vector<Term>
Cvc5Term::get_children() const
{
  std::vector<Term> res;
  for (const auto& c : d_term)
  {
    res.emplace_back(new Cvc5Term(d_rng, d_solver, c));
  }
  return res;
}

bool
Cvc5Term::is_indexed() const
{
  return d_term.getOp().isIndexed();
}

size_t
Cvc5Term::get_num_indices() const
{
  return d_term.getOp().getNumIndices();
}

std::vector<std::string>
Cvc5Term::get_indices() const
{
  assert(is_indexed());
  std::vector<std::string> res;
  Op::Kind kind = get_kind();
  size_t n_idxs = get_num_indices();
  if (d_rng.flip_coin())
  {
    if (kind == Op::INT_IS_DIV)
    {
      res.push_back(d_term.getOp().getIndices<std::string>());
    }
    else if (n_idxs == 2)
    {
      auto cvc5_res =
          d_term.getOp().getIndices<std::pair<uint32_t, uint32_t>>();
      res.push_back(std::to_string(cvc5_res.first));
      res.push_back(std::to_string(cvc5_res.second));
    }
    else
    {
      MURXLA_TEST(n_idxs == 1);
      res.push_back(std::to_string(d_term.getOp().getIndices<uint32_t>()));
    }
  }
  else
  {
    auto cvc5_res = d_term.getOp().getIndices<std::vector<::cvc5::api::Term>>();
    if (kind == Op::INT_IS_DIV)
    {
      MURXLA_TEST(cvc5_res.size() == 1);
      MURXLA_TEST(cvc5_res[0].isIntegerValue());
      res.push_back(cvc5_res[0].getIntegerValue());
    }
    else
    {
      for (auto& t : cvc5_res)
      {
        MURXLA_TEST(t.isIntegerValue());
        res.push_back(t.getIntegerValue());
      }
    }
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
      new Cvc5Sort(d_solver, d_term.getSort().getArrayIndexSort()));
}

Sort
Cvc5Term::get_array_element_sort() const
{
  assert(is_array());
  return std::shared_ptr<Cvc5Sort>(
      new Cvc5Sort(d_solver, d_term.getSort().getArrayElementSort()));
}

uint32_t
Cvc5Term::get_fun_arity() const
{
  assert(is_fun());
  return d_term.getSort().getFunctionArity();
}

Sort
Cvc5Term::get_fun_codomain_sort() const
{
  assert(is_fun());
  return std::shared_ptr<Cvc5Sort>(
      new Cvc5Sort(d_solver, d_term.getSort().getFunctionCodomainSort()));
}

std::vector<Sort>
Cvc5Term::get_fun_domain_sorts() const
{
  assert(is_fun());
  std::vector<::cvc5::api::Sort> cvc5_res =
      d_term.getSort().getFunctionDomainSorts();
  return Cvc5Sort::cvc5_sorts_to_sorts(d_solver, cvc5_res);
}

/* -------------------------------------------------------------------------- */
/* Cvc5Solver                                                                 */
/* -------------------------------------------------------------------------- */

OpKindSet
Cvc5Solver::get_unsupported_op_kinds() const
{
  return {Op::BAG_CHOOSE,
          Op::BAG_FROM_SET,
          Op::BAG_TO_SET,
          Op::BAG_IS_SINGLETON,
          Op::IFF};
}

Solver::OpKindSortKindMap
Cvc5Solver::get_unsupported_op_sort_kinds() const
{
  std::unordered_map<Op::Kind, SortKindSet> res =
      Solver::get_unsupported_op_sort_kinds();
  /* Disallow DISTINCT over REGLAN terms. */
  {
    const auto& it = res.find(Op::DISTINCT);
    if (it == res.end())
    {
      res[Op::DISTINCT] = {SORT_REGLAN};
    }
    else
    {
      it->second.insert(SORT_REGLAN);
    }
  }
  /* Disallow EQUAL over REGLAN terms. */
  {
    const auto& it = res.find(Op::EQUAL);
    if (it == res.end())
    {
      res[Op::EQUAL] = {SORT_REGLAN};
    }
    else
    {
      it->second.insert(SORT_REGLAN);
    }
  }
  /* Disallow ITE over REGLAN terms. */
  {
    const auto& it = res.find(Op::ITE);
    if (it == res.end())
    {
      res[Op::ITE] = {SORT_REGLAN};
    }
    else
    {
      it->second.insert(SORT_REGLAN);
    }
  }
  return res;
}

SortKindSet
Cvc5Solver::get_unsupported_var_sort_kinds() const
{
  return {SORT_FUN, SORT_REGLAN};
}

SortKindSet
Cvc5Solver::get_unsupported_array_index_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN, SORT_REGLAN};
}

SortKindSet
Cvc5Solver::get_unsupported_array_element_sort_kinds() const
{
  return {SORT_FUN, SORT_REGLAN};
}

SortKindSet
Cvc5Solver::get_unsupported_bag_element_sort_kinds() const
{
  return {SORT_FUN, SORT_REGLAN};
}

SortKindSet
Cvc5Solver::get_unsupported_seq_element_sort_kinds() const
{
  return {SORT_FUN, SORT_REGLAN};
}

SortKindSet
Cvc5Solver::get_unsupported_set_element_sort_kinds() const
{
  return {SORT_FUN, SORT_REGLAN};
}

SortKindSet
Cvc5Solver::get_unsupported_dt_sel_codomain_sort_kinds() const
{
  return {SORT_FUN, SORT_REGLAN};
}

SortKindSet
Cvc5Solver::get_unsupported_fun_domain_sort_kinds() const
{
  return {SORT_FUN, SORT_REGLAN};
}

SortKindSet
Cvc5Solver::get_unsupported_fun_codomain_sort_kinds() const
{
  return {SORT_FUN, SORT_REGLAN};
}

SortKindSet
Cvc5Solver::get_unsupported_get_value_sort_kinds() const
{
  return {SORT_REGLAN};
}

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
  d_solver = new ::cvc5::api::Solver();
}

void
Cvc5Solver::delete_solver()
{
  assert(d_solver != nullptr);
  delete d_solver;
  d_solver = nullptr;
}

::cvc5::api::Solver*
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

bool
Cvc5Solver::is_unsat_assumption(const Term& t) const
{
  return !Cvc5Term::get_cvc5_term(t).isNull();
}

/* -------------------------------------------------------------------------- */

Sort
Cvc5Solver::mk_sort(SortKind kind)
{
  ::cvc5::api::Sort cvc5_res;
  switch (kind)
  {
    case SORT_BOOL: cvc5_res = d_solver->getBooleanSort(); break;
    case SORT_INT: cvc5_res = d_solver->getIntegerSort(); break;
    case SORT_REAL: cvc5_res = d_solver->getRealSort(); break;
    case SORT_RM: cvc5_res = d_solver->getRoundingModeSort(); break;
    case SORT_REGLAN: cvc5_res = d_solver->getRegExpSort(); break;
    case SORT_STRING: cvc5_res = d_solver->getStringSort(); break;

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unsupported sort kind '" << kind
          << "' as argument to Cvc5Solver::mk_sort, expected '" << SORT_BOOL
          << "', '" << SORT_INT << "', '" << SORT_REAL << "', '" << SORT_RM
          << "', '" << SORT_REGLAN << "' or '" << SORT_STRING << "'";
  }
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_solver, cvc5_res));
}

Sort
Cvc5Solver::mk_sort(SortKind kind, uint32_t size)
{
  MURXLA_CHECK_CONFIG(kind == SORT_BV)
      << "unsupported sort kind '" << kind
      << "' as argument to Cvc5Solver::mk_sort, expected '" << SORT_BV << "'";
  ::cvc5::api::Sort cvc5_res = d_solver->mkBitVectorSort(size);
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_solver, cvc5_res));
}

Sort
Cvc5Solver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  MURXLA_CHECK_CONFIG(kind == SORT_FP)
      << "unsupported sort kind '" << kind
      << "' as argument to Cvc5Solver::mk_sort, expected '" << SORT_FP << "'";
  ::cvc5::api::Sort cvc5_res = d_solver->mkFloatingPointSort(esize, ssize);
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_solver, cvc5_res));
}

Sort
Cvc5Solver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  ::cvc5::api::Sort cvc5_res;

  switch (kind)
  {
    case SORT_ARRAY:
      assert(sorts.size() == 2);
      cvc5_res = d_solver->mkArraySort(Cvc5Sort::get_cvc5_sort(sorts[0]),
                                       Cvc5Sort::get_cvc5_sort(sorts[1]));
      break;

    case SORT_BAG:
      assert(sorts.size() == 1);
      cvc5_res = d_solver->mkBagSort(Cvc5Sort::get_cvc5_sort(sorts[0]));
      break;

    case SORT_FUN:
    {
      std::vector<::cvc5::api::Sort> domain;
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        domain.push_back(Cvc5Sort::get_cvc5_sort(*it));
      }
      ::cvc5::api::Sort codomain = Cvc5Sort::get_cvc5_sort(sorts.back());

      cvc5_res = d_solver->mkFunctionSort(domain, codomain);
      break;
    }

    case SORT_SEQ:
      assert(sorts.size() == 1);
      cvc5_res = d_solver->mkSequenceSort(Cvc5Sort::get_cvc5_sort(sorts[0]));
      break;

    case SORT_SET:
      assert(sorts.size() == 1);
      cvc5_res = d_solver->mkSetSort(Cvc5Sort::get_cvc5_sort(sorts[0]));
      break;

    default:
      MURXLA_CHECK_CONFIG(false) << "unsupported sort kind '" << kind
                                 << "' as argument to Cvc5Solver::mk_sort, "
                                    "expected '"
                                 << SORT_ARRAY << "' or '" << SORT_FUN << "'";
  }
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_solver, cvc5_res));
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

  std::vector<::cvc5::api::DatatypeDecl> cvc5_dtypedecls;

  for (size_t i = 0; i < n_dt_sorts; ++i)
  {
    const std::string& name = dt_names[i];
    const auto& psorts      = param_sorts[i];
    const auto& ctors       = constructors[i];

    bool is_parametric = !psorts.empty();
    std::unordered_map<std::string, ::cvc5::api::Sort> symbol_to_cvc5_psorts;
    std::vector<::cvc5::api::Sort> cvc5_psorts;
    for (const auto& s : psorts)
    {
      const std::string& symbol =
          dynamic_cast<ParamSort*>(s.get())->get_symbol();
      ::cvc5::api::Sort cvc5_param_sort = d_solver->mkParamSort(symbol);
      cvc5_psorts.push_back(cvc5_param_sort);
      assert(symbol_to_cvc5_psorts.find(symbol) == symbol_to_cvc5_psorts.end());
      symbol_to_cvc5_psorts[symbol] = cvc5_param_sort;
    }

    ::cvc5::api::DatatypeDecl cvc5_dtypedecl =
        is_parametric ? (psorts.size() == 1 && d_rng.flip_coin()
                             ? d_solver->mkDatatypeDecl(name, cvc5_psorts[0])
                             : d_solver->mkDatatypeDecl(name, cvc5_psorts))
                      : d_solver->mkDatatypeDecl(name);
    if (d_rng.pick_with_prob(10))
    {
      MURXLA_TEST(is_parametric == cvc5_dtypedecl.isParametric());
      MURXLA_TEST(name == cvc5_dtypedecl.getName());
    }

    std::vector<::cvc5::api::DatatypeConstructorDecl> cvc5_ctors;
    for (const auto& c : ctors)
    {
      const auto& cname = c.first;
      const auto& sels  = c.second;

      ::cvc5::api::DatatypeConstructorDecl cvc5_cdecl =
          d_solver->mkDatatypeConstructorDecl(cname);

      for (const auto& s : sels)
      {
        const auto& sname = s.first;
        const auto& ssort = s.second;
        if (ssort == nullptr)
        {
          cvc5_cdecl.addSelectorSelf(sname);
        }
        else
        {
          if (ssort->is_param_sort())
          {
            const std::string& symbol =
                dynamic_cast<ParamSort*>(ssort.get())->get_symbol();
            assert(symbol_to_cvc5_psorts.find(symbol)
                   != symbol_to_cvc5_psorts.end());
            cvc5_cdecl.addSelector(sname, symbol_to_cvc5_psorts.at(symbol));
          }
          else
          {
            cvc5_cdecl.addSelector(sname, Cvc5Sort::get_cvc5_sort(ssort));
          }
        }
      }

      cvc5_dtypedecl.addConstructor(cvc5_cdecl);
    }
    cvc5_dtypedecls.push_back(cvc5_dtypedecl);
  }

  if (n_dt_sorts == 1 && d_rng.flip_coin())
  {
    ::cvc5::api::Sort cvc5_res = d_solver->mkDatatypeSort(cvc5_dtypedecls[0]);
    MURXLA_TEST(!cvc5_res.isNull());
    MURXLA_TEST(!cvc5_res.getDatatype().isNull());
    return {std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_solver, cvc5_res))};
  }

  std::vector<::cvc5::api::Sort> cvc5_res =
      d_solver->mkDatatypeSorts(cvc5_dtypedecls);
  size_t idx = d_rng.pick<size_t>(0, cvc5_res.size() - 1);
  MURXLA_TEST(!cvc5_res[idx].isNull());
  MURXLA_TEST(!cvc5_res[idx].getDatatype().isNull());
  std::vector<Sort> res(cvc5_res.size());
  std::transform(
      cvc5_res.begin(), cvc5_res.end(), res.begin(), [this](const auto& sort) {
        return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_solver, sort));
      });
  return res;
}

Sort
Cvc5Solver::instantiate_sort(Sort param_sort, const std::vector<Sort>& sorts)
{
  ::cvc5::api::Sort cvc5_param_sort = Cvc5Sort::get_cvc5_sort(param_sort);
  std::vector<::cvc5::api::Sort> cvc5_sorts =
      Cvc5Sort::sorts_to_cvc5_sorts(sorts);
  ::cvc5::api::Sort cvc5_res = cvc5_param_sort.instantiate(cvc5_sorts);
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_const(Sort sort, const std::string& name)
{
  ::cvc5::api::Term cvc5_res =
      d_solver->mkConst(Cvc5Sort::get_cvc5_sort(sort), name);
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Term>(new Cvc5Term(d_rng, d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_var(Sort sort, const std::string& name)
{
  ::cvc5::api::Term cvc5_res =
      d_solver->mkVar(Cvc5Sort::get_cvc5_sort(sort), name);
  MURXLA_TEST(!cvc5_res.isNull());
  return std::shared_ptr<Cvc5Term>(new Cvc5Term(d_rng, d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_value(Sort sort, bool value)
{
  MURXLA_CHECK_CONFIG(sort->is_bool())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to "
         "Cvc5Solver::mk_value, expected Boolean sort ";

  ::cvc5::api::Term cvc5_res;

  if (d_rng.flip_coin())
  {
    cvc5_res = value ? d_solver->mkTrue() : d_solver->mkFalse();
  }
  else
  {
    cvc5_res = d_solver->mkBoolean(value);
  }
  MURXLA_TEST(!cvc5_res.isNull());
  std::shared_ptr<Cvc5Term> res(new Cvc5Term(d_rng, d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_value(Sort sort, const std::string& value)
{
  ::cvc5::api::Term cvc5_res;
  ::cvc5::api::Sort cvc5_sort = Cvc5Sort::get_cvc5_sort(sort);
  SortKind sort_kind        = sort->get_kind();

  switch (sort_kind)
  {
    case SORT_FP:
    {
      uint32_t ew = sort->get_fp_exp_size();
      uint32_t sw = sort->get_fp_sig_size();
      cvc5_res    = d_solver->mkFloatingPoint(
          ew, sw, d_solver->mkBitVector(ew + sw, value, 2));
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
        cvc5_res = d_solver->mkInteger(val64);
      }
      else
      {
        cvc5_res = d_solver->mkInteger(value);
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
          cvc5_res = d_solver->mkReal(val64);
        }
        else
        {
          cvc5_res = d_solver->mkReal(value);
        }
      }
      else
      {
        cvc5_res = d_solver->mkReal(value);
      }
      break;

    case SORT_REGLAN:
    case SORT_STRING:
      // TODO: test more mkString functions
      cvc5_res = d_solver->mkString(value);
      break;

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unexpected sort of kind '" << sort->get_kind()
          << "' as argument to "
             "Cvc5Solver::mk_value, expected Integer, Real, Reglan or String "
             "sort ";
  }
  MURXLA_TEST(!cvc5_res.isNull());
  std::shared_ptr<Cvc5Term> res(new Cvc5Term(d_rng, d_solver, cvc5_res));
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
  ::cvc5::api::Term cvc5_res;

  cvc5_res = d_solver->mkReal(
      static_cast<int64_t>(strtoull(num.c_str(), nullptr, 10)),
      static_cast<int64_t>(strtoull(den.c_str(), nullptr, 10)));
  MURXLA_TEST(!cvc5_res.isNull());
  std::shared_ptr<Cvc5Term> res(new Cvc5Term(d_rng, d_solver, cvc5_res));
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

  ::cvc5::api::Term cvc5_res;
  ::cvc5::api::Sort cvc5_sort = Cvc5Sort::get_cvc5_sort(sort);
  uint32_t bw               = sort->get_bv_size();

  switch (base)
  {
    case DEC:
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc5_res =
            d_solver->mkBitVector(bw, strtoull(value.c_str(), nullptr, 10));
      }
      else
      {
        cvc5_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bw, value, 10)
                       : d_solver->mkBitVector(bw, value.c_str(), 10);
      }
      break;

    case HEX:
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc5_res =
            d_solver->mkBitVector(bw, strtoull(value.c_str(), nullptr, 16));
      }
      else
      {
        cvc5_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bw, value, 16)
                       : d_solver->mkBitVector(bw, value.c_str(), 16);
      }
      break;

    default:
      assert(base == BIN);
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc5_res =
            d_solver->mkBitVector(bw, strtoull(value.c_str(), nullptr, 2));
      }
      else
      {
        cvc5_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bw, value, 2)
                       : d_solver->mkBitVector(bw, value.c_str(), 2);
      }
  }
  MURXLA_TEST(!cvc5_res.isNull());
  std::shared_ptr<Cvc5Term> res(new Cvc5Term(d_rng, d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_special_value(Sort sort, const AbsTerm::SpecialValueKind& value)
{
  ::cvc5::api::Term cvc5_res;

  switch (sort->get_kind())
  {
    case SORT_BAG:
    {
      assert(value == AbsTerm::SPECIAL_VALUE_BAG_EMPTY);
      const std::vector<Sort>& sorts = sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      cvc5_res          = d_solver->mkEmptyBag(Cvc5Sort::get_cvc5_sort(sort));
    }
    break;

    case SORT_BV:
    {
      uint32_t bw = sort->get_bv_size();
      if (value == AbsTerm::SPECIAL_VALUE_BV_ZERO)
      {
        cvc5_res =
            d_rng.flip_coin()
                ? d_solver->mkBitVector(bw, bv_special_value_zero_str(bw), 2)
                : d_solver->mkBitVector(
                    bw, bv_special_value_zero_str(bw).c_str(), 2);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_ONE)
      {
        cvc5_res =
            d_rng.flip_coin()
                ? d_solver->mkBitVector(bw, bv_special_value_one_str(bw), 2)
                : d_solver->mkBitVector(
                    bw, bv_special_value_one_str(bw).c_str(), 2);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_ONES)
      {
        cvc5_res =
            d_rng.flip_coin()
                ? d_solver->mkBitVector(bw, bv_special_value_ones_str(bw), 2)
                : d_solver->mkBitVector(
                    bw, bv_special_value_ones_str(bw).c_str(), 2);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED)
      {
        cvc5_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(
                           bw, bv_special_value_min_signed_str(bw), 2)
                       : d_solver->mkBitVector(
                           bw, bv_special_value_min_signed_str(bw).c_str(), 2);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED);
        cvc5_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(
                           bw, bv_special_value_max_signed_str(bw), 2)
                       : d_solver->mkBitVector(
                           bw, bv_special_value_max_signed_str(bw).c_str(), 2);
      }
    }
    break;

    case SORT_FP:
    {
      uint32_t ew = sort->get_fp_exp_size();
      uint32_t sw = sort->get_fp_sig_size();
      if (value == AbsTerm::SPECIAL_VALUE_FP_POS_INF)
      {
        cvc5_res = d_solver->mkPosInf(ew, sw);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_NEG_INF)
      {
        cvc5_res = d_solver->mkNegInf(ew, sw);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_POS_ZERO)
      {
        cvc5_res = d_solver->mkPosZero(ew, sw);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_NEG_ZERO)
      {
        cvc5_res = d_solver->mkNegZero(ew, sw);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_FP_NAN);
        cvc5_res = d_solver->mkNaN(ew, sw);
      }
    }
    break;

    case SORT_RM:
      if (value == AbsTerm::SPECIAL_VALUE_RM_RNE)
      {
        cvc5_res = d_solver->mkRoundingMode(
            ::cvc5::api::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RNA)
      {
        cvc5_res = d_solver->mkRoundingMode(
            ::cvc5::api::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RTN)
      {
        cvc5_res = d_solver->mkRoundingMode(
            ::cvc5::api::RoundingMode::ROUND_TOWARD_NEGATIVE);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RTP)
      {
        cvc5_res = d_solver->mkRoundingMode(
            ::cvc5::api::RoundingMode::ROUND_TOWARD_POSITIVE);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_RM_RTZ);
        cvc5_res = d_solver->mkRoundingMode(
            ::cvc5::api::RoundingMode::ROUND_TOWARD_ZERO);
      }
      break;

    case SORT_SEQ:
    {
      assert(value == AbsTerm::SPECIAL_VALUE_SEQ_EMPTY);
      const std::vector<Sort>& sorts = sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      cvc5_res =
          d_solver->mkEmptySequence(Cvc5Sort::get_cvc5_sort(element_sort));
    }
    break;

    case SORT_SET:
    {
      const std::vector<Sort>& sorts = sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      if (value == AbsTerm::SPECIAL_VALUE_SET_EMPTY)
      {
        cvc5_res = d_solver->mkEmptySet(Cvc5Sort::get_cvc5_sort(sort));
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_SET_UNIVERSE);
        cvc5_res = d_solver->mkUniverseSet(Cvc5Sort::get_cvc5_sort(sort));
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
  std::shared_ptr<Cvc5Term> res(new Cvc5Term(d_rng, d_solver, cvc5_res));
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

  ::cvc5::api::Term cvc5_res;
  ::cvc5::api::Op cvc5_opterm;
  ::cvc5::api::Kind cvc5_kind = Cvc5Term::s_kinds_to_cvc5_kinds.at(kind);
  std::vector<::cvc5::api::Term> cvc5_args =
      Cvc5Term::terms_to_cvc5_terms(args);

  std::vector<uint32_t> iindices = indices;  // copy to modify
  int32_t n_args                 = args.size();
  uint32_t n_indices             = indices.size();

  if ((kind == Op::FP_TO_FP_FROM_BV || kind == Op::FP_TO_FP_FROM_FP
       || kind == Op::FP_TO_FP_FROM_SBV || kind == Op::FP_TO_FP_FROM_UBV
       || kind == Op::FP_TO_FP_FROM_REAL)
      && d_rng.flip_coin())
  {
    cvc5_kind = ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_GENERIC;
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
        cvc5_opterm = d_solver->mkOp(cvc5_kind, std::to_string(iindices[0]));
      }
      else
      {
        cvc5_opterm = d_solver->mkOp(cvc5_kind, iindices[0]);
      }
      MURXLA_TEST(!cvc5_opterm.isNull());
      MURXLA_TEST(!d_rng.pick_with_prob(1) || cvc5_opterm == cvc5_opterm);
      MURXLA_TEST(!d_rng.pick_with_prob(1) || !(cvc5_opterm != cvc5_opterm));
      MURXLA_TEST(cvc5_opterm.isIndexed());
      MURXLA_TEST(cvc5_opterm.getKind() == cvc5_kind);
      uint32_t idx;
      if (kind == Op::INT_IS_DIV)
      {
        std::string sidx = cvc5_opterm.getIndices<std::string>();
        /* we only generate 32 bit indices, so this shouldn't throw */
        idx = str_to_uint32(sidx);
      }
      else
      {
        idx = cvc5_opterm.getIndices<uint32_t>();
      }
      MURXLA_TEST(idx == iindices[0]);
      break;
    }
    case 2:
    {
      cvc5_opterm = d_solver->mkOp(cvc5_kind, iindices[0], iindices[1]);
      MURXLA_TEST(!cvc5_opterm.isNull());
      MURXLA_TEST(!d_rng.pick_with_prob(1) || cvc5_opterm == cvc5_opterm);
      MURXLA_TEST(!d_rng.pick_with_prob(1) || !(cvc5_opterm != cvc5_opterm));
      MURXLA_TEST(cvc5_opterm.isIndexed());
      MURXLA_TEST(cvc5_opterm.getKind() == cvc5_kind);
      std::pair<uint32_t, uint32_t> res_idxs =
          cvc5_opterm.getIndices<std::pair<uint32_t, uint32_t>>();
      MURXLA_TEST(res_idxs.first == iindices[0]);
      MURXLA_TEST(res_idxs.second == iindices[1]);
      break;
    }
    default:
      assert(n_indices == 0);
      if (d_rng.flip_coin())
      {
        cvc5_opterm = d_solver->mkOp(cvc5_kind);
      }
  }

  if (kind == Op::FORALL || kind == Op::EXISTS)
  {
    assert(args.size() >= 2);
    std::vector<::cvc5::api::Term> cvc5_vars;
    for (size_t i = 0; i < args.size() - 1; ++i)
    {
      cvc5_vars.push_back(cvc5_args[i]);
    }
    ::cvc5::api::Term cvc5_bvl =
        d_rng.flip_coin()
            ? d_solver->mkTerm(::cvc5::api::Kind::VARIABLE_LIST, cvc5_vars)
            : d_solver->mkTerm(d_solver->mkOp(::cvc5::api::Kind::VARIABLE_LIST),
                               cvc5_vars);
    ::cvc5::api::Term cvc5_body = Cvc5Term::get_cvc5_term(args.back());
    cvc5_args                   = {cvc5_bvl, cvc5_body};
    n_args                      = cvc5_args.size();
  }
  else if (kind == Op::RE_ALL)
  {
    cvc5_res = d_solver->mkRegexpAll();
    goto DONE;
  }
  else if (kind == Cvc5Term::OP_REAL_PI && d_rng.flip_coin())
  {
    cvc5_res = d_solver->mkPi();
    goto DONE;
  }
  else if (kind == Op::RE_NONE && d_rng.flip_coin())
  {
    cvc5_res = d_solver->mkRegexpNone();
    goto DONE;
  }
  else if (kind == Cvc5Term::OP_BV_ITE)
  {
    uint32_t size = cvc5_args[0].getSort().getBitVectorSize();
    /* if the first argument is of size greater than 1, slice random
     * bit out of it */
    if (size > 1)
    {
      uint32_t hi = d_rng.pick<uint32_t>(0, size - 1);
      uint32_t lo = hi;
      ::cvc5::api::Op op =
          d_solver->mkOp(::cvc5::api::Kind::BITVECTOR_EXTRACT, hi, lo);
      cvc5_args[0] = d_solver->mkTerm(op, cvc5_args[0]);
    }
  }
  else if (kind == Op::SET_INSERT || kind == Op::SET_MEMBER)
  {
    /* cvc5 uses order <elem>+ <set> for the arguments
     * (is given as <set> <elem>+) */
    ::cvc5::api::Term set = cvc5_args[0];
    size_t n              = cvc5_args.size() - 1;
    cvc5_args[0]          = cvc5_args[n];
    cvc5_args[n]          = set;
  }
  else if (kind == Op::SET_COMPREHENSION)
  {
    /* cvc5 uses order <var_list> <predicate> <term> for the arguments
     * (is given as <predicate> <term> <var>+) */
    assert(args.size() >= 3);
    std::vector<::cvc5::api::Term> vars;
    for (size_t i = 2; i < args.size(); ++i)
    {
      vars.push_back(cvc5_args[i]);
    }
    cvc5_args = {d_solver->mkTerm(::cvc5::api::Kind::VARIABLE_LIST, vars),
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
      cvc5_res = cvc5_opterm.isNull() ? d_solver->mkTerm(cvc5_kind)
                                      : d_solver->mkTerm(cvc5_opterm);
      break;

    case 1:
      if (kind == Op::NOT && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = cvc5_args[0].notTerm();
      }
      else
      {
        cvc5_res = cvc5_opterm.isNull()
                       ? d_solver->mkTerm(cvc5_kind, cvc5_args[0])
                       : d_solver->mkTerm(cvc5_opterm, cvc5_args[0]);
      }
      break;

    case 2:
      if (kind == Op::AND && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = cvc5_args[0].andTerm(cvc5_args[1]);
      }
      else if (kind == Op::OR && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = cvc5_args[0].orTerm(cvc5_args[1]);
      }
      else if (kind == Op::XOR && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = cvc5_args[0].xorTerm(cvc5_args[1]);
      }
      else if (kind == Op::EQUAL && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = cvc5_args[0].eqTerm(cvc5_args[1]);
      }
      else if (kind == Op::IMPLIES && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = cvc5_args[0].impTerm(cvc5_args[1]);
      }
      else
      {
        cvc5_res =
            cvc5_opterm.isNull()
                ? d_solver->mkTerm(cvc5_kind, cvc5_args[0], cvc5_args[1])
                : d_solver->mkTerm(cvc5_opterm, cvc5_args[0], cvc5_args[1]);
      }
      break;

    case 3:
      if (kind == Op::ITE && d_rng.flip_coin())
      {
        assert(!n_indices);
        cvc5_res = cvc5_args[0].iteTerm(cvc5_args[1], cvc5_args[2]);
      }
      else
      {
        cvc5_res =
            cvc5_opterm.isNull()
                ? d_solver->mkTerm(
                    cvc5_kind, cvc5_args[0], cvc5_args[1], cvc5_args[2])
                : d_solver->mkTerm(
                    cvc5_opterm, cvc5_args[0], cvc5_args[1], cvc5_args[2]);
      }
      break;

    default:
      assert(n_args == MURXLA_MK_TERM_N_ARGS_BIN || n_args > 3);
      cvc5_res = cvc5_opterm.isNull()
                     ? d_solver->mkTerm(cvc5_kind, cvc5_args)
                     : d_solver->mkTerm(cvc5_opterm, cvc5_args);
  }
DONE:
  MURXLA_TEST(!cvc5_res.isNull());
  MURXLA_TEST(cvc5_kind == cvc5_res.getKind()
              || (cvc5_res.getSort().isBoolean()
                  && cvc5_res.getKind() == ::cvc5::api::Kind::AND));
  return std::shared_ptr<Cvc5Term>(new Cvc5Term(d_rng, d_solver, cvc5_res));
}

::cvc5::api::DatatypeConstructor
Cvc5Solver::getDatatypeConstructor(::cvc5::api::Sort dt_sort,
                                   const std::string& ctor_name)
{
  ::cvc5::api::Datatype dt = dt_sort.getDatatype();
  ::cvc5::api::DatatypeConstructor res;
  auto choice = d_rng.pick_one_of_three();
  if (choice == RNGenerator::Choice::FIRST)
  {
    res = dt[ctor_name];
  }
  else if (choice == RNGenerator::Choice::SECOND)
  {
    auto ch = d_rng.pick_one_of_four();
    ::cvc5::api::Datatype::const_iterator it, end;
    if (ch == RNGenerator::Choice::FIRST)
    {
      for (it = dt.begin(), end = dt.end(); it != end; ++it)
      {
        if (it->getName() == ctor_name)
        {
          res = *it;
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
          break;
        }
      }
    }
  }
  else
  {
    res = dt.getConstructor(ctor_name);
  }
  MURXLA_TEST(!res.isNull());
  return res;
}

::cvc5::api::DatatypeSelector
Cvc5Solver::getDatatypeSelector(::cvc5::api::Sort dt_sort,
                                const std::string& ctor_name,
                                const std::string& sel_name)
{
  ::cvc5::api::DatatypeConstructor ctor =
      getDatatypeConstructor(dt_sort, ctor_name);
  ::cvc5::api::DatatypeSelector res;
  auto choice = d_rng.pick_one_of_four();
  if (choice == RNGenerator::Choice::FIRST)
  {
    res = ctor[sel_name];
  }
  else if (choice == RNGenerator::Choice::SECOND)
  {
    ::cvc5::api::DatatypeConstructor::const_iterator it, end;
    auto ch = d_rng.pick_one_of_four();
    if (ch == RNGenerator::Choice::FIRST)
    {
      for (it = ctor.begin(), end = ctor.end(); it != end; ++it)
      {
        if (it->getName() == sel_name)
        {
          res = *it;
          break;
        }
      }
    }
    else if (ch == RNGenerator::Choice::SECOND)
    {
      for (it = ctor.begin(), end = ctor.end(); it != end; it++)
      {
        if (it->getName() == sel_name)
        {
          res = *it;
          break;
        }
      }
    }
    else if (ch == RNGenerator::Choice::THIRD)
    {
      for (it = ctor.begin(), end = ctor.end(); !(it == end); ++it)
      {
        if (it->getName() == sel_name)
        {
          res = *it;
          break;
        }
      }
    }
    else
    {
      for (it = ctor.begin(), end = ctor.end(); !(it == end); it++)
      {
        if (it->getName() == sel_name)
        {
          res = *it;
          break;
        }
      }
    }
  }
  else if (choice == RNGenerator::Choice::THIRD)
  {
    res = ctor.getSelector(sel_name);
  }
  else
  {
    res = dt_sort.getDatatype().getSelector(sel_name);
  }

  MURXLA_TEST(!res.isNull());
  return res;
}

::cvc5::api::Term
Cvc5Solver::getDatatypeConstructorTerm(::cvc5::api::Sort dt_sort,
                                       const std::string& ctor_name)
{
  if (d_rng.flip_coin())
  {
    return dt_sort.getDatatype().getConstructorTerm(ctor_name);
  }
  return getDatatypeConstructor(dt_sort, ctor_name).getConstructorTerm();
}

::cvc5::api::Term
Cvc5Solver::getDatatypeSelectorTerm(::cvc5::api::Sort dt_sort,
                                    const std::string& ctor_name,
                                    const std::string& sel_name)
{
  if (d_rng.flip_coin())
  {
    return getDatatypeSelector(dt_sort, ctor_name, sel_name).getSelectorTerm();
  }
  return getDatatypeConstructor(dt_sort, ctor_name).getSelectorTerm(sel_name);
}

Term
Cvc5Solver::mk_term(const Op::Kind& kind,
                    const std::vector<std::string>& str_args,
                    const std::vector<Term>& args)
{
  MURXLA_CHECK_CONFIG(Cvc5Term::s_kinds_to_cvc5_kinds.find(kind)
                      != Cvc5Term::s_kinds_to_cvc5_kinds.end())
      << "Cvc5Solver: operator kind '" << kind << "' not configured";

  ::cvc5::api::Term cvc5_res;
  ::cvc5::api::Kind cvc5_kind = Cvc5Term::s_kinds_to_cvc5_kinds.at(kind);
  std::vector<::cvc5::api::Term> cvc5_args =
      Cvc5Term::terms_to_cvc5_terms(args);

  ::cvc5::api::Sort cvc5_dt_sort = cvc5_args[0].getSort();

  ::cvc5::api::Op cvc5_opterm;
  if (d_rng.flip_coin())
  {
    cvc5_opterm = d_solver->mkOp(cvc5_kind);
  }

  if (kind == Op::DT_APPLY_SEL)
  {
    assert(str_args.size() == 2);
    assert(args.size() == 1);

    ::cvc5::api::Term cvc5_sel_term =
        getDatatypeSelectorTerm(cvc5_dt_sort, str_args[0], str_args[1]);
    cvc5_res = cvc5_opterm.isNull()
                   ? d_solver->mkTerm(cvc5_kind, cvc5_sel_term, cvc5_args[0])
                   : d_solver->mkTerm(cvc5_opterm, cvc5_sel_term, cvc5_args[0]);
  }
  else
  {
    if (kind == Op::DT_APPLY_TESTER)
    {
      assert(str_args.size() == 1);
      assert(args.size() == 1);
      ::cvc5::api::DatatypeConstructor cvc5_ctor =
          getDatatypeConstructor(cvc5_dt_sort, str_args[0]);
      cvc5_res = cvc5_opterm.isNull()
                     ? d_solver->mkTerm(
                         cvc5_kind, cvc5_ctor.getTesterTerm(), cvc5_args[0])
                     : d_solver->mkTerm(
                         cvc5_opterm, cvc5_ctor.getTesterTerm(), cvc5_args[0]);
    }
    else
    {
      assert(kind == Op::DT_APPLY_UPDATER);
      assert(str_args.size() == 2);
      assert(args.size() == 2);

      ::cvc5::api::DatatypeSelector cvc5_sel =
          getDatatypeSelector(cvc5_dt_sort, str_args[0], str_args[1]);
      cvc5_res =
          cvc5_opterm.isNull() ? d_solver->mkTerm(
              cvc5_kind, cvc5_sel.getUpdaterTerm(), cvc5_args[0], cvc5_args[1])
                               : d_solver->mkTerm(cvc5_opterm,
                                                  cvc5_sel.getUpdaterTerm(),
                                                  cvc5_args[0],
                                                  cvc5_args[1]);
    }
  }
  MURXLA_TEST(!cvc5_res.isNull());
  MURXLA_TEST(cvc5_kind == cvc5_res.getKind()
              || (cvc5_res.getSort().isBoolean()
                  && cvc5_res.getKind() == ::cvc5::api::Kind::AND));
  return std::shared_ptr<Cvc5Term>(new Cvc5Term(d_rng, d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_term(const Op::Kind& kind,
                    Sort sort,
                    const std::vector<std::string>& str_args,
                    const std::vector<Term>& args)
{
  assert(sort->is_dt());

  ::cvc5::api::Term cvc5_res;
  ::cvc5::api::Kind cvc5_kind    = Cvc5Term::s_kinds_to_cvc5_kinds.at(kind);
  ::cvc5::api::Sort cvc5_dt_sort = Cvc5Sort::get_cvc5_sort(sort);
  std::vector<::cvc5::api::Term> cvc5_args =
      Cvc5Term::terms_to_cvc5_terms(args);

  if (kind == Op::DT_MATCH_BIND_CASE)
  {
    std::vector<::cvc5::api::Term> cvc5_vars;
    for (size_t i = 0; i < args.size() - 1; ++i)
    {
      cvc5_vars.push_back(cvc5_args[i]);
    }
    ::cvc5::api::Term cvc5_bvl =
        d_rng.flip_coin()
            ? d_solver->mkTerm(::cvc5::api::Kind::VARIABLE_LIST, cvc5_vars)
            : d_solver->mkTerm(d_solver->mkOp(::cvc5::api::Kind::VARIABLE_LIST),
                               cvc5_vars);

    if (str_args.size() == 1)
    {
      std::vector<Term> vars{args.begin(), args.end() - 1};
      Term acons = mk_term(Op::DT_APPLY_CONS, sort, str_args, vars);
      ::cvc5::api::Term cvc5_acons = Cvc5Term::get_cvc5_term(acons);
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
    ::cvc5::api::Term cvc5_acons = Cvc5Term::get_cvc5_term(acons);
    cvc5_args                    = {cvc5_acons, cvc5_args.back()};
  }
  else
  {
    assert(kind == Op::DT_APPLY_CONS);
    assert(str_args.size() == 1);

    ::cvc5::api::Term cvc5_ctor_term;
    if (sort->is_dt_instantiated())
    {
      cvc5_ctor_term = cvc5_dt_sort.getDatatype()
                           .getConstructor(str_args[0])
                           .getInstantiatedConstructorTerm(cvc5_dt_sort);
    }
    else
    {
      cvc5_ctor_term = getDatatypeConstructorTerm(cvc5_dt_sort, str_args[0]);
    }
    cvc5_args.insert(cvc5_args.begin(), cvc5_ctor_term);
  }

  if (d_rng.flip_coin())
  {
    ::cvc5::api::Op cvc5_opterm = d_solver->mkOp(cvc5_kind);
    cvc5_res                    = d_solver->mkTerm(cvc5_opterm, cvc5_args);
  }
  else
  {
    cvc5_res = d_solver->mkTerm(cvc5_kind, cvc5_args);
  }
  MURXLA_TEST(!cvc5_res.isNull());
  MURXLA_TEST(cvc5_kind == cvc5_res.getKind());
  return std::shared_ptr<Cvc5Term>(new Cvc5Term(d_rng, d_solver, cvc5_res));
}

Sort
Cvc5Solver::get_sort(Term term, SortKind sort_kind) const
{
  (void) sort_kind;
  ::cvc5::api::Term cvc5_term = Cvc5Term::get_cvc5_term(term);
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_solver, cvc5_term.getSort()));
}

void
Cvc5Solver::assert_formula(const Term& t)
{
  d_solver->assertFormula(Cvc5Term::get_cvc5_term(t));
}

Solver::Result
Cvc5Solver::check_sat()
{
  ::cvc5::api::Result res = d_solver->checkSat();
  MURXLA_TEST(!res.isNull());
  MURXLA_TEST(res != ::cvc5::api::Result());
  MURXLA_TEST(!d_rng.pick_with_prob(1) || res == res);
  if (res.isSat()) return Result::SAT;
  if (res.isUnsat()) return Result::UNSAT;
  MURXLA_TEST(res.isSatUnknown());
  if (d_rng.pick_with_prob(1))
  {
    (void) res.getUnknownExplanation();
  }
  return Result::UNKNOWN;
}

Solver::Result
Cvc5Solver::check_sat_assuming(const std::vector<Term>& assumptions)
{
  ::cvc5::api::Result res;
  std::vector<::cvc5::api::Term> cvc5_assumptions =
      Cvc5Term::terms_to_cvc5_terms(assumptions);

  MURXLA_TEST(assumptions.size() == cvc5_assumptions.size());

  res = cvc5_assumptions.size() == 1 && d_rng.flip_coin()
            ? d_solver->checkSatAssuming(cvc5_assumptions[0])
            : d_solver->checkSatAssuming(cvc5_assumptions);
  MURXLA_TEST(!res.isNull());
  MURXLA_TEST(!d_rng.pick_with_prob(1) || res == res);
  MURXLA_TEST(res != ::cvc5::api::Result());
  MURXLA_TEST(!res.isEntailed());
  MURXLA_TEST(!res.isNotEntailed());
  MURXLA_TEST(!res.isEntailmentUnknown());
  if (res.isSat()) return Result::SAT;
  if (res.isUnsat()) return Result::UNSAT;
  MURXLA_TEST(res.isSatUnknown());
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
  std::vector<::cvc5::api::Term> cvc5_res = d_solver->getUnsatAssumptions();
  return Cvc5Term::cvc5_terms_to_terms(d_rng, d_solver, cvc5_res);
}

std::vector<Term>
Cvc5Solver::get_unsat_core()
{
  std::vector<Term> res;
  std::vector<::cvc5::api::Term> cvc5_res = d_solver->getUnsatCore();
  return Cvc5Term::cvc5_terms_to_terms(d_rng, d_solver, cvc5_res);
}

std::vector<Term>
Cvc5Solver::get_value(const std::vector<Term>& terms)
{
  std::vector<Term> res;
  std::vector<::cvc5::api::Term> cvc5_res;
  std::vector<::cvc5::api::Term> cvc5_terms =
      Cvc5Term::terms_to_cvc5_terms(terms);

  if (d_rng.flip_coin())
  {
    cvc5_res = d_solver->getValue(cvc5_terms);
  }
  else
  {
    for (::cvc5::api::Term& t : cvc5_terms)
    {
      cvc5_res.push_back(d_solver->getValue(t));
    }
  }
  return Cvc5Term::cvc5_terms_to_terms(d_rng, d_solver, cvc5_res);
}

void
Cvc5Solver::push(uint32_t n_levels)
{
  d_solver->push(n_levels);
}

void
Cvc5Solver::pop(uint32_t n_levels)
{
  d_solver->pop(n_levels);
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
  d_solver->setLogic(logic);
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
  d_solver->resetAssertions();
}

void
Cvc5Solver::set_opt(const std::string& opt, const std::string& value)
{
  // Check if opt=value conflicts with already enabled options.
  ::cvc5::api::Solver check_opt_slv;
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
  catch (const ::cvc5::api::CVC5ApiOptionException& e)
  {
    throw MurxlaSolverOptionException("incompatible option");
  }

  d_solver->setOption(opt, value);
  d_enabled_options.emplace_back(opt, value);
}

void
Cvc5Solver::check_value(Term term)
{
  ::cvc5::api::Term cvc5_term = Cvc5Term::get_cvc5_term(term);

  if (cvc5_term.isAbstractValue())
  {
    (void) cvc5_term.getAbstractValue();
  }
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
  }
  if (cvc5_term.isReal32Value())
  {
    (void) cvc5_term.getReal32Value();
  }
  if (cvc5_term.isReal64Value())
  {
    (void) cvc5_term.getReal64Value();
  }
  if (cvc5_term.isUInt32Value())
  {
    (void) cvc5_term.getUInt32Value();
  }
  if (cvc5_term.isUInt64Value())
  {
    (void) cvc5_term.getUInt64Value();
  }
  if (cvc5_term.isSequenceValue())
  {
    (void) cvc5_term.getSequenceValue();
  }
  if (cvc5_term.isSetValue())
  {
    (void) cvc5_term.getSetValue();
  }
  if (cvc5_term.isStringValue())
  {
    (void) cvc5_term.getStringValue();
  }
  if (cvc5_term.isTupleValue())
  {
    (void) cvc5_term.getTupleValue();
  }
  if (cvc5_term.isUninterpretedValue())
  {
    (void) cvc5_term.getUninterpretedValue();
  }
}

void
Cvc5Solver::check_sort(Sort sort)
{
  ::cvc5::api::Sort cvc5_sort = Cvc5Sort::get_cvc5_sort(sort);

  if (cvc5_sort.isDatatype())
  {
    const auto& cons_names = sort->get_dt_cons_names();
    const std::string& ctor =
        d_rng.pick_from_set<decltype(cons_names), std::string>(cons_names);

    ::cvc5::api::Term cvc5_ctor_term =
        d_rng.flip_coin()
            ? cvc5_sort.getDatatype().getConstructorTerm(ctor)
            : cvc5_sort.getDatatype().getConstructor(ctor).getConstructorTerm();
    MURXLA_TEST(cvc5_ctor_term.getSort().isConstructor());

    ::cvc5::api::Term cvc5_tester_term =
        cvc5_sort.getDatatype().getConstructor(ctor).getTesterTerm();
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

      ::cvc5::api::DatatypeSelector cvc5_sel =
          d_rng.flip_coin()
              ? cvc5_sort.getDatatype().getSelector(sel)
              : cvc5_sort.getDatatype().getConstructor(ctor).getSelector(sel);

      ::cvc5::api::Term cvc5_sel_term = cvc5_sel.getSelectorTerm();

      MURXLA_TEST(cvc5_sel_term.getSort().isSelector());

      Sort sel_codomain = sort->get_dt_sel_sort(sort, ctor, sel);
      ::cvc5::api::Sort cvc5_sel_codomain =
          cvc5_sel_term.getSort().getSelectorCodomainSort();
      ::cvc5::api::Sort cvc5_sel_domain =
          cvc5_sel_term.getSort().getSelectorDomainSort();
      MURXLA_TEST(cvc5_sel_domain == Cvc5Sort::get_cvc5_sort(sort));
      if (sel_codomain == nullptr)
      {
        MURXLA_TEST(cvc5_sel_codomain == Cvc5Sort::get_cvc5_sort(sort));
      }
      else if (!sel_codomain->is_param_sort())
      {
        MURXLA_TEST(cvc5_sel_codomain == Cvc5Sort::get_cvc5_sort(sel_codomain));
      }

      MURXLA_TEST(cvc5_sel.getUpdaterTerm().getSort().isUpdater());
    }

    std::vector<::cvc5::api::Sort> cvc5_ctor_domain_sorts =
        cvc5_ctor_term.getSort().getConstructorDomainSorts();
    MURXLA_TEST(cvc5_ctor_domain_sorts.size() == ctor_domain_sorts.size());
    for (size_t i = 0, n = ctor_domain_sorts.size(); i < n; ++i)
    {
      if (ctor_domain_sorts[i] == nullptr)
      {
        MURXLA_TEST(cvc5_ctor_domain_sorts[i] == Cvc5Sort::get_cvc5_sort(sort));
      }
      else if (!ctor_domain_sorts[i]->is_param_sort())
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
    if (cvc5_sort.getDatatype().isParametric())
    {
      if (!sorts.empty())
      {
        const auto& cvc5_param_sorts = cvc5_sort.getDatatypeParamSorts();
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
    (void) cvc5_sort.getUninterpretedSortName();

    if (cvc5_sort.isUninterpretedSortParameterized())
    {
      (void) cvc5_sort.getUninterpretedSortParamSorts();
    }
  }
  else if (cvc5_sort.isSortConstructor())
  {
    (void) cvc5_sort.getSortConstructorName();
    (void) cvc5_sort.getSortConstructorArity();
    MURXLA_TEST(cvc5_sort.isFunctionLike());
  }
  if (cvc5_sort.isFunction())
  {
    MURXLA_TEST(cvc5_sort.isFunctionLike());
    MURXLA_TEST(!cvc5_sort.getFunctionCodomainSort().isBoolean()
                || cvc5_sort.isPredicate());
  }
  else
  {
    MURXLA_TEST(!cvc5_sort.isPredicate());
  }
  MURXLA_TEST(cvc5_sort.isSubsortOf(cvc5_sort));
  MURXLA_TEST(cvc5_sort.isComparableTo(cvc5_sort));
}

std::unordered_map<std::string, std::string>
Cvc5Solver::get_required_options(TheoryId theory) const
{
  std::unordered_map<std::string, std::string> reqopts;
  if (theory == THEORY_BAG)
  {
    reqopts.emplace("fmf-found", "true");
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
  // Real
  opmgr->add_op_kind(
      Cvc5Term::OP_REAL_PI, 0, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
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

class Cvc5ActionCheckEntailed : public Action
{
 public:
  Cvc5ActionCheckEntailed(SolverManager& smgr)
      : Action(smgr, Cvc5Solver::ACTION_CHECK_ENTAILED, NONE)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_incremental && d_smgr.d_n_sat_calls > 0) return false;
    if (!d_smgr.has_term(SORT_BOOL, 0)) return false;

    if (d_rng.flip_coin())
    {
      Term term = d_smgr.pick_term(SORT_BOOL, 0);
      _run(term);
    }
    else
    {
      uint32_t n_terms =
          d_rng.pick<uint32_t>(1, MURXLA_CVC5_MAX_N_TERMS_CHECK_ENTAILED);
      std::vector<Term> terms;
      for (uint32_t i = 0; i < n_terms; ++i)
      {
        Term t = d_smgr.pick_term(SORT_BOOL, 0);
        assert(t->get_sort()->get_kind() == SORT_BOOL);
        terms.push_back(t);
      }
      _run(terms);
    }
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS_MIN(1, "", tokens.size());
    if (tokens.size() == 1)
    {
      Term term = d_smgr.get_untraced_term(untrace_str_to_id(tokens[0]));
      MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
      _run(term);
    }
    else
    {
      std::vector<Term> terms;
      uint32_t n_terms = str_to_uint32(tokens[0]);
      for (uint32_t i = 0, idx = 1; i < n_terms; ++i, ++idx)
      {
        uint32_t id = untrace_str_to_id(tokens[idx]);
        Term term   = d_smgr.get_untraced_term(id);
        MURXLA_CHECK_TRACE_TERM(term, id);
        terms.push_back(term);
      }
      _run(terms);
    }
    return {};
  }

 private:
  void _run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    d_smgr.reset_sat();
    Cvc5Solver& solver          = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::api::Solver* cvc5   = solver.get_solver();
    ::cvc5::api::Term cvc5_term = Cvc5Term::get_cvc5_term(term);
    MURXLA_TEST(!cvc5_term.isNull());
    ::cvc5::api::Result res = cvc5->checkEntailed(cvc5_term);
    MURXLA_TEST(!res.isNull());
    MURXLA_TEST(!d_rng.pick_with_prob(1) || res == res);
    MURXLA_TEST(res != ::cvc5::api::Result());
    MURXLA_TEST(!res.isSat());
    MURXLA_TEST(!res.isUnsat());
    MURXLA_TEST(!res.isSatUnknown());
    if (res.isEntailmentUnknown())
    {
      if (d_rng.pick_with_prob(1))
      {
        (void) res.getUnknownExplanation();
      }
      d_smgr.report_result(Solver::Result::UNKNOWN);
    }
    else if (res.isEntailed())
    {
      d_smgr.report_result(Solver::Result::UNSAT);
    }
    else
    {
      MURXLA_TEST(res.isNotEntailed());
      d_smgr.report_result(Solver::Result::SAT);
    }
  }

  void _run(std::vector<Term> terms)
  {
    MURXLA_TRACE << get_kind() << " " << terms.size() << terms;
    d_smgr.reset_sat();
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::api::Solver* cvc5 = solver.get_solver();
    std::vector<::cvc5::api::Term> cvc5_terms =
        Cvc5Term::terms_to_cvc5_terms(terms);
    ::cvc5::api::Result res = cvc5->checkEntailed(cvc5_terms);
    MURXLA_TEST(!d_rng.pick_with_prob(1) || res == res);
    MURXLA_TEST(res != ::cvc5::api::Result());
    MURXLA_TEST(!res.isSat());
    MURXLA_TEST(!res.isUnsat());
    MURXLA_TEST(!res.isSatUnknown());
    if (res.isEntailmentUnknown())
    {
      if (d_rng.pick_with_prob(1))
      {
        (void) res.getUnknownExplanation();
      }
      d_smgr.report_result(Solver::Result::UNKNOWN);
    }
    else if (res.isEntailed())
    {
      d_smgr.report_result(Solver::Result::UNSAT);
    }
    else
    {
      MURXLA_TEST(res.isNotEntailed());
      d_smgr.report_result(Solver::Result::SAT);
    }
  }
};

class Cvc5ActionSimplify : public Action
{
 public:
  Cvc5ActionSimplify(SolverManager& smgr)
      : Action(smgr, Cvc5Solver::ACTION_SIMPLIFY, NONE)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    Term term = d_smgr.pick_term();
    _run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = d_smgr.get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    _run(term);
    return {};
  }

 private:
  void _run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    d_smgr.reset_sat();
    Cvc5Solver& solver         = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::api::Solver* cvc5  = solver.get_solver();
    ::cvc5::api::Term cvc5_res = cvc5->simplify(Cvc5Term::get_cvc5_term(term));
    MURXLA_TEST(!cvc5_res.isNull());
    /* Note: The simplified term 'cvc5_res' may or may not be already in the
     *       term DB. Since we can't always compute the exact level, we can't
     *       add the simplified term to the term DB. */
  }
};

/* -------------------------------------------------------------------------- */

void
Cvc5Solver::configure_fsm(FSM* fsm) const
{
  State* s_sat = fsm->get_state(State::CHECK_SAT);

  // Solver::simplify(const Term& term)
  auto a_simplify = fsm->new_action<Cvc5ActionSimplify>();
  fsm->add_action_to_all_states(a_simplify, 100, {State::NEW, State::DELETE});

  // Solver::checkEntailed(Term term)
  // Solver::checkEntailed(std::vector<Term> terms)
  auto a_check_entailed = fsm->new_action<Cvc5ActionCheckEntailed>();
  s_sat->add_action(a_check_entailed, 2);
}
/* -------------------------------------------------------------------------- */

void
Cvc5Solver::configure_options(SolverManager* smgr) const
{
  using namespace ::cvc5::api;

  ::cvc5::api::Solver slv;

  for (const auto& option : slv.getOptionNames())
  {
    auto info = slv.getOptionInfo(option);
    if (std::holds_alternative<OptionInfo::ValueInfo<bool>>(info.valueInfo))
    {
      smgr->add_option(new SolverOptionBool(option));
    }
    else if (std::holds_alternative<OptionInfo::NumberInfo<int64_t>>(
                 info.valueInfo))
    {
      auto num_info = std::get<OptionInfo::NumberInfo<int64_t>>(info.valueInfo);
      smgr->add_option(new SolverOptionNum<int64_t>(
          option,
          num_info.minimum.value_or(std::numeric_limits<int64_t>::min()),
          num_info.maximum.value_or(std::numeric_limits<int64_t>::max())));
    }
    else if (std::holds_alternative<OptionInfo::NumberInfo<uint64_t>>(
                 info.valueInfo))
    {
      auto num_info =
          std::get<OptionInfo::NumberInfo<uint64_t>>(info.valueInfo);
      smgr->add_option(new SolverOptionNum<uint64_t>(
          option,
          num_info.minimum.value_or(std::numeric_limits<uint64_t>::min()),
          num_info.maximum.value_or(std::numeric_limits<uint64_t>::max())));
    }
    else if (std::holds_alternative<OptionInfo::ModeInfo>(info.valueInfo))
    {
      auto mode_info = std::get<OptionInfo::ModeInfo>(info.valueInfo);
      smgr->add_option(new SolverOptionList(option, mode_info.modes));
    }
    else if (std::holds_alternative<OptionInfo::NumberInfo<double>>(
                 info.valueInfo))
    {
      auto num_info = std::get<OptionInfo::NumberInfo<double>>(info.valueInfo);
      smgr->add_option(new SolverOptionNum<double>(
          option,
          num_info.minimum.value_or(std::numeric_limits<double>::min()),
          num_info.maximum.value_or(std::numeric_limits<double>::max())));
    }
  }
}

}  // namespace cvc5
}  // namespace murxla

#endif
