#ifndef __SMTMBT__OP_H
#define __SMTMBT__OP_H

#include <cassert>
#include <cstdint>
#include <unordered_map>
#include <vector>

#include "sort.hpp"

namespace smtmbt {

enum OpKind
{
  OP_UNDEFINED,

  /* Special cases */
  OP_DISTINCT,
  OP_EQUAL,
  OP_ITE,

  /* Arrays */
  OP_ARRAY_SELECT,
  OP_ARRAY_STORE,

  /* Boolean */
  OP_AND,
  OP_IFF,
  OP_IMPLIES,
  OP_NOT,
  OP_OR,
  OP_XOR,

  /* BV */
  OP_BV_EXTRACT,
  OP_BV_REPEAT,
  OP_BV_ROTATE_LEFT,
  OP_BV_ROTATE_RIGHT,
  OP_BV_SIGN_EXTEND,
  OP_BV_ZERO_EXTEND,

  OP_BV_ADD,
  OP_BV_AND,
  OP_BV_ASHR,
  OP_BV_COMP,
  OP_BV_CONCAT,
  OP_BV_LSHR,
  OP_BV_MULT,
  OP_BV_NAND,
  OP_BV_NEG,
  OP_BV_NOR,
  OP_BV_NOT,
  OP_BV_OR,
  OP_BV_SDIV,
  OP_BV_SGE,
  OP_BV_SGT,
  OP_BV_SHL,
  OP_BV_SLE,
  OP_BV_SLT,
  OP_BV_SMOD,
  OP_BV_SREM,
  OP_BV_SUB,
  OP_BV_UDIV,
  OP_BV_UGE,
  OP_BV_UGT,
  OP_BV_ULE,
  OP_BV_ULT,
  OP_BV_UREM,
  OP_BV_XNOR,
  OP_BV_XOR,

  /* FP */
  OP_FP_TO_FP_FROM_BV,
  OP_FP_TO_FP_FROM_INT_BV,
  OP_FP_TO_FP_FROM_FP,
  OP_FP_TO_FP_FROM_UINT_BV,
  OP_FP_TO_FP_FROM_REAL,
  OP_FP_TO_SBV,
  OP_FP_TO_UBV,

  OP_FP_ABS,
  OP_FP_ADD,
  OP_FP_DIV,
  OP_FP_EQ,
  OP_FP_FMA,
  OP_FP_FP,
  OP_FP_IS_NORMAL,
  OP_FP_IS_SUBNORMAL,
  OP_FP_IS_INF,
  OP_FP_IS_NAN,
  OP_FP_IS_NEG,
  OP_FP_IS_POS,
  OP_FP_IS_ZERO,
  OP_FP_LT,
  OP_FP_LTE,
  OP_FP_GT,
  OP_FP_GTE,
  OP_FP_MAX,
  OP_FP_MIN,
  OP_FP_MUL,
  OP_FP_NEG,
  OP_FP_REM,
  OP_FP_RTI,
  OP_FP_SQRT,
  OP_FP_SUB,
  OP_FP_TO_REAL,

  /* Ints */
  OP_INT_IS_DIV,
  OP_INT_NEG,
  OP_INT_SUB,
  OP_INT_ADD,
  OP_INT_MUL,
  OP_INT_DIV,
  OP_INT_MOD,
  OP_INT_ABS,
  OP_INT_LT,
  OP_INT_LTE,
  OP_INT_GT,
  OP_INT_GTE,

  /* Reals */
  OP_REAL_NEG,
  OP_REAL_SUB,
  OP_REAL_ADD,
  OP_REAL_MUL,
  OP_REAL_DIV,
  OP_REAL_LT,
  OP_REAL_LTE,
  OP_REAL_GT,
  OP_REAL_GTE,

  /* Quantifiers */
  OP_FORALL,
  OP_EXISTS,

  /* Strings */
  OP_STR_CONCAT,
  OP_STR_LEN,
  OP_STR_LT,
  OP_STR_TO_RE,
  OP_STR_IN_RE,
  OP_RE_CONCAT,
  OP_RE_UNION,
  OP_RE_INTER,
  OP_RE_STAR,
  OP_STR_LE,
  OP_STR_AT,
  OP_STR_SUBSTR,
  OP_STR_PREFIXOF,
  OP_STR_SUFFIXOF,
  OP_STR_CONTAINS,
  OP_STR_INDEXOF,
  OP_STR_REPLACE,
  OP_STR_REPLACE_ALL,
  OP_STR_REPLACE_RE,
  OP_STR_REPLACE_RE_ALL,
  OP_RE_COMP,
  OP_RE_DIFF,
  OP_RE_PLUS,
  OP_RE_OPT,
  OP_RE_RANGE,
  OP_RE_POW,
  OP_RE_LOOP,
  OP_STR_IS_DIGIT,
  OP_STR_TO_CODE,
  OP_STR_FROM_CODE,
  OP_STR_TO_INT,
  OP_STR_FROM_INT,

  /* only place-holders for solver-specific operators below ----------------- */
  OP_EXT_OP_01,
  OP_EXT_OP_02,
  OP_EXT_OP_03,
  OP_EXT_OP_04,
  OP_EXT_OP_05,
  OP_EXT_OP_06,
  OP_EXT_OP_07,
  OP_EXT_OP_08,
  OP_EXT_OP_09,
  OP_EXT_OP_10,
  OP_EXT_OP_11,
  OP_EXT_OP_12,
  OP_EXT_OP_13,
  OP_EXT_OP_14,
  OP_EXT_OP_15,
  OP_EXT_OP_16,
  OP_EXT_OP_17,
  OP_EXT_OP_18,
  OP_EXT_OP_19,
  OP_EXT_OP_20,

  OP_ALL, /* must be last */
};

struct OpKindHashFunction
{
  size_t operator()(OpKind kind) const;
};

struct Op
{
  Op(OpKind kind,
     int32_t arity,
     uint32_t nparams,
     SortKind sort_kind,
     const std::vector<SortKind>& sort_kind_args,
     TheoryId theory)
      : d_kind(kind),
        d_arity(arity),
        d_nparams(nparams),
        d_sort_kind(sort_kind),
        d_theory(theory),
        d_sort_kind_args(sort_kind_args)
  {
  }

  bool operator==(const Op& other) const;

  SortKind get_arg_sort_kind(size_t i) const;

  /** The Kind. */
  OpKind d_kind;
  /** The arity of this kind. */
  int32_t d_arity;
  /** The number of parameters if parameterized. */
  uint32_t d_nparams;
  /** The sort kind of a term of this kind. */
  SortKind d_sort_kind;
  /** The theory to which the operator belongs to. */
  TheoryId d_theory;

 private:
  /** The sort kind of the term arguments of this kind. */
  std::vector<SortKind> d_sort_kind_args;
};

#define SMTMBT_OP_TO_STR(kind) \
  {                            \
    kind, #kind                \
  }

/** Map OpKind to its string representation. */
extern std::unordered_map<OpKind, std::string, OpKindHashFunction>
    op_kinds_to_str;

/** Use given string as string representation of given kind. */
void update_op_kinds_to_str(OpKind kind, std::string string);

std::ostream& operator<<(std::ostream& out, OpKind kind);

OpKind op_kind_from_str(std::string& s);

using OpKindVector = std::vector<OpKind>;
using OpKindSet    = std::unordered_set<OpKind, OpKindHashFunction>;
using OpKindMap    = std::unordered_map<OpKind, Op, OpKindHashFunction>;
using OpKinds = std::unordered_map<SortKind, OpKindVector>;

}  // namespace smtmbt

#endif
