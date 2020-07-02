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

  /* Boolean */
  OP_AND,
  OP_IFF,
  OP_IMPLIES,
  OP_NOT,
  OP_OR,
  OP_XOR,

  /* Arrays */
  OP_ARRAY_SELECT,
  OP_ARRAY_STORE,

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
  OP_BV_REDAND,
  OP_BV_REDOR,
  OP_BV_SADDO,
  OP_BV_SDIV,
  OP_BV_SDIVO,
  OP_BV_SGE,
  OP_BV_SGT,
  OP_BV_SHL,
  OP_BV_SLE,
  OP_BV_SLT,
  OP_BV_SMOD,
  OP_BV_SMULO,
  OP_BV_SREM,
  OP_BV_SSUBO,
  OP_BV_SUB,
  OP_BV_UADDO,
  OP_BV_UDIV,
  OP_BV_UGE,
  OP_BV_UGT,
  OP_BV_ULE,
  OP_BV_ULT,
  OP_BV_UMULO,
  OP_BV_UREM,
  OP_BV_USUBO,
  OP_BV_XNOR,
  OP_BV_XOR,
  OP_BV_INC,
  OP_BV_DEC,
  OP_BV_REDXOR,

  /* FP */
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
  OP_FP_TO_FP_FROM_BV,
  OP_FP_TO_FP_FRON_INT_BV,
  OP_FP_TO_FP_FROM_FP,
  OP_FP_TO_FP_FROM_UINT_BV,
  OP_FP_TO_FP_FROM_REAL,
  OP_FP_TO_REAL,
  OP_FP_TO_SBV,
  OP_FP_TO_UBV,

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

  /* The Kind. */
  OpKind d_kind;
  /* The arity of this kind. */
  int32_t d_arity;
  /* The number of parameters if parameterized. */
  uint32_t d_nparams;
  /* The sort kind of a term of this kind. */
  SortKind d_sort_kind;
  /* The theory to which the operator belongs to. */
  TheoryId d_theory;

 private:
  /* The sort kind of the term arguments of this kind. */
  std::vector<SortKind> d_sort_kind_args;
};

#define SMTMBT_OP_TO_STR(kind) \
  {                            \
    kind, #kind                \
  }

static std::unordered_map<OpKind, std::string, OpKindHashFunction>
    op_kinds_to_str{
        SMTMBT_OP_TO_STR(OP_UNDEFINED),

        SMTMBT_OP_TO_STR(OP_ARRAY_SELECT),
        SMTMBT_OP_TO_STR(OP_ARRAY_STORE),

        SMTMBT_OP_TO_STR(OP_AND),
        SMTMBT_OP_TO_STR(OP_DISTINCT),
        SMTMBT_OP_TO_STR(OP_EQUAL),
        SMTMBT_OP_TO_STR(OP_IFF),
        SMTMBT_OP_TO_STR(OP_IMPLIES),
        SMTMBT_OP_TO_STR(OP_ITE),
        SMTMBT_OP_TO_STR(OP_NOT),
        SMTMBT_OP_TO_STR(OP_OR),
        SMTMBT_OP_TO_STR(OP_XOR),

        SMTMBT_OP_TO_STR(OP_BV_EXTRACT),
        SMTMBT_OP_TO_STR(OP_BV_REPEAT),
        SMTMBT_OP_TO_STR(OP_BV_ROTATE_LEFT),
        SMTMBT_OP_TO_STR(OP_BV_ROTATE_RIGHT),
        SMTMBT_OP_TO_STR(OP_BV_SIGN_EXTEND),
        SMTMBT_OP_TO_STR(OP_BV_ZERO_EXTEND),

        SMTMBT_OP_TO_STR(OP_BV_ADD),
        SMTMBT_OP_TO_STR(OP_BV_AND),
        SMTMBT_OP_TO_STR(OP_BV_ASHR),
        SMTMBT_OP_TO_STR(OP_BV_COMP),
        SMTMBT_OP_TO_STR(OP_BV_CONCAT),
        SMTMBT_OP_TO_STR(OP_BV_DEC),
        SMTMBT_OP_TO_STR(OP_BV_INC),
        SMTMBT_OP_TO_STR(OP_BV_LSHR),
        SMTMBT_OP_TO_STR(OP_BV_MULT),
        SMTMBT_OP_TO_STR(OP_BV_NAND),
        SMTMBT_OP_TO_STR(OP_BV_NEG),
        SMTMBT_OP_TO_STR(OP_BV_NOR),
        SMTMBT_OP_TO_STR(OP_BV_NOT),
        SMTMBT_OP_TO_STR(OP_BV_OR),
        SMTMBT_OP_TO_STR(OP_BV_REDAND),
        SMTMBT_OP_TO_STR(OP_BV_REDOR),
        SMTMBT_OP_TO_STR(OP_BV_REDXOR),
        SMTMBT_OP_TO_STR(OP_BV_SADDO),
        SMTMBT_OP_TO_STR(OP_BV_SDIV),
        SMTMBT_OP_TO_STR(OP_BV_SDIVO),
        SMTMBT_OP_TO_STR(OP_BV_SGE),
        SMTMBT_OP_TO_STR(OP_BV_SGT),
        SMTMBT_OP_TO_STR(OP_BV_SHL),
        SMTMBT_OP_TO_STR(OP_BV_SLE),
        SMTMBT_OP_TO_STR(OP_BV_SLT),
        SMTMBT_OP_TO_STR(OP_BV_SMOD),
        SMTMBT_OP_TO_STR(OP_BV_SMULO),
        SMTMBT_OP_TO_STR(OP_BV_SREM),
        SMTMBT_OP_TO_STR(OP_BV_SSUBO),
        SMTMBT_OP_TO_STR(OP_BV_SUB),
        SMTMBT_OP_TO_STR(OP_BV_UADDO),
        SMTMBT_OP_TO_STR(OP_BV_UDIV),
        SMTMBT_OP_TO_STR(OP_BV_UGE),
        SMTMBT_OP_TO_STR(OP_BV_UGT),
        SMTMBT_OP_TO_STR(OP_BV_ULE),
        SMTMBT_OP_TO_STR(OP_BV_ULT),
        SMTMBT_OP_TO_STR(OP_BV_UMULO),
        SMTMBT_OP_TO_STR(OP_BV_UREM),
        SMTMBT_OP_TO_STR(OP_BV_USUBO),
        SMTMBT_OP_TO_STR(OP_BV_XNOR),
        SMTMBT_OP_TO_STR(OP_BV_XOR),

        SMTMBT_OP_TO_STR(OP_FP_ABS),
        SMTMBT_OP_TO_STR(OP_FP_ADD),
        SMTMBT_OP_TO_STR(OP_FP_DIV),
        SMTMBT_OP_TO_STR(OP_FP_EQ),
        SMTMBT_OP_TO_STR(OP_FP_FMA),
        SMTMBT_OP_TO_STR(OP_FP_FP),
        SMTMBT_OP_TO_STR(OP_FP_IS_NORMAL),
        SMTMBT_OP_TO_STR(OP_FP_IS_SUBNORMAL),
        SMTMBT_OP_TO_STR(OP_FP_IS_INF),
        SMTMBT_OP_TO_STR(OP_FP_IS_NAN),
        SMTMBT_OP_TO_STR(OP_FP_IS_NEG),
        SMTMBT_OP_TO_STR(OP_FP_IS_POS),
        SMTMBT_OP_TO_STR(OP_FP_IS_ZERO),
        SMTMBT_OP_TO_STR(OP_FP_LT),
        SMTMBT_OP_TO_STR(OP_FP_LTE),
        SMTMBT_OP_TO_STR(OP_FP_GT),
        SMTMBT_OP_TO_STR(OP_FP_GTE),
        SMTMBT_OP_TO_STR(OP_FP_MAX),
        SMTMBT_OP_TO_STR(OP_FP_MIN),
        SMTMBT_OP_TO_STR(OP_FP_MUL),
        SMTMBT_OP_TO_STR(OP_FP_NEG),
        SMTMBT_OP_TO_STR(OP_FP_REM),
        SMTMBT_OP_TO_STR(OP_FP_RTI),
        SMTMBT_OP_TO_STR(OP_FP_SQRT),
        SMTMBT_OP_TO_STR(OP_FP_SUB),
        SMTMBT_OP_TO_STR(OP_FP_TO_FP_FROM_BV),
        SMTMBT_OP_TO_STR(OP_FP_TO_FP_FRON_INT_BV),
        SMTMBT_OP_TO_STR(OP_FP_TO_FP_FROM_FP),
        SMTMBT_OP_TO_STR(OP_FP_TO_FP_FROM_UINT_BV),
        SMTMBT_OP_TO_STR(OP_FP_TO_FP_FROM_REAL),
        SMTMBT_OP_TO_STR(OP_FP_TO_REAL),
        SMTMBT_OP_TO_STR(OP_FP_TO_SBV),
        SMTMBT_OP_TO_STR(OP_FP_TO_UBV),
    };

std::ostream& operator<<(std::ostream& out, OpKind kind);

OpKind op_kind_from_str(std::string& s);

using OpKindVector = std::vector<OpKind>;
using OpKindSet    = std::unordered_set<OpKind, OpKindHashFunction>;
using OpKindMap    = std::unordered_map<OpKind, Op, OpKindHashFunction>;
using OpKinds = std::unordered_map<SortKind, OpKindVector>;

}  // namespace smtmbt

#endif
