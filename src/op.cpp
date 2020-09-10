#include "op.hpp"
#include <iostream>

namespace smtmbt {

#define SMTMBT_OP_TO_STR(kind) \
  {                            \
    kind, #kind                \
  }

std::unordered_map<OpKind, std::string, OpKindHashFunction> op_kinds_to_str = {
    SMTMBT_OP_TO_STR(OP_UNDEFINED),

    /* Special Cases */
    SMTMBT_OP_TO_STR(OP_DISTINCT),
    SMTMBT_OP_TO_STR(OP_EQUAL),
    SMTMBT_OP_TO_STR(OP_ITE),

    /* Arrays */
    SMTMBT_OP_TO_STR(OP_ARRAY_SELECT),
    SMTMBT_OP_TO_STR(OP_ARRAY_STORE),

    /* Boolean */
    SMTMBT_OP_TO_STR(OP_AND),
    SMTMBT_OP_TO_STR(OP_IFF),
    SMTMBT_OP_TO_STR(OP_IMPLIES),
    SMTMBT_OP_TO_STR(OP_NOT),
    SMTMBT_OP_TO_STR(OP_OR),
    SMTMBT_OP_TO_STR(OP_XOR),

    /* BV */
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
    SMTMBT_OP_TO_STR(OP_BV_LSHR),
    SMTMBT_OP_TO_STR(OP_BV_MULT),
    SMTMBT_OP_TO_STR(OP_BV_NAND),
    SMTMBT_OP_TO_STR(OP_BV_NEG),
    SMTMBT_OP_TO_STR(OP_BV_NOR),
    SMTMBT_OP_TO_STR(OP_BV_NOT),
    SMTMBT_OP_TO_STR(OP_BV_OR),
    SMTMBT_OP_TO_STR(OP_BV_SDIV),
    SMTMBT_OP_TO_STR(OP_BV_SGE),
    SMTMBT_OP_TO_STR(OP_BV_SGT),
    SMTMBT_OP_TO_STR(OP_BV_SHL),
    SMTMBT_OP_TO_STR(OP_BV_SLE),
    SMTMBT_OP_TO_STR(OP_BV_SLT),
    SMTMBT_OP_TO_STR(OP_BV_SMOD),
    SMTMBT_OP_TO_STR(OP_BV_SREM),
    SMTMBT_OP_TO_STR(OP_BV_SUB),
    SMTMBT_OP_TO_STR(OP_BV_UDIV),
    SMTMBT_OP_TO_STR(OP_BV_UGE),
    SMTMBT_OP_TO_STR(OP_BV_UGT),
    SMTMBT_OP_TO_STR(OP_BV_ULE),
    SMTMBT_OP_TO_STR(OP_BV_ULT),
    SMTMBT_OP_TO_STR(OP_BV_UREM),
    SMTMBT_OP_TO_STR(OP_BV_XNOR),
    SMTMBT_OP_TO_STR(OP_BV_XOR),

    /* FP */
    SMTMBT_OP_TO_STR(OP_FP_TO_FP_FROM_BV),
    SMTMBT_OP_TO_STR(OP_FP_TO_FP_FROM_INT_BV),
    SMTMBT_OP_TO_STR(OP_FP_TO_FP_FROM_FP),
    SMTMBT_OP_TO_STR(OP_FP_TO_FP_FROM_UINT_BV),
    SMTMBT_OP_TO_STR(OP_FP_TO_FP_FROM_REAL),
    SMTMBT_OP_TO_STR(OP_FP_TO_SBV),
    SMTMBT_OP_TO_STR(OP_FP_TO_UBV),

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
    SMTMBT_OP_TO_STR(OP_FP_TO_REAL),

    /* Ints */
    SMTMBT_OP_TO_STR(OP_INT_IS_DIV),
    SMTMBT_OP_TO_STR(OP_INT_IS_INT),
    SMTMBT_OP_TO_STR(OP_INT_NEG),
    SMTMBT_OP_TO_STR(OP_INT_SUB),
    SMTMBT_OP_TO_STR(OP_INT_ADD),
    SMTMBT_OP_TO_STR(OP_INT_MUL),
    SMTMBT_OP_TO_STR(OP_INT_DIV),
    SMTMBT_OP_TO_STR(OP_INT_MOD),
    SMTMBT_OP_TO_STR(OP_INT_ABS),
    SMTMBT_OP_TO_STR(OP_INT_LT),
    SMTMBT_OP_TO_STR(OP_INT_LTE),
    SMTMBT_OP_TO_STR(OP_INT_GT),
    SMTMBT_OP_TO_STR(OP_INT_GTE),

    /* Reals */
    SMTMBT_OP_TO_STR(OP_REAL_IS_INT),
    SMTMBT_OP_TO_STR(OP_REAL_NEG),
    SMTMBT_OP_TO_STR(OP_REAL_SUB),
    SMTMBT_OP_TO_STR(OP_REAL_ADD),
    SMTMBT_OP_TO_STR(OP_REAL_MUL),
    SMTMBT_OP_TO_STR(OP_REAL_DIV),
    SMTMBT_OP_TO_STR(OP_REAL_LT),
    SMTMBT_OP_TO_STR(OP_REAL_LTE),
    SMTMBT_OP_TO_STR(OP_REAL_GT),
    SMTMBT_OP_TO_STR(OP_REAL_GTE),

    /* Quantifiers */
    SMTMBT_OP_TO_STR(OP_FORALL),
    SMTMBT_OP_TO_STR(OP_EXISTS),

    /* Strings */
    SMTMBT_OP_TO_STR(OP_STR_CONCAT),
    SMTMBT_OP_TO_STR(OP_STR_LEN),
    SMTMBT_OP_TO_STR(OP_STR_LT),
    SMTMBT_OP_TO_STR(OP_STR_TO_RE),
    SMTMBT_OP_TO_STR(OP_STR_IN_RE),
    SMTMBT_OP_TO_STR(OP_RE_CONCAT),
    SMTMBT_OP_TO_STR(OP_RE_UNION),
    SMTMBT_OP_TO_STR(OP_RE_INTER),
    SMTMBT_OP_TO_STR(OP_RE_STAR),
    SMTMBT_OP_TO_STR(OP_STR_LE),
    SMTMBT_OP_TO_STR(OP_STR_AT),
    SMTMBT_OP_TO_STR(OP_STR_SUBSTR),
    SMTMBT_OP_TO_STR(OP_STR_PREFIXOF),
    SMTMBT_OP_TO_STR(OP_STR_SUFFIXOF),
    SMTMBT_OP_TO_STR(OP_STR_CONTAINS),
    SMTMBT_OP_TO_STR(OP_STR_INDEXOF),
    SMTMBT_OP_TO_STR(OP_STR_REPLACE),
    SMTMBT_OP_TO_STR(OP_STR_REPLACE_ALL),
    SMTMBT_OP_TO_STR(OP_STR_REPLACE_RE),
    SMTMBT_OP_TO_STR(OP_STR_REPLACE_RE_ALL),
    SMTMBT_OP_TO_STR(OP_RE_COMP),
    SMTMBT_OP_TO_STR(OP_RE_DIFF),
    SMTMBT_OP_TO_STR(OP_RE_PLUS),
    SMTMBT_OP_TO_STR(OP_RE_OPT),
    SMTMBT_OP_TO_STR(OP_RE_RANGE),
    SMTMBT_OP_TO_STR(OP_RE_POW),
    SMTMBT_OP_TO_STR(OP_RE_LOOP),
    SMTMBT_OP_TO_STR(OP_STR_IS_DIGIT),
    SMTMBT_OP_TO_STR(OP_STR_TO_CODE),
    SMTMBT_OP_TO_STR(OP_STR_FROM_CODE),
    SMTMBT_OP_TO_STR(OP_STR_TO_INT),
    SMTMBT_OP_TO_STR(OP_STR_FROM_INT),

    /* UF */
    SMTMBT_OP_TO_STR(OP_UF_APPLY),

    /* Placeholders */
    SMTMBT_OP_TO_STR(OP_EXT_OP_01),
    SMTMBT_OP_TO_STR(OP_EXT_OP_02),
    SMTMBT_OP_TO_STR(OP_EXT_OP_03),
    SMTMBT_OP_TO_STR(OP_EXT_OP_04),
    SMTMBT_OP_TO_STR(OP_EXT_OP_05),
    SMTMBT_OP_TO_STR(OP_EXT_OP_06),
    SMTMBT_OP_TO_STR(OP_EXT_OP_07),
    SMTMBT_OP_TO_STR(OP_EXT_OP_08),
    SMTMBT_OP_TO_STR(OP_EXT_OP_09),
    SMTMBT_OP_TO_STR(OP_EXT_OP_10),
    SMTMBT_OP_TO_STR(OP_EXT_OP_11),
    SMTMBT_OP_TO_STR(OP_EXT_OP_12),
    SMTMBT_OP_TO_STR(OP_EXT_OP_13),
    SMTMBT_OP_TO_STR(OP_EXT_OP_14),
    SMTMBT_OP_TO_STR(OP_EXT_OP_15),
    SMTMBT_OP_TO_STR(OP_EXT_OP_16),
    SMTMBT_OP_TO_STR(OP_EXT_OP_17),
    SMTMBT_OP_TO_STR(OP_EXT_OP_18),
    SMTMBT_OP_TO_STR(OP_EXT_OP_19),
    SMTMBT_OP_TO_STR(OP_EXT_OP_20),
    SMTMBT_OP_TO_STR(OP_EXT_OP_21),
    SMTMBT_OP_TO_STR(OP_EXT_OP_22),
    SMTMBT_OP_TO_STR(OP_EXT_OP_23),
    SMTMBT_OP_TO_STR(OP_EXT_OP_24),
    SMTMBT_OP_TO_STR(OP_EXT_OP_25),
    SMTMBT_OP_TO_STR(OP_EXT_OP_26),
    SMTMBT_OP_TO_STR(OP_EXT_OP_27),
    SMTMBT_OP_TO_STR(OP_EXT_OP_28),
    SMTMBT_OP_TO_STR(OP_EXT_OP_29),
    SMTMBT_OP_TO_STR(OP_EXT_OP_30),
    SMTMBT_OP_TO_STR(OP_EXT_OP_31),
    SMTMBT_OP_TO_STR(OP_EXT_OP_32),
    SMTMBT_OP_TO_STR(OP_EXT_OP_33),
    SMTMBT_OP_TO_STR(OP_EXT_OP_34),
    SMTMBT_OP_TO_STR(OP_EXT_OP_35),
    SMTMBT_OP_TO_STR(OP_EXT_OP_36),
    SMTMBT_OP_TO_STR(OP_EXT_OP_37),
    SMTMBT_OP_TO_STR(OP_EXT_OP_38),
    SMTMBT_OP_TO_STR(OP_EXT_OP_39),
    SMTMBT_OP_TO_STR(OP_EXT_OP_40),
};

void
update_op_kinds_to_str(OpKind kind, std::string string)
{
  assert(op_kinds_to_str.find(kind) != op_kinds_to_str.end());
  op_kinds_to_str.at(kind) = string;
}

std::ostream&
operator<<(std::ostream& out, OpKind kind)
{
  assert(op_kinds_to_str.find(kind) != op_kinds_to_str.end());
  out << op_kinds_to_str.at(kind);
  return out;
}

size_t
OpKindHashFunction::operator()(OpKind kind) const
{
  return kind;
}

bool
Op::operator==(const Op& other) const
{
  if (d_kind != other.d_kind || d_arity != other.d_arity
      || d_sort_kind != other.d_sort_kind)
    return false;

  if (d_sort_kind_args.size() != other.d_sort_kind_args.size()) return false;

  for (size_t i = 0, size = d_sort_kind_args.size(); i < size; ++i)
  {
    if (d_sort_kind_args[i] != other.d_sort_kind_args[i]) return false;
  }
  return true;
}

SortKind
Op::get_arg_sort_kind(size_t i) const
{
  if (i >= d_sort_kind_args.size())
  {
    /* All remaining arguments have the same sort, except for some operators in
     * theory of FP, where some FP operators have one RM and the remainder FP
     * arguments. All FP arguments have the same sort, and the RM argument
     * always comes first. */
    assert(d_sort_kind_args[0] != SORT_RM || d_sort_kind_args.size() > 1);
    return d_sort_kind_args[0] == SORT_RM ? d_sort_kind_args[1]
                                          : d_sort_kind_args[0];
  }
  return d_sort_kind_args[i];
}

OpKind
op_kind_from_str(std::string& s)
{
  for (const auto& p : op_kinds_to_str)
  {
    if (p.second == s)
    {
      return p.first;
    }
  }
  return OP_UNDEFINED;
}

}  // namespace smtmbt

