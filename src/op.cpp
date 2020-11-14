#include "op.hpp"

#include <iostream>
#include <sstream>

#include "config.hpp"
#include "except.hpp"

namespace smtmbt {

const OpKind Op::UNDEFINED = "OP_UNDEFINED";
/* Special cases */
const OpKind Op::DISTINCT = "OP_DISTINCT";
const OpKind Op::EQUAL    = "OP_EQUAL";
const OpKind Op::ITE      = "OP_ITE";
/* Arrays */
const OpKind Op::ARRAY_SELECT = "OP_ARRAY_SELECT";
const OpKind Op::ARRAY_STORE  = "OP_ARRAY_STORE";
/* Boolean */
const OpKind Op::AND     = "OP_AND";
const OpKind Op::IFF     = "OP_IFF";
const OpKind Op::IMPLIES = "OP_IMPLIES";
const OpKind Op::NOT     = "OP_NOT";
const OpKind Op::OR      = "OP_OR";
const OpKind Op::XOR     = "OP_XOR";
/* BV */
const OpKind Op::BV_EXTRACT      = "OP_BV_EXTRACT";
const OpKind Op::BV_REPEAT       = "OP_BV_REPEAT";
const OpKind Op::BV_ROTATE_LEFT  = "OP_BV_ROTATE_LEFT";
const OpKind Op::BV_ROTATE_RIGHT = "OP_BV_ROTATE_RIGHT";
const OpKind Op::BV_SIGN_EXTEND  = "OP_BV_SIGN_EXTEND";
const OpKind Op::BV_ZERO_EXTEND  = "OP_BV_ZERO_EXTEND";
const OpKind Op::BV_ADD          = "OP_BV_ADD";
const OpKind Op::BV_AND          = "OP_BV_AND";
const OpKind Op::BV_ASHR         = "OP_BV_ASHR";
const OpKind Op::BV_COMP         = "OP_BV_COMP";
const OpKind Op::BV_CONCAT       = "OP_BV_CONCAT";
const OpKind Op::BV_LSHR         = "OP_BV_LSHR";
const OpKind Op::BV_MULT         = "OP_BV_MULT";
const OpKind Op::BV_NAND         = "OP_BV_NAND";
const OpKind Op::BV_NEG          = "OP_BV_NEG";
const OpKind Op::BV_NOR          = "OP_BV_NOR";
const OpKind Op::BV_NOT          = "OP_BV_NOT";
const OpKind Op::BV_OR           = "OP_BV_OR";
const OpKind Op::BV_SDIV         = "OP_BV_SDIV";
const OpKind Op::BV_SGE          = "OP_BV_SGE";
const OpKind Op::BV_SGT          = "OP_BV_SGT";
const OpKind Op::BV_SHL          = "OP_BV_SHL";
const OpKind Op::BV_SLE          = "OP_BV_SLE";
const OpKind Op::BV_SLT          = "OP_BV_SLT";
const OpKind Op::BV_SMOD         = "OP_BV_SMOD";
const OpKind Op::BV_SREM         = "OP_BV_SREM";
const OpKind Op::BV_SUB          = "OP_BV_SUB";
const OpKind Op::BV_UDIV         = "OP_BV_UDIV";
const OpKind Op::BV_UGE          = "OP_BV_UGE";
const OpKind Op::BV_UGT          = "OP_BV_UGT";
const OpKind Op::BV_ULE          = "OP_BV_ULE";
const OpKind Op::BV_ULT          = "OP_BV_ULT";
const OpKind Op::BV_UREM         = "OP_BV_UREM";
const OpKind Op::BV_XNOR         = "OP_BV_XNOR";
const OpKind Op::BV_XOR          = "OP_BV_XOR";
/* FP */
const OpKind Op::FP_TO_FP_FROM_BV      = "OP_FP_TO_FP_FROM_BV";
const OpKind Op::FP_TO_FP_FROM_INT_BV  = "OP_FP_TO_FP_FROM_INT_BV";
const OpKind Op::FP_TO_FP_FROM_FP      = "OP_FP_TO_FP_FROM_FP";
const OpKind Op::FP_TO_FP_FROM_UINT_BV = "OP_FP_TO_FP_FROM_UINT_BV";
const OpKind Op::FP_TO_FP_FROM_REAL    = "OP_FP_TO_FP_FROM_REAL";
const OpKind Op::FP_TO_SBV             = "OP_FP_TO_SBV";
const OpKind Op::FP_TO_UBV             = "OP_FP_TO_UBV";
const OpKind Op::FP_ABS                = "OP_FP_ABS";
const OpKind Op::FP_ADD                = "OP_FP_ADD";
const OpKind Op::FP_DIV                = "OP_FP_DIV";
const OpKind Op::FP_EQ                 = "OP_FP_EQ";
const OpKind Op::FP_FMA                = "OP_FP_FMA";
const OpKind Op::FP_FP                 = "OP_FP_FP";
const OpKind Op::FP_IS_NORMAL          = "OP_FP_IS_NORMAL";
const OpKind Op::FP_IS_SUBNORMAL       = "OP_FP_IS_SUBNORMAL";
const OpKind Op::FP_IS_INF             = "OP_FP_IS_INF";
const OpKind Op::FP_IS_NAN             = "OP_FP_IS_NAN";
const OpKind Op::FP_IS_NEG             = "OP_FP_IS_NEG";
const OpKind Op::FP_IS_POS             = "OP_FP_IS_POS";
const OpKind Op::FP_IS_ZERO            = "OP_FP_IS_ZERO";
const OpKind Op::FP_LT                 = "OP_FP_LT";
const OpKind Op::FP_LEQ                = "OP_FP_LEQ";
const OpKind Op::FP_GT                 = "OP_FP_GT";
const OpKind Op::FP_GEQ                = "OP_FP_GEQ";
const OpKind Op::FP_MAX                = "OP_FP_MAX";
const OpKind Op::FP_MIN                = "OP_FP_MIN";
const OpKind Op::FP_MUL                = "OP_FP_MUL";
const OpKind Op::FP_NEG                = "OP_FP_NEG";
const OpKind Op::FP_REM                = "OP_FP_REM";
const OpKind Op::FP_RTI                = "OP_FP_RTI";
const OpKind Op::FP_SQRT               = "OP_FP_SQRT";
const OpKind Op::FP_SUB                = "OP_FP_SUB";
const OpKind Op::FP_TO_REAL            = "OP_FP_TO_REAL";
/* Ints */
const OpKind Op::INT_IS_DIV = "OP_INT_IS_DIV";
const OpKind Op::INT_IS_INT = "OP_INT_IS_INT";
const OpKind Op::INT_NEG    = "OP_INT_NEG";
const OpKind Op::INT_SUB    = "OP_INT_SUB";
const OpKind Op::INT_ADD    = "OP_INT_ADD";
const OpKind Op::INT_MUL    = "OP_INT_MUL";
const OpKind Op::INT_DIV    = "OP_INT_DIV";
const OpKind Op::INT_MOD    = "OP_INT_MOD";
const OpKind Op::INT_ABS    = "OP_INT_ABS";
const OpKind Op::INT_LT     = "OP_INT_LT";
const OpKind Op::INT_LTE    = "OP_INT_LTE";
const OpKind Op::INT_GT     = "OP_INT_GT";
const OpKind Op::INT_GTE    = "OP_INT_GTE";
/* Reals */
const OpKind Op::REAL_IS_INT = "OP_REAL_IS_INT";
const OpKind Op::REAL_NEG    = "OP_REAL_NEG";
const OpKind Op::REAL_SUB    = "OP_REAL_SUB";
const OpKind Op::REAL_ADD    = "OP_REAL_ADD";
const OpKind Op::REAL_MUL    = "OP_REAL_MUL";
const OpKind Op::REAL_DIV    = "OP_REAL_DIV";
const OpKind Op::REAL_LT     = "OP_REAL_LT";
const OpKind Op::REAL_LTE    = "OP_REAL_LTE";
const OpKind Op::REAL_GT     = "OP_REAL_GT";
const OpKind Op::REAL_GTE    = "OP_REAL_GTE";
/* Quantifiers */
const OpKind Op::FORALL = "OP_FORALL";
const OpKind Op::EXISTS = "OP_EXISTS";
/* Strings */
const OpKind Op::RE_COMP            = "OP_RE_COMP";
const OpKind Op::RE_CONCAT          = "OP_RE_CONCAT";
const OpKind Op::RE_DIFF            = "OP_RE_DIFF";
const OpKind Op::RE_INTER           = "OP_RE_INTER";
const OpKind Op::RE_LOOP            = "OP_RE_LOOP";
const OpKind Op::RE_OPT             = "OP_RE_OPT";
const OpKind Op::RE_PLUS            = "OP_RE_PLUS";
const OpKind Op::RE_POW             = "OP_RE_POW";
const OpKind Op::RE_RANGE           = "OP_RE_RANGE";
const OpKind Op::RE_STAR            = "OP_RE_STAR";
const OpKind Op::RE_UNION           = "OP_RE_UNION";
const OpKind Op::STR_AT             = "OP_STR_";
const OpKind Op::STR_CONCAT         = "OP_STR_CONCAT";
const OpKind Op::STR_CONTAINS       = "OP_STR_CONTAINS";
const OpKind Op::STR_FROM_CODE      = "OP_STR_FROM_CODE";
const OpKind Op::STR_FROM_INT       = "OP_STR_FROM_INT";
const OpKind Op::STR_INDEXOF        = "OP_STR_INDEXOF";
const OpKind Op::STR_IN_RE          = "OP_STR_IN_RE";
const OpKind Op::STR_IS_DIGIT       = "OP_STR_IS_DIGIT";
const OpKind Op::STR_LE             = "OP_STR_";
const OpKind Op::STR_LEN            = "OP_STR_LEN";
const OpKind Op::STR_LT             = "OP_STR_LT";
const OpKind Op::STR_PREFIXOF       = "OP_STR_PREFIXOF";
const OpKind Op::STR_REPLACE        = "OP_STR_REPLACE";
const OpKind Op::STR_REPLACE_ALL    = "OP_STR_REPLACE_ALL";
const OpKind Op::STR_REPLACE_RE     = "OP_STR_REPLACE_RE";
const OpKind Op::STR_REPLACE_RE_ALL = "OP_STR_REPLACE_RE_ALL";
const OpKind Op::STR_SUBSTR         = "OP_STR_SUBSTR";
const OpKind Op::STR_SUFFIXOF       = "OP_STR_SUFFIXOF";
const OpKind Op::STR_TO_CODE        = "OP_STR_TO_CODE";
const OpKind Op::STR_TO_INT         = "OP_STR_TO_INT";
const OpKind Op::STR_TO_RE          = "OP_STR_TO_RE";
/* UF */
const OpKind Op::UF_APPLY = "OP_UF_APPLY";

Op::Op(uint64_t id,
       const OpKind& kind,
       int32_t arity,
       uint32_t nparams,
       SortKind sort_kind,
       const std::vector<SortKind>& sort_kind_args,
       TheoryId theory)
    : d_id(id),
      d_kind(kind),
      d_arity(arity),
      d_nparams(nparams),
      d_sort_kind(sort_kind),
      d_theory(theory),
      d_sort_kind_args(sort_kind_args)
{
  SMTMBT_CHECK_CONFIG(kind.size() <= SMTMBT_MAX_KIND_LEN)
      << "'" << kind
      << "' exceeds maximum length for operator kinds, increase limit by "
         "adjusting value of macro SMTMBT_MAX_KIND_LEN in config.hpp";
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

}  // namespace smtmbt
