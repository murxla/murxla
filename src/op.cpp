#include "op.hpp"

#include <cstring>
#include <iostream>
#include <sstream>

#include "config.hpp"
#include "except.hpp"
#include "statistics.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

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
const OpKind Op::FP_TO_FP_FROM_SBV     = "OP_FP_TO_FP_FROM_SBV";
const OpKind Op::FP_TO_FP_FROM_FP      = "OP_FP_TO_FP_FROM_FP";
const OpKind Op::FP_TO_FP_FROM_UBV     = "OP_FP_TO_FP_FROM_UBV";
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

/* -------------------------------------------------------------------------- */

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
  MURXLA_CHECK_CONFIG(kind.size() <= MURXLA_MAX_KIND_LEN)
      << "'" << kind
      << "' exceeds maximum length for operator kinds, increase limit by "
         "adjusting value of macro MURXLA_MAX_KIND_LEN in config.hpp";
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

/* -------------------------------------------------------------------------- */

Op&
OpKindManager::get_op(const OpKind& kind)
{
  return d_op_kinds.at(kind);
}

void
OpKindManager::add_op_kinds()
{
  uint32_t n = MURXLA_MK_TERM_N_ARGS_BIN;

  /* Special Cases */
  add_op_kind(Op::DISTINCT, n, 0, SORT_BOOL, {SORT_ANY}, THEORY_BOOL);
  add_op_kind(Op::EQUAL, n, 0, SORT_BOOL, {SORT_ANY}, THEORY_BOOL);
  add_op_kind(
      Op::ITE, 3, 0, SORT_ANY, {SORT_BOOL, SORT_ANY, SORT_ANY}, THEORY_ALL);

  /* Arrays */
  add_op_kind(
      Op::ARRAY_SELECT, 2, 0, SORT_ANY, {SORT_ARRAY, SORT_ANY}, THEORY_ARRAY);
  add_op_kind(Op::ARRAY_STORE,
              3,
              0,
              SORT_ARRAY,
              {SORT_ARRAY, SORT_ANY, SORT_ANY},
              THEORY_ARRAY);

  /* Bool */
  add_op_kind(Op::AND, n, 0, SORT_BOOL, {SORT_BOOL}, THEORY_BOOL);
  add_op_kind(Op::OR, n, 0, SORT_BOOL, {SORT_BOOL}, THEORY_BOOL);
  add_op_kind(Op::NOT, 1, 0, SORT_BOOL, {SORT_BOOL}, THEORY_BOOL);
  add_op_kind(Op::XOR, 2, 0, SORT_BOOL, {SORT_BOOL}, THEORY_BOOL);
  add_op_kind(Op::IMPLIES, n, 0, SORT_BOOL, {SORT_BOOL}, THEORY_BOOL);
  add_op_kind(Op::FORALL, 2, 0, SORT_BOOL, {SORT_ANY, SORT_BOOL}, THEORY_QUANT);
  add_op_kind(Op::EXISTS, 2, 0, SORT_BOOL, {SORT_ANY, SORT_BOOL}, THEORY_QUANT);

  /* BV */
  add_op_kind(Op::BV_CONCAT, n, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_AND, n, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_OR, n, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_XOR, n, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_MULT, n, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_ADD, n, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_NOT, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_NEG, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_ASHR, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_COMP, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_LSHR, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_NAND, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_NOR, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_SDIV, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_SGE, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_SGT, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_SHL, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_SLE, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_SLT, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_SMOD, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_SREM, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_SUB, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_UDIV, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_UGE, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_UGT, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_ULE, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_ULT, 2, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_UREM, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_XNOR, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  // indexed
  add_op_kind(Op::BV_EXTRACT, 1, 2, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_REPEAT, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_ROTATE_LEFT, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_ROTATE_RIGHT, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_SIGN_EXTEND, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  add_op_kind(Op::BV_ZERO_EXTEND, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);

  /* FP */
  add_op_kind(Op::FP_ABS, 1, 0, SORT_FP, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_ADD, 3, 0, SORT_FP, {SORT_RM, SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_DIV, 3, 0, SORT_FP, {SORT_RM, SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_EQ, n, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_FMA, 4, 0, SORT_FP, {SORT_RM, SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_FP, 3, 0, SORT_FP, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_IS_NORMAL, 1, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_IS_SUBNORMAL, 1, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_IS_INF, 1, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_IS_NAN, 1, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_IS_NEG, 1, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_IS_POS, 1, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_IS_ZERO, 1, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_LT, n, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_LEQ, n, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_GT, n, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_GEQ, n, 0, SORT_BOOL, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_MAX, 2, 0, SORT_FP, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_MIN, 2, 0, SORT_FP, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_MUL, 3, 0, SORT_FP, {SORT_RM, SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_NEG, 1, 0, SORT_FP, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_REM, 2, 0, SORT_FP, {SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_RTI, 2, 0, SORT_FP, {SORT_RM, SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_SQRT, 2, 0, SORT_FP, {SORT_RM, SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_SUB, 3, 0, SORT_FP, {SORT_RM, SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_TO_REAL, 1, 0, SORT_REAL, {SORT_FP}, THEORY_FP);
  // indexed
  add_op_kind(Op::FP_TO_FP_FROM_BV, 1, 2, SORT_FP, {SORT_BV}, THEORY_FP);
  add_op_kind(
      Op::FP_TO_FP_FROM_SBV, 2, 2, SORT_FP, {SORT_RM, SORT_BV}, THEORY_FP);
  add_op_kind(
      Op::FP_TO_FP_FROM_FP, 2, 2, SORT_FP, {SORT_RM, SORT_FP}, THEORY_FP);
  add_op_kind(
      Op::FP_TO_FP_FROM_UBV, 2, 2, SORT_FP, {SORT_RM, SORT_BV}, THEORY_FP);
  add_op_kind(
      Op::FP_TO_FP_FROM_REAL, 2, 2, SORT_FP, {SORT_RM, SORT_REAL}, THEORY_FP);
  add_op_kind(Op::FP_TO_SBV, 2, 1, SORT_BV, {SORT_RM, SORT_FP}, THEORY_FP);
  add_op_kind(Op::FP_TO_UBV, 2, 1, SORT_BV, {SORT_RM, SORT_FP}, THEORY_FP);

  /* Ints */
  add_op_kind(Op::INT_IS_INT, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  add_op_kind(Op::INT_NEG, 1, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  add_op_kind(Op::INT_ABS, 1, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  add_op_kind(Op::INT_SUB, n, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  add_op_kind(Op::INT_ADD, n, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  add_op_kind(Op::INT_MUL, n, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  if (!d_arith_linear)
  {
    add_op_kind(Op::INT_DIV, n, 0, SORT_INT, {SORT_INT}, THEORY_INT);
    add_op_kind(Op::INT_MOD, 2, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  }
  add_op_kind(Op::INT_LT, n, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  add_op_kind(Op::INT_LTE, n, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  add_op_kind(Op::INT_GT, n, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  add_op_kind(Op::INT_GTE, n, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  // indexed
  add_op_kind(Op::INT_IS_DIV, 1, 1, SORT_BOOL, {SORT_INT}, THEORY_INT);

  /* Reals */
  add_op_kind(Op::REAL_IS_INT, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  add_op_kind(Op::REAL_NEG, 1, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  add_op_kind(Op::REAL_SUB, n, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  add_op_kind(Op::REAL_ADD, n, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  add_op_kind(Op::REAL_MUL, n, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  if (!d_arith_linear)
  {
    add_op_kind(Op::REAL_DIV, n, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  }
  add_op_kind(Op::REAL_LT, n, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  add_op_kind(Op::REAL_LTE, n, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  add_op_kind(Op::REAL_GT, n, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  add_op_kind(Op::REAL_GTE, n, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);

  /* Strings */
  add_op_kind(Op::STR_CONCAT, n, 0, SORT_STRING, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_LEN, 1, 0, SORT_INT, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_LT, 2, 0, SORT_BOOL, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_TO_RE, 1, 0, SORT_REGLAN, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_CONCAT, n, 0, SORT_STRING, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_LEN, 1, 0, SORT_INT, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_LT, 2, 0, SORT_BOOL, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_TO_RE, 1, 0, SORT_REGLAN, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_IN_RE,
              2,
              0,
              SORT_BOOL,
              {SORT_STRING, SORT_REGLAN},
              THEORY_STRING);
  add_op_kind(Op::RE_CONCAT, n, 0, SORT_REGLAN, {SORT_REGLAN}, THEORY_STRING);
  add_op_kind(Op::RE_UNION, n, 0, SORT_REGLAN, {SORT_REGLAN}, THEORY_STRING);
  add_op_kind(Op::RE_INTER, n, 0, SORT_REGLAN, {SORT_REGLAN}, THEORY_STRING);
  add_op_kind(Op::RE_STAR, 1, 0, SORT_REGLAN, {SORT_REGLAN}, THEORY_STRING);
  add_op_kind(Op::STR_LE, 2, 0, SORT_BOOL, {SORT_STRING}, THEORY_STRING);
  add_op_kind(
      Op::STR_AT, 2, 0, SORT_STRING, {SORT_STRING, SORT_INT}, THEORY_STRING);
  add_op_kind(Op::STR_SUBSTR,
              3,
              0,
              SORT_STRING,
              {SORT_STRING, SORT_INT, SORT_INT},
              THEORY_STRING);
  add_op_kind(Op::STR_PREFIXOF, 2, 0, SORT_BOOL, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_SUFFIXOF, 2, 0, SORT_BOOL, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_CONTAINS, 2, 0, SORT_BOOL, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_INDEXOF,
              3,
              0,
              SORT_INT,
              {SORT_STRING, SORT_STRING, SORT_INT},
              THEORY_STRING);
  add_op_kind(Op::STR_REPLACE, 3, 0, SORT_STRING, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_REPLACE, 3, 0, SORT_STRING, {SORT_STRING}, THEORY_STRING);
  add_op_kind(
      Op::STR_REPLACE_ALL, 3, 0, SORT_STRING, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_REPLACE_RE,
              3,
              0,
              SORT_STRING,
              {SORT_STRING, SORT_REGLAN, SORT_STRING},
              THEORY_STRING);
  add_op_kind(Op::STR_REPLACE_RE_ALL,
              3,
              0,
              SORT_STRING,
              {SORT_STRING, SORT_REGLAN, SORT_STRING},
              THEORY_STRING);
  add_op_kind(Op::RE_COMP, 1, 0, SORT_REGLAN, {SORT_REGLAN}, THEORY_STRING);
  add_op_kind(Op::RE_DIFF, n, 0, SORT_REGLAN, {SORT_REGLAN}, THEORY_STRING);
  add_op_kind(Op::RE_PLUS, 1, 0, SORT_REGLAN, {SORT_REGLAN}, THEORY_STRING);
  add_op_kind(Op::RE_OPT, 1, 0, SORT_REGLAN, {SORT_REGLAN}, THEORY_STRING);
  add_op_kind(Op::RE_RANGE, 2, 0, SORT_REGLAN, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_IS_DIGIT, 1, 0, SORT_BOOL, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_TO_CODE, 1, 0, SORT_INT, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_FROM_CODE, 1, 0, SORT_STRING, {SORT_INT}, THEORY_STRING);
  add_op_kind(Op::STR_TO_INT, 1, 0, SORT_INT, {SORT_STRING}, THEORY_STRING);
  add_op_kind(Op::STR_FROM_INT, 1, 0, SORT_STRING, {SORT_INT}, THEORY_STRING);
  // indexed
  add_op_kind(Op::RE_POW, 1, 1, SORT_REGLAN, {SORT_REGLAN}, THEORY_STRING);
  add_op_kind(Op::RE_LOOP, 1, 2, SORT_REGLAN, {SORT_REGLAN}, THEORY_STRING);

  /* UF */
  add_op_kind(Op::UF_APPLY, n, 0, SORT_ANY, {SORT_FUN, SORT_ANY}, THEORY_UF);
}

void
OpKindManager::add_op_kind(const OpKind& kind,
                           int32_t arity,
                           uint32_t nparams,
                           SortKind sort_kind,
                           const std::vector<SortKind>& sort_kind_args,
                           TheoryId theory)
{
  if (d_disabled_op_kinds.find(kind) == d_disabled_op_kinds.end()
      && (theory == THEORY_ALL
          || d_enabled_theories.find(theory) != d_enabled_theories.end()))
  {
    uint64_t id = d_op_kinds.size();
    if (id >= MURXLA_MAX_N_OPS)
    {
      throw MurxlaException(
          "maximum number of operators exceeded, increase limit by adjusting "
          "value of macro MURXLA_MAX_N_OPS in config.hpp");
    }
    d_op_kinds.emplace(
        kind, Op(id, kind, arity, nparams, sort_kind, sort_kind_args, theory));
    strncpy(d_stats->d_op_kinds[id], kind.c_str(), kind.size());
  }
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla
