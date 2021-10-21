#include "op.hpp"

#include <cstring>
#include <iostream>
#include <sstream>

#include "config.hpp"
#include "except.hpp"
#include "statistics.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

Op::Op(uint64_t id,
       const Kind& kind,
       int32_t arity,
       uint32_t nparams,
       SortKindSet sort_kinds,
       const std::vector<SortKindSet>& sort_kinds_args,
       TheoryId theory)
    : d_id(id),
      d_kind(kind),
      d_arity(arity),
      d_nparams(nparams),
      d_sort_kinds(sort_kinds),
      d_theory(theory),
      d_sort_kinds_args(sort_kinds_args)
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
      || d_sort_kinds != other.d_sort_kinds)
    return false;

  if (d_sort_kinds_args.size() != other.d_sort_kinds_args.size()) return false;

  for (size_t i = 0, size = d_sort_kinds_args.size(); i < size; ++i)
  {
    if (d_sort_kinds_args[i] != other.d_sort_kinds_args[i]) return false;
  }
  return true;
}

SortKindSet
Op::get_arg_sort_kind(size_t i) const
{
  if (i >= d_sort_kinds_args.size())
  {
    /* All remaining arguments have the same sort, except for some operators in
     * theory of FP, where some FP operators have one RM and the remainder FP
     * arguments. All FP arguments have the same sort, and the RM argument
     * always comes first. */
    SortKindSet rm{SORT_RM};
    assert(d_sort_kinds_args[0] != rm || d_sort_kinds_args.size() > 1);
    return d_sort_kinds_args[0] == rm ? d_sort_kinds_args[1]
                                      : d_sort_kinds_args[0];
  }
  return d_sort_kinds_args[i];
}

/* -------------------------------------------------------------------------- */

Op&
OpKindManager::get_op(const Op::Kind& kind)
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
OpKindManager::add_op_kind(const Op::Kind& kind,
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

    SortKindSet exclude_sort_kinds;
    const auto& it = d_unsupported_op_kind_sorts.find(kind);
    if (it != d_unsupported_op_kind_sorts.end())
    {
      exclude_sort_kinds = it->second;
    }

    SortKindSet sort_kinds;
    if (sort_kind == SORT_ANY)
    {
      sort_kinds = get_all_sort_kinds_for_any(exclude_sort_kinds);
    }
    else
    {
      sort_kinds.insert(sort_kind);
    }
    std::vector<SortKindSet> sort_kinds_args;
    for (SortKind s : sort_kind_args)
    {
      SortKindSet sk;
      if (s == SORT_ANY)
      {
        sk = get_all_sort_kinds_for_any(exclude_sort_kinds);
      }
      else
      {
        sk.insert(s);
      }
      sort_kinds_args.push_back(sk);
    }
    d_op_kinds.emplace(
        kind,
        Op(id, kind, arity, nparams, sort_kinds, sort_kinds_args, theory));
    strncpy(d_stats->d_op_kinds[id], kind.c_str(), kind.size());
  }
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla
