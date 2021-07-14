#ifndef __MURXLA__OP_H
#define __MURXLA__OP_H

#include <cassert>
#include <cstdint>
#include <unordered_map>
#include <vector>

#include "sort.hpp"

namespace murxla {

namespace statistics {
struct Statistics;
}

/* -------------------------------------------------------------------------- */

using OpKind = std::string;

/* -------------------------------------------------------------------------- */

struct Op
{
  static const OpKind UNDEFINED;
  /* Special cases */
  static const OpKind DISTINCT;
  static const OpKind EQUAL;
  static const OpKind ITE;
  /* Arrays */
  static const OpKind ARRAY_SELECT;
  static const OpKind ARRAY_STORE;
  /* Boolean */
  static const OpKind AND;
  static const OpKind IFF;
  static const OpKind IMPLIES;
  static const OpKind NOT;
  static const OpKind OR;
  static const OpKind XOR;
  /* BV */
  static const OpKind BV_EXTRACT;
  static const OpKind BV_REPEAT;
  static const OpKind BV_ROTATE_LEFT;
  static const OpKind BV_ROTATE_RIGHT;
  static const OpKind BV_SIGN_EXTEND;
  static const OpKind BV_ZERO_EXTEND;
  static const OpKind BV_ADD;
  static const OpKind BV_AND;
  static const OpKind BV_ASHR;
  static const OpKind BV_COMP;
  static const OpKind BV_CONCAT;
  static const OpKind BV_LSHR;
  static const OpKind BV_MULT;
  static const OpKind BV_NAND;
  static const OpKind BV_NEG;
  static const OpKind BV_NOR;
  static const OpKind BV_NOT;
  static const OpKind BV_OR;
  static const OpKind BV_SDIV;
  static const OpKind BV_SGE;
  static const OpKind BV_SGT;
  static const OpKind BV_SHL;
  static const OpKind BV_SLE;
  static const OpKind BV_SLT;
  static const OpKind BV_SMOD;
  static const OpKind BV_SREM;
  static const OpKind BV_SUB;
  static const OpKind BV_UDIV;
  static const OpKind BV_UGE;
  static const OpKind BV_UGT;
  static const OpKind BV_ULE;
  static const OpKind BV_ULT;
  static const OpKind BV_UREM;
  static const OpKind BV_XNOR;
  static const OpKind BV_XOR;
  /* FP */
  static const OpKind FP_TO_FP_FROM_BV;
  static const OpKind FP_TO_FP_FROM_SBV;
  static const OpKind FP_TO_FP_FROM_FP;
  static const OpKind FP_TO_FP_FROM_UBV;
  static const OpKind FP_TO_FP_FROM_REAL;
  static const OpKind FP_TO_SBV;
  static const OpKind FP_TO_UBV;
  static const OpKind FP_ABS;
  static const OpKind FP_ADD;
  static const OpKind FP_DIV;
  static const OpKind FP_EQ;
  static const OpKind FP_FMA;
  static const OpKind FP_FP;
  static const OpKind FP_IS_NORMAL;
  static const OpKind FP_IS_SUBNORMAL;
  static const OpKind FP_IS_INF;
  static const OpKind FP_IS_NAN;
  static const OpKind FP_IS_NEG;
  static const OpKind FP_IS_POS;
  static const OpKind FP_IS_ZERO;
  static const OpKind FP_LT;
  static const OpKind FP_LEQ;
  static const OpKind FP_GT;
  static const OpKind FP_GEQ;
  static const OpKind FP_MAX;
  static const OpKind FP_MIN;
  static const OpKind FP_MUL;
  static const OpKind FP_NEG;
  static const OpKind FP_REM;
  static const OpKind FP_RTI;
  static const OpKind FP_SQRT;
  static const OpKind FP_SUB;
  static const OpKind FP_TO_REAL;
  /* Ints */
  static const OpKind INT_IS_DIV;
  static const OpKind INT_IS_INT;
  static const OpKind INT_NEG;
  static const OpKind INT_SUB;
  static const OpKind INT_ADD;
  static const OpKind INT_MUL;
  static const OpKind INT_DIV;
  static const OpKind INT_MOD;
  static const OpKind INT_ABS;
  static const OpKind INT_LT;
  static const OpKind INT_LTE;
  static const OpKind INT_GT;
  static const OpKind INT_GTE;
  /* Reals */
  static const OpKind REAL_IS_INT;
  static const OpKind REAL_NEG;
  static const OpKind REAL_SUB;
  static const OpKind REAL_ADD;
  static const OpKind REAL_MUL;
  static const OpKind REAL_DIV;
  static const OpKind REAL_LT;
  static const OpKind REAL_LTE;
  static const OpKind REAL_GT;
  static const OpKind REAL_GTE;
  /* Quantifiers */
  static const OpKind FORALL;
  static const OpKind EXISTS;
  /* Strings */
  static const OpKind RE_COMP;
  static const OpKind RE_CONCAT;
  static const OpKind RE_DIFF;
  static const OpKind RE_INTER;
  static const OpKind RE_LOOP;
  static const OpKind RE_OPT;
  static const OpKind RE_PLUS;
  static const OpKind RE_POW;
  static const OpKind RE_RANGE;
  static const OpKind RE_STAR;
  static const OpKind RE_UNION;
  static const OpKind STR_AT;
  static const OpKind STR_CONCAT;
  static const OpKind STR_CONTAINS;
  static const OpKind STR_FROM_CODE;
  static const OpKind STR_FROM_INT;
  static const OpKind STR_INDEXOF;
  static const OpKind STR_IN_RE;
  static const OpKind STR_IS_DIGIT;
  static const OpKind STR_LE;
  static const OpKind STR_LEN;
  static const OpKind STR_LT;
  static const OpKind STR_PREFIXOF;
  static const OpKind STR_REPLACE;
  static const OpKind STR_REPLACE_ALL;
  static const OpKind STR_REPLACE_RE;
  static const OpKind STR_REPLACE_RE_ALL;
  static const OpKind STR_SUBSTR;
  static const OpKind STR_SUFFIXOF;
  static const OpKind STR_TO_CODE;
  static const OpKind STR_TO_INT;
  static const OpKind STR_TO_RE;
  /* UF */
  static const OpKind UF_APPLY;

  Op(uint64_t id,
     const OpKind& kind,
     int32_t arity,
     uint32_t nparams,
     SortKind sort_kind,
     const std::vector<SortKind>& sort_kind_args,
     TheoryId theory);

  bool operator==(const Op& other) const;

  SortKind get_arg_sort_kind(size_t i) const;

  /* Op id, assigned in the order they have been created. */
  uint64_t d_id = 0u;
  /** The Kind. */
  const OpKind& d_kind = UNDEFINED;
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

/* -------------------------------------------------------------------------- */

using OpKindVector = std::vector<OpKind>;
using OpKindSet    = std::unordered_set<OpKind>;
using OpKindMap    = std::unordered_map<OpKind, Op>;
using OpKinds = std::unordered_map<SortKind, OpKindVector>;

/* -------------------------------------------------------------------------- */

/**
 * The OpKind Manager.
 *
 * Maintains the current set of operator kinds, based on enabled theories
 * and unsupported operator kinds.
 */
class OpKindManager
{
 public:
  /** Constructor. */
  OpKindManager(const TheoryIdSet& enabled_theories,
                const OpKindSet& disabled_op_kinds,
                bool arith_linear,
                statistics::Statistics* stats)
      : d_enabled_theories(enabled_theories),
        d_disabled_op_kinds(disabled_op_kinds),
        d_arith_linear(arith_linear),
        d_stats(stats)
  {
    add_op_kinds();
  }

  /** Get operator of given kind. */
  Op& get_op(const OpKind& kind);

  /**
   * Add operator kind to operator kinds database.
   * kind           : The operator kind
   * arity          : The arity of the operator
   * nparams        : The number of parameters of the operator
   * sort_kind      : The sort kind of the operator
   * sort_kind_args : A vector of sorts of the operators' arguments. if all or
   *                  the remaining kinds are the same, it's sufficient to only
   *                  list it once.
   */
  void add_op_kind(const OpKind& kind,
                   int32_t arity,
                   uint32_t nparams,
                   SortKind sort_kind,
                   const std::vector<SortKind>& sort_kind_args,
                   TheoryId theory);

  const OpKindMap& get_op_kinds() { return d_op_kinds; }

 private:
  /**
   * Populate operator kinds database with enabled operator kinds.
   * Operator kinds are enabled based on the set of enabled theories.
   */
  void add_op_kinds();
  /** The set of enabled operator kinds. Maps OpKind to Op. */
  OpKindMap d_op_kinds;
  /** The set of enabled theories. */
  TheoryIdSet d_enabled_theories;
  /** The set of disabled operator kinds. */
  OpKindSet d_disabled_op_kinds;
  /** True to restrict arithmetic operators to linear fragment. */
  bool d_arith_linear = false;
  /** Statistics. */
  statistics::Statistics* d_stats;
};

/* -------------------------------------------------------------------------- */
}  // namespace murxla

#endif
