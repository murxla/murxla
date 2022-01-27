/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
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

struct Op
{
  using Kind = std::string;

  inline static const Kind UNDEFINED = "OP_UNDEFINED";
  inline static const Kind INTERNAL = "OP_INTERNAL";
  /* Leaf kinds (only needed for Term::get_kind) */
  inline static const Kind CONSTANT    = "OP_CONSTANT";
  inline static const Kind CONST_ARRAY = "OP_CONST_ARRAY";
  inline static const Kind VALUE       = "OP_VALUE";
  inline static const Kind VARIABLE    = "OP_VARIABLE";
  inline static const Kind FUN         = "OP_FUN";
  /* Special cases */
  inline static const Kind DISTINCT = "OP_DISTINCT";
  inline static const Kind EQUAL    = "OP_EQUAL";
  inline static const Kind ITE      = "OP_ITE";
  /* Arrays */
  inline static const Kind ARRAY_SELECT = "OP_ARRAY_SELECT";
  inline static const Kind ARRAY_STORE  = "OP_ARRAY_STORE";
  /* Boolean */
  inline static const Kind AND     = "OP_AND";
  inline static const Kind IFF     = "OP_IFF";
  inline static const Kind IMPLIES = "OP_IMPLIES";
  inline static const Kind NOT     = "OP_NOT";
  inline static const Kind OR      = "OP_OR";
  inline static const Kind XOR     = "OP_XOR";
  /* BV */
  inline static const Kind BV_EXTRACT      = "OP_BV_EXTRACT";
  inline static const Kind BV_REPEAT       = "OP_BV_REPEAT";
  inline static const Kind BV_ROTATE_LEFT  = "OP_BV_ROTATE_LEFT";
  inline static const Kind BV_ROTATE_RIGHT = "OP_BV_ROTATE_RIGHT";
  inline static const Kind BV_SIGN_EXTEND  = "OP_BV_SIGN_EXTEND";
  inline static const Kind BV_ZERO_EXTEND  = "OP_BV_ZERO_EXTEND";
  inline static const Kind BV_ADD          = "OP_BV_ADD";
  inline static const Kind BV_AND          = "OP_BV_AND";
  inline static const Kind BV_ASHR         = "OP_BV_ASHR";
  inline static const Kind BV_COMP         = "OP_BV_COMP";
  inline static const Kind BV_CONCAT       = "OP_BV_CONCAT";
  inline static const Kind BV_LSHR         = "OP_BV_LSHR";
  inline static const Kind BV_MULT         = "OP_BV_MULT";
  inline static const Kind BV_NAND         = "OP_BV_NAND";
  inline static const Kind BV_NEG          = "OP_BV_NEG";
  inline static const Kind BV_NOR          = "OP_BV_NOR";
  inline static const Kind BV_NOT          = "OP_BV_NOT";
  inline static const Kind BV_OR           = "OP_BV_OR";
  inline static const Kind BV_SDIV         = "OP_BV_SDIV";
  inline static const Kind BV_SGE          = "OP_BV_SGE";
  inline static const Kind BV_SGT          = "OP_BV_SGT";
  inline static const Kind BV_SHL          = "OP_BV_SHL";
  inline static const Kind BV_SLE          = "OP_BV_SLE";
  inline static const Kind BV_SLT          = "OP_BV_SLT";
  inline static const Kind BV_SMOD         = "OP_BV_SMOD";
  inline static const Kind BV_SREM         = "OP_BV_SREM";
  inline static const Kind BV_SUB          = "OP_BV_SUB";
  inline static const Kind BV_UDIV         = "OP_BV_UDIV";
  inline static const Kind BV_UGE          = "OP_BV_UGE";
  inline static const Kind BV_UGT          = "OP_BV_UGT";
  inline static const Kind BV_ULE          = "OP_BV_ULE";
  inline static const Kind BV_ULT          = "OP_BV_ULT";
  inline static const Kind BV_UREM         = "OP_BV_UREM";
  inline static const Kind BV_XNOR         = "OP_BV_XNOR";
  inline static const Kind BV_XOR          = "OP_BV_XOR";
  /* Datatypes */
  inline static const Kind DT_APPLY_CONS      = "OP_DT_APPLY_CONS";
  inline static const Kind DT_APPLY_SEL       = "OP_DT_APPLY_SEL";
  inline static const Kind DT_APPLY_TESTER    = "OP_DT_APPLY_TESTER";
  inline static const Kind DT_APPLY_UPDATER   = "OP_DT_APPLY_UPDATER";
  inline static const Kind DT_MATCH           = "OP_DT_MATCH";
  inline static const Kind DT_MATCH_CASE      = "OP_DT_MATCH_CASE";
  inline static const Kind DT_MATCH_BIND_CASE = "OP_DT_MATCH_BIND_CASE";
  inline static const Kind DT_TUPLE_PROJECT   = "OP_DT_TUPLE_PROJECT";
  /* FP */
  inline static const Kind FP_TO_FP_FROM_BV   = "OP_FP_TO_FP_FROM_BV";
  inline static const Kind FP_TO_FP_FROM_SBV  = "OP_FP_TO_FP_FROM_SBV";
  inline static const Kind FP_TO_FP_FROM_FP   = "OP_FP_TO_FP_FROM_FP";
  inline static const Kind FP_TO_FP_FROM_UBV  = "OP_FP_TO_FP_FROM_UBV";
  inline static const Kind FP_TO_FP_FROM_REAL = "OP_FP_TO_FP_FROM_REAL";
  inline static const Kind FP_TO_SBV          = "OP_FP_TO_SBV";
  inline static const Kind FP_TO_UBV          = "OP_FP_TO_UBV";
  inline static const Kind FP_ABS             = "OP_FP_ABS";
  inline static const Kind FP_ADD             = "OP_FP_ADD";
  inline static const Kind FP_DIV             = "OP_FP_DIV";
  inline static const Kind FP_EQ              = "OP_FP_EQ";
  inline static const Kind FP_FMA             = "OP_FP_FMA";
  inline static const Kind FP_FP              = "OP_FP_FP";
  inline static const Kind FP_IS_NORMAL       = "OP_FP_IS_NORMAL";
  inline static const Kind FP_IS_SUBNORMAL    = "OP_FP_IS_SUBNORMAL";
  inline static const Kind FP_IS_INF          = "OP_FP_IS_INF";
  inline static const Kind FP_IS_NAN          = "OP_FP_IS_NAN";
  inline static const Kind FP_IS_NEG          = "OP_FP_IS_NEG";
  inline static const Kind FP_IS_POS          = "OP_FP_IS_POS";
  inline static const Kind FP_IS_ZERO         = "OP_FP_IS_ZERO";
  inline static const Kind FP_LT              = "OP_FP_LT";
  inline static const Kind FP_LEQ             = "OP_FP_LEQ";
  inline static const Kind FP_GT              = "OP_FP_GT";
  inline static const Kind FP_GEQ             = "OP_FP_GEQ";
  inline static const Kind FP_MAX             = "OP_FP_MAX";
  inline static const Kind FP_MIN             = "OP_FP_MIN";
  inline static const Kind FP_MUL             = "OP_FP_MUL";
  inline static const Kind FP_NEG             = "OP_FP_NEG";
  inline static const Kind FP_REM             = "OP_FP_REM";
  inline static const Kind FP_RTI             = "OP_FP_RTI";
  inline static const Kind FP_SQRT            = "OP_FP_SQRT";
  inline static const Kind FP_SUB             = "OP_FP_SUB";
  inline static const Kind FP_TO_REAL         = "OP_FP_TO_REAL";
  /* Ints */
  inline static const Kind INT_IS_DIV = "OP_INT_IS_DIV";
  inline static const Kind INT_NEG    = "OP_INT_NEG";
  inline static const Kind INT_SUB    = "OP_INT_SUB";
  inline static const Kind INT_ADD    = "OP_INT_ADD";
  inline static const Kind INT_MUL    = "OP_INT_MUL";
  inline static const Kind INT_DIV    = "OP_INT_DIV";
  inline static const Kind INT_MOD    = "OP_INT_MOD";
  inline static const Kind INT_ABS    = "OP_INT_ABS";
  inline static const Kind INT_LT     = "OP_INT_LT";
  inline static const Kind INT_LTE    = "OP_INT_LTE";
  inline static const Kind INT_GT     = "OP_INT_GT";
  inline static const Kind INT_GTE    = "OP_INT_GTE";
  /* Reals */
  inline static const Kind REAL_NEG    = "OP_REAL_NEG";
  inline static const Kind REAL_SUB    = "OP_REAL_SUB";
  inline static const Kind REAL_ADD    = "OP_REAL_ADD";
  inline static const Kind REAL_MUL    = "OP_REAL_MUL";
  inline static const Kind REAL_DIV    = "OP_REAL_DIV";
  inline static const Kind REAL_LT     = "OP_REAL_LT";
  inline static const Kind REAL_LTE    = "OP_REAL_LTE";
  inline static const Kind REAL_GT     = "OP_REAL_GT";
  inline static const Kind REAL_GTE    = "OP_REAL_GTE";
  /* Reals and Ints */
  inline static const Kind INT_IS_INT  = "OP_INT_IS_INT";
  inline static const Kind INT_TO_REAL = "OP_INT_TO_REAL";
  inline static const Kind REAL_IS_INT = "OP_REAL_IS_INT";
  inline static const Kind REAL_TO_INT = "OP_REAL_TO_INT";
  /* Quantifiers */
  inline static const Kind FORALL = "OP_FORALL";
  inline static const Kind EXISTS = "OP_EXISTS";
  /* Strings */
  inline static const Kind RE_ALL             = "OP_RE_ALL";
  inline static const Kind RE_ALLCHAR         = "OP_RE_ALLCHAR";
  inline static const Kind RE_COMP            = "OP_RE_COMP";
  inline static const Kind RE_CONCAT          = "OP_RE_CONCAT";
  inline static const Kind RE_DIFF            = "OP_RE_DIFF";
  inline static const Kind RE_NONE            = "OP_RE_NONE";
  inline static const Kind RE_INTER           = "OP_RE_INTER";
  inline static const Kind RE_LOOP            = "OP_RE_LOOP";
  inline static const Kind RE_OPT             = "OP_RE_OPT";
  inline static const Kind RE_PLUS            = "OP_RE_PLUS";
  inline static const Kind RE_POW             = "OP_RE_POW";
  inline static const Kind RE_RANGE           = "OP_RE_RANGE";
  inline static const Kind RE_STAR            = "OP_RE_STAR";
  inline static const Kind RE_UNION           = "OP_RE_UNION";
  inline static const Kind STR_AT             = "OP_STR_AT";
  inline static const Kind STR_CONCAT         = "OP_STR_CONCAT";
  inline static const Kind STR_CONTAINS       = "OP_STR_CONTAINS";
  inline static const Kind STR_FROM_CODE      = "OP_STR_FROM_CODE";
  inline static const Kind STR_FROM_INT       = "OP_STR_FROM_INT";
  inline static const Kind STR_INDEXOF        = "OP_STR_INDEXOF";
  inline static const Kind STR_IN_RE          = "OP_STR_IN_RE";
  inline static const Kind STR_IS_DIGIT       = "OP_STR_IS_DIGIT";
  inline static const Kind STR_LE             = "OP_STR_LE";
  inline static const Kind STR_LEN            = "OP_STR_LEN";
  inline static const Kind STR_LT             = "OP_STR_LT";
  inline static const Kind STR_PREFIXOF       = "OP_STR_PREFIXOF";
  inline static const Kind STR_REPLACE        = "OP_STR_REPLACE";
  inline static const Kind STR_REPLACE_ALL    = "OP_STR_REPLACE_ALL";
  inline static const Kind STR_REPLACE_RE     = "OP_STR_REPLACE_RE";
  inline static const Kind STR_REPLACE_RE_ALL = "OP_STR_REPLACE_RE_ALL";
  inline static const Kind STR_SUBSTR         = "OP_STR_SUBSTR";
  inline static const Kind STR_SUFFIXOF       = "OP_STR_SUFFIXOF";
  inline static const Kind STR_TO_CODE        = "OP_STR_TO_CODE";
  inline static const Kind STR_TO_INT         = "OP_STR_TO_INT";
  inline static const Kind STR_TO_RE          = "OP_STR_TO_RE";
  /* Transcendentals */
  inline static const Kind TRANS_PI           = "OP_TRANS_PI";
  inline static const Kind TRANS_SINE         = "OP_TRANS_SINE";
  inline static const Kind TRANS_COSINE       = "OP_TRANS_COSINE";
  inline static const Kind TRANS_TANGENT      = "OP_TRANS_TANGENT";
  inline static const Kind TRANS_COTANGENT    = "OP_TRANS_COTANGENT";
  inline static const Kind TRANS_SECANT       = "OP_TRANS_SECANT";
  inline static const Kind TRANS_COSECANT     = "OP_TRANS_COSECANT";
  inline static const Kind TRANS_ARCSINE      = "OP_TRANS_ARCSINE";
  inline static const Kind TRANS_ARCCOSINE    = "OP_TRANS_ARCCOSINE";
  inline static const Kind TRANS_ARCTANGENT   = "OP_TRANS_ARCTANGENT";
  inline static const Kind TRANS_ARCCOSECANT  = "OP_TRANS_ARCCOSECANT";
  inline static const Kind TRANS_ARCSECANT    = "OP_TRANS_ARCSECANT";
  inline static const Kind TRANS_ARCCOTANGENT = "OP_TRANS_ARCCOTANGENT";
  inline static const Kind TRANS_SQRT         = "OP_TRANS_SQRT";
  /* UF */
  inline static const Kind UF_APPLY = "OP_UF_APPLY";
  /* Operators of non-standardized theories. */
  // Bags
  inline static const Kind BAG_UNION_MAX        = "OP_BAG_UNION_MAX";
  inline static const Kind BAG_UNION_DISJOINT   = "OP_BAG_UNION_DISJOINT";
  inline static const Kind BAG_INTERSECTION_MIN = "OP_BAG_INTERSECTION_MIN";
  inline static const Kind BAG_DIFFERENCE_SUBTRACT =
      "OP_BAG_DIFFERENCE_SUBTRACT";
  inline static const Kind BAG_DIFFERENCE_REMOVE = "OP_BAG_DIFFERENCE_REMOVE";
  inline static const Kind BAG_SUBBAG            = "OP_BAG_SUBBAG";
  inline static const Kind BAG_COUNT             = "OP_BAG_COUNT";
  inline static const Kind BAG_DUPLICATE_REMOVAL = "OP_BAG_DUPLICATE_REMOVAL";
  inline static const Kind BAG_MAKE              = "OP_BAG_MAKE";
  inline static const Kind BAG_EMPTY             = "OP_BAG_EMPTY";
  inline static const Kind BAG_CARD              = "OP_BAG_CARD";
  inline static const Kind BAG_CHOOSE            = "OP_BAG_CHOOSE";
  inline static const Kind BAG_IS_SINGLETON      = "OP_BAG_IS_SINGLETON";
  inline static const Kind BAG_FROM_SET          = "OP_BAG_FROM_SET";
  inline static const Kind BAG_TO_SET            = "OP_BAG_TO_SET";
  inline static const Kind BAG_MAP               = "OP_BAG_MAP";
  // Sequences
  inline static const Kind SEQ_CONCAT      = "OP_SEQ_CONCAT";
  inline static const Kind SEQ_LENGTH      = "OP_SEQ_LENGTH";
  inline static const Kind SEQ_EXTRACT     = "OP_SEQ_EXTRACT";
  inline static const Kind SEQ_UPDATE      = "OP_SEQ_UPDATE";
  inline static const Kind SEQ_AT          = "OP_SEQ_AT";
  inline static const Kind SEQ_CONTAINS    = "OP_SEQ_CONTAINS";
  inline static const Kind SEQ_INDEXOF     = "OP_SEQ_INDEXOF";
  inline static const Kind SEQ_REPLACE     = "OP_SEQ_REPLACE";
  inline static const Kind SEQ_REPLACE_ALL = "OP_SEQ_REPLACE_ALL";
  inline static const Kind SEQ_REV         = "OP_SEQ_REV";
  inline static const Kind SEQ_PREFIX      = "OP_SEQ_PREFIX";
  inline static const Kind SEQ_SUFFIX      = "OP_SEQ_SUFFIX";
  inline static const Kind SEQ_UNIT        = "OP_SEQ_UNIT";
  inline static const Kind SEQ_NTH         = "OP_SEQ_NTH";
  // Sets
  inline static const Kind SET_CARD          = "OP_SET_CARD";
  inline static const Kind SET_COMPLEMENT    = "OP_SET_COMPLEMENT";
  inline static const Kind SET_COMPREHENSION = "OP_SET_COMPREHENSION";
  inline static const Kind SET_CHOOSE        = "OP_SET_CHOOSE";
  inline static const Kind SET_INTERSECTION  = "OP_SET_INTERSECTION";
  inline static const Kind SET_INSERT        = "OP_SET_INSERT";
  inline static const Kind SET_IS_SINGLETON  = "OP_SET_IS_SINGLETON";
  inline static const Kind SET_UNION         = "OP_SET_UNION";
  inline static const Kind SET_MEMBER        = "OP_SET_MEMBER";
  inline static const Kind SET_MINUS         = "OP_SET_MINUS";
  inline static const Kind SET_SINGLETON     = "OP_SET_SINGLETON";
  inline static const Kind SET_SUBSET        = "OP_SET_SUBSET";
  // Relations
  inline static const Kind REL_JOIN       = "OP_REL_JOIN";
  inline static const Kind REL_JOIN_IMAGE = "OP_REL_JOIN_IMAGE";
  inline static const Kind REL_IDEN       = "OP_REL_IDEN";
  inline static const Kind REL_PRODUCT    = "OP_REL_PRODUCT";
  inline static const Kind REL_TCLOSURE   = "OP_REL_TCLOSURE";
  inline static const Kind REL_TRANSPOSE  = "OP_REL_TRANSPOSE";

  Op(uint64_t id,
     const Kind& kind,
     int32_t arity,
     uint32_t nidxs,
     SortKindSet sort_kinds,
     const std::vector<SortKindSet>& sort_kinds_args,
     TheoryId theory);

  bool operator==(const Op& other) const;

  SortKindSet get_arg_sort_kind(size_t i) const;

  /** Op id, assigned in the order they have been created. */
  uint64_t d_id = 0u;
  /** The Kind. */
  const Kind& d_kind = UNDEFINED;
  /** The arity of this kind. */
  int32_t d_arity;
  /** The number of parameters if parameterized. */
  uint32_t d_nidxs;
  /** The sort kind of a term of this kind. */
  SortKindSet d_sort_kinds;
  /** The theory to which the operator belongs to. */
  TheoryId d_theory;

 private:
  /** The sort kind of the term arguments of this kind. */
  std::vector<SortKindSet> d_sort_kinds_args;

};

/* -------------------------------------------------------------------------- */

using OpKindVector = std::vector<Op::Kind>;
using OpKindSet    = std::unordered_set<Op::Kind>;
using OpKindMap    = std::unordered_map<Op::Kind, Op>;
using OpKinds = std::unordered_map<SortKind, OpKindVector>;

/* -------------------------------------------------------------------------- */

/**
 * The operator kind manager.
 *
 * Maintains the current set of operator kinds, based on enabled theories
 * and unsupported operator kinds.
 */
class OpKindManager
{
 public:
  /** Constructor. */
  OpKindManager(const TheoryIdSet& enabled_theories,
                const SortKindMap& enabled_sort_kinds,
                const OpKindSet& disabled_op_kinds,
                const std::unordered_map<Op::Kind, SortKindSet>&
                    unsupported_op_kind_sorts,
                bool arith_linear,
                statistics::Statistics* stats)
      : d_enabled_theories(enabled_theories),
        d_disabled_op_kinds(disabled_op_kinds),
        d_unsupported_op_kind_sorts(unsupported_op_kind_sorts),
        d_arith_linear(arith_linear),
        d_stats(stats),
        d_op_undefined(0u, Op::UNDEFINED, 0, 0, {}, {}, THEORY_ALL)
  {
    for (const auto p : enabled_sort_kinds)
    {
      d_enabled_sort_kinds.insert(p.first);
    }
    add_op_kinds();
  }

  /**
   * Get operator of given kind.
   * Returns a reference to d_op_undefined if the op kind has not been added
   * to the op database.
   */
  Op& get_op(const Op::Kind& kind);

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
  void add_op_kind(const Op::Kind& kind,
                   int32_t arity,
                   uint32_t nparams,
                   SortKind sort_kind,
                   const std::vector<SortKind>& sort_kind_args,
                   TheoryId theory);

  /** Get a map of enabled operator kinds to their corresponding Op. */
  const OpKindMap& get_op_kinds() { return d_op_kinds; }

 private:
  /**
   * Populate operator kinds database with enabled operator kinds.
   * Operator kinds are enabled based on the set of enabled theories.
   */
  void add_op_kinds();
  /** The set of enabled operator kinds. Maps Op::Kind to Op. */
  OpKindMap d_op_kinds;
  /** The set of enabled theories. */
  TheoryIdSet d_enabled_theories;
  /** Enabled sort kinds. */
  SortKindSet d_enabled_sort_kinds;
  /** The set of disabled operator kinds. */
  OpKindSet d_disabled_op_kinds;
  /** The map of unsupported sorts for operator kinds. */
  std::unordered_map<Op::Kind, SortKindSet> d_unsupported_op_kind_sorts;
  /** True to restrict arithmetic operators to linear fragment. */
  bool d_arith_linear = false;
  /** Statistics. */
  statistics::Statistics* d_stats;
  /**
   * Op representing kinds that are defined but not added as operator kind
   * to d_op_kinds, to be returned via get_op(). This is for operators that
   * are explicitly not added to the op kind database because they should not
   * be randomly picked but only created on demand. Examples are DT_MATCH_CASE
   * and DT_MATCH_BIND_CASE. */
  Op d_op_undefined;
};

/* -------------------------------------------------------------------------- */
}  // namespace murxla

#endif
