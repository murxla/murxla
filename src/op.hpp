#ifndef __SMTMBT__OP_H
#define __SMTMBT__OP_H

#include <cstdint>
#include <unordered_map>
#include <vector>

#include "theory.hpp"

namespace smtmbt {

enum OpKind
{
  UNDEFINED,
  DISTINCT,
  EQUAL,
  ITE,

  AND,
  OR,
  NOT,
  XOR,
  IMPLIES,

  BV_EXTRACT,
  BV_REPEAT,
  BV_ROTATE_LEFT,
  BV_ROTATE_RIGHT,
  BV_SIGN_EXTEND,
  BV_ZERO_EXTEND,

  //  BITVECTOR_CONCAT, -1, THEORY_BV, THEORY_BV);
  //  BITVECTOR_AND, -1, THEORY_BV, THEORY_BV);
  //  BITVECTOR_OR, -1, THEORY_BV, THEORY_BV);
  //  BITVECTOR_XOR, -1, THEORY_BV, THEORY_BV);
  //  BITVECTOR_MULT, -1, THEORY_BV, THEORY_BV);
  //  BITVECTOR_PLUS, -1, THEORY_BV, THEORY_BV);
  //  BITVECTOR_NOT, 1, THEORY_BV, THEORY_BV);
  //  BITVECTOR_NEG, 1, THEORY_BV, THEORY_BV);
  //  BITVECTOR_REDOR, 1, THEORY_BOOL, THEORY_BV);
  //  BITVECTOR_REDAND, 1, THEORY_BOOL, THEORY_BV);
  //  BITVECTOR_NAND, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_NOR, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_XNOR, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_COMP, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_SUB, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_UDIV, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_UREM, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_SDIV, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_SREM, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_SMOD, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_UDIV_TOTAL, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_UREM_TOTAL, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_SHL, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_LSHR, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_ASHR, 2, THEORY_BV, THEORY_BV);
  //  BITVECTOR_ULT, 2, THEORY_BOOL, THEORY_BV);
  //  BITVECTOR_ULE, 2, THEORY_BOOL, THEORY_BV);
  //  BITVECTOR_UGT, 2, THEORY_BOOL, THEORY_BV);
  //  BITVECTOR_UGE, 2, THEORY_BOOL, THEORY_BV);
  //  BITVECTOR_SLT, 2, THEORY_BOOL, THEORY_BV);
  //  BITVECTOR_SLE, 2, THEORY_BOOL, THEORY_BV);
  //  BITVECTOR_SGT, 2, THEORY_BOOL, THEORY_BV);
  //  BITVECTOR_SGE, 2, THEORY_BOOL, THEORY_BV);
  //  // SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_ULTBV, 2, THEORY_BV,
  //  THEORY_BV);
  //  // SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SLTBV, 2, THEORY_BV,
  //  THEORY_BV);
  //
  //  /* Non-operator parameterized kinds
  //  --------------------------------------- */
  //
  //      BITVECTOR_EXTRACT, BITVECTOR_EXTRACT_OP, 1, 2, THEORY_BV,
  //      THEORY_BV); BITVECTOR_REPEAT, BITVECTOR_REPEAT_OP, 1, 1, THEORY_BV,
  //      THEORY_BV);
  //  BITVECTOR_ROTATE_LEFT,
  //                             BITVECTOR_ROTATE_LEFT_OP,
  //                             1,
  //                             1,
  //                             THEORY_BV,
  //                             THEORY_BV);
  //  BITVECTOR_ROTATE_RIGHT,
  //                             BITVECTOR_ROTATE_RIGHT_OP,
  //                             1,
  //                             1,
  //                             THEORY_BV,
  //                             THEORY_BV);
  //  BITVECTOR_SIGN_EXTEND,
  //                             BITVECTOR_SIGN_EXTEND_OP,
  //                             1,
  //                             1,
  //                             THEORY_BV,
  //                             THEORY_BV);
  //  BITVECTOR_ZERO_EXTEND,
  //                             BITVECTOR_ZERO_EXTEND_OP,
  //                             1,
  //                             1,
  //                             THEORY_BV,
  //                             THEORY_BV);
  //
  //

};

struct OpKindHashFunction
{
  size_t operator()(OpKind kind) const { return kind; }
};

struct OpKindData
{
  OpKindData(OpKind kind          = UNDEFINED,
             int32_t arity        = 0,
             uint32_t nparams     = 0,
             TheoryId theory_term = THEORY_BOOL,
             TheoryId theory_args = THEORY_BOOL)
      : d_kind(kind),
        d_arity(arity),
        d_nparams(nparams),
        d_theory_term(theory_term),
        d_theory_args(theory_args)
  {
  }

  bool operator==(const OpKindData& other) const
  {
    return (d_kind == other.d_kind && d_arity == other.d_arity
            && d_theory_term == other.d_theory_term
            && d_theory_args == other.d_theory_args);
  }

  /* The Kind. */
  OpKind d_kind;
  /* The arity of this kind. */
  int32_t d_arity;
  /* The number of parameters if parameterized. */
  uint32_t d_nparams;
  /* The theory of a term of this kind. */
  TheoryId d_theory_term;
  /* The theory of the term arguments of this kind. */
  TheoryId d_theory_args;
};

struct Op
{
  Op() : d_kind(OpKind::UNDEFINED), d_indices(){};
  Op(OpKind k, std::vector<uint32_t>& indices)
      : d_kind(k), d_indices(indices){};

  bool operator==(const Op& other) const
  {
    // TODO
    return false;
  }

  OpKind d_kind;
  std::vector<uint32_t> d_indices;

  //  /* The theory of a term of this kind. */
  //  TheoryId d_theory_term;
  //  /* The theory of the term arguments of this kind. */
  //  TheoryId d_theory_args;
};

using OpKindMap = std::unordered_map<OpKind, OpKindData, OpKindHashFunction>;
using OpKindVector = std::vector<OpKind>;

}  // namespace smtmbt

#endif
