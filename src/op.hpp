#ifndef __SMTMBT__OP_H
#define __SMTMBT__OP_H

#include <cstdint>
#include <vector>

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

}  // namespace smtmbt

#endif
