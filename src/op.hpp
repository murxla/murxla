#ifndef __SMTMBT__OP_H
#define __SMTMBT__OP_H

#include <cstdint>
#include <unordered_map>
#include <vector>

#include "sort.hpp"

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

  BV_CONCAT,
  BV_AND,
  BV_OR,
  BV_XOR,
  BV_MULT,
  BV_ADD,
  BV_NOT,
  BV_NEG,
  BV_REDOR,
  BV_REDAND,
  BV_NAND,
  BV_NOR,
  BV_XNOR,
  BV_COMP,
  BV_SUB,
  BV_UDIV,
  BV_UREM,
  BV_SDIV,
  BV_SREM,
  BV_SMOD,
  BV_SHL,
  BV_LSHR,
  BV_ASHR,
  BV_ULT,
  BV_ULE,
  BV_UGT,
  BV_UGE,
  BV_SLT,
  BV_SLE,
  BV_SGT,
  BV_SGE,
};

struct OpKindHashFunction
{
  size_t operator()(OpKind kind) const;
};

struct OpKindData
{
  OpKindData(OpKind kind,
             int32_t arity,
             uint32_t nparams,
             SortKind sort_kind,
             SortKind sort_kind_args)
      : d_kind(kind),
        d_arity(arity),
        d_nparams(nparams),
        d_sort_kind(sort_kind),
        d_sort_kind_args(sort_kind_args)
  {
  }

  bool operator==(const OpKindData& other) const;

  /* The Kind. */
  OpKind d_kind;
  /* The arity of this kind. */
  int32_t d_arity;
  /* The number of parameters if parameterized. */
  uint32_t d_nparams;
  /* The sort kind of a term of this kind. */
  SortKind d_sort_kind;
  /* The sort kind of the term arguments of this kind. */
  SortKind d_sort_kind_args;
};

#if 0
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
#endif

static std::unordered_map<OpKind, std::string, OpKindHashFunction>
    op_kinds_to_str{
        {UNDEFINED, "UNDEFINED"},
        {DISTINCT, "DISTINCT"},
        {EQUAL, "EQUAL"},
        {ITE, "ITE"},
        {AND, "AND"},
        {OR, "OR"},
        {NOT, "NOT"},
        {XOR, "XOR"},
        {IMPLIES, "IMPLIES"},
        {BV_EXTRACT, "BV_EXTRACT"},
        {BV_REPEAT, "BV_REPEAT"},
        {BV_ROTATE_LEFT, "BV_ROTATE_LEFT"},
        {BV_ROTATE_RIGHT, "BV_ROTATE_RIGHT"},
        {BV_SIGN_EXTEND, "BV_SIGN_EXTEND"},
        {BV_ZERO_EXTEND, "BV_ZERO_EXTEND"},
        {BV_CONCAT, "BV_CONCAT"},
        {BV_AND, "BV_AND"},
        {BV_OR, "BV_OR"},
        {BV_XOR, "BV_XOR"},
        {BV_MULT, "BV_MULT"},
        {BV_ADD, "BV_ADD"},
        {BV_NOT, "BV_NOT"},
        {BV_NEG, "BV_NEG"},
        {BV_REDOR, "BV_REDOR"},
        {BV_REDAND, "BV_REDAND"},
        {BV_NAND, "BV_NAND"},
        {BV_NOR, "BV_NOR"},
        {BV_XNOR, "BV_XNOR"},
        {BV_COMP, "BV_COMP"},
        {BV_SUB, "BV_SUB"},
        {BV_UDIV, "BV_UDIV"},
        {BV_UREM, "BV_UREM"},
        {BV_SDIV, "BV_SDIV"},
        {BV_SREM, "BV_SREM"},
        {BV_SMOD, "BV_SMOD"},
        {BV_SHL, "BV_SHL"},
        {BV_LSHR, "BV_LSHR"},
        {BV_ASHR, "BV_ASHR"},
        {BV_ULT, "BV_ULT"},
        {BV_ULE, "BV_ULE"},
        {BV_UGT, "BV_UGT"},
        {BV_UGE, "BV_UGE"},
        {BV_SLT, "BV_SLT"},
        {BV_SLE, "BV_SLE"},
        {BV_SGT, "BV_SGT"},
        {BV_SGE, "BV_SGE"},
    };

std::ostream& operator<<(std::ostream& out, OpKind kind);

OpKind op_kind_from_str(std::string& s);

using OpKindVector = std::vector<OpKind>;
using OpKindMap    = std::unordered_map<OpKind, OpKindData, OpKindHashFunction>;
using OpKinds = std::unordered_map<SortKind, OpKindVector>;

}  // namespace smtmbt

#endif
