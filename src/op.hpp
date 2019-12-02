#ifndef __SMTMBT__OP_H
#define __SMTMBT__OP_H

#include <cstdint>
#include <unordered_map>
#include <vector>

#include "sort.hpp"

namespace smtmbt {

enum OpKind
{
  OP_UNDEFINED,
  OP_DISTINCT,
  OP_EQUAL,
  OP_ITE,

  OP_AND,
  OP_OR,
  OP_NOT,
  OP_XOR,
  OP_IMPLIES,

  OP_BV_EXTRACT,
  OP_BV_REPEAT,
  OP_BV_ROTATE_LEFT,
  OP_BV_ROTATE_RIGHT,
  OP_BV_SIGN_EXTEND,
  OP_BV_ZERO_EXTEND,

  OP_BV_CONCAT,
  OP_BV_AND,
  OP_BV_OR,
  OP_BV_XOR,
  OP_BV_MULT,
  OP_BV_ADD,
  OP_BV_NOT,
  OP_BV_NEG,
  OP_BV_REDOR,
  OP_BV_REDAND,
  OP_BV_NAND,
  OP_BV_NOR,
  OP_BV_XNOR,
  OP_BV_COMP,
  OP_BV_SUB,
  OP_BV_UDIV,
  OP_BV_UREM,
  OP_BV_SDIV,
  OP_BV_SREM,
  OP_BV_SMOD,
  OP_BV_SHL,
  OP_BV_LSHR,
  OP_BV_ASHR,
  OP_BV_ULT,
  OP_BV_ULE,
  OP_BV_UGT,
  OP_BV_UGE,
  OP_BV_SLT,
  OP_BV_SLE,
  OP_BV_SGT,
  OP_BV_SGE,

  OP_ALL,
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
        {OP_UNDEFINED, "OP_UNDEFINED"},
        {OP_DISTINCT, "OP_DISTINCT"},
        {OP_EQUAL, "OP_EQUAL"},
        {OP_ITE, "OP_ITE"},
        {OP_AND, "OP_AND"},
        {OP_OR, "OP_OR"},
        {OP_NOT, "OP_NOT"},
        {OP_XOR, "OP_XOR"},
        {OP_IMPLIES, "OP_IMPLIES"},
        {OP_BV_EXTRACT, "OP_BV_EXTRACT"},
        {OP_BV_REPEAT, "OP_BV_REPEAT"},
        {OP_BV_ROTATE_LEFT, "OP_BV_ROTATE_LEFT"},
        {OP_BV_ROTATE_RIGHT, "OP_BV_ROTATE_RIGHT"},
        {OP_BV_SIGN_EXTEND, "OP_BV_SIGN_EXTEND"},
        {OP_BV_ZERO_EXTEND, "OP_BV_ZERO_EXTEND"},
        {OP_BV_CONCAT, "OP_BV_CONCAT"},
        {OP_BV_AND, "OP_BV_AND"},
        {OP_BV_OR, "OP_BV_OR"},
        {OP_BV_XOR, "OP_BV_XOR"},
        {OP_BV_MULT, "OP_BV_MULT"},
        {OP_BV_ADD, "OP_BV_ADD"},
        {OP_BV_NOT, "OP_BV_NOT"},
        {OP_BV_NEG, "OP_BV_NEG"},
        {OP_BV_REDOR, "OP_BV_REDOR"},
        {OP_BV_REDAND, "OP_BV_REDAND"},
        {OP_BV_NAND, "OP_BV_NAND"},
        {OP_BV_NOR, "OP_BV_NOR"},
        {OP_BV_XNOR, "OP_BV_XNOR"},
        {OP_BV_COMP, "OP_BV_COMP"},
        {OP_BV_SUB, "OP_BV_SUB"},
        {OP_BV_UDIV, "OP_BV_UDIV"},
        {OP_BV_UREM, "OP_BV_UREM"},
        {OP_BV_SDIV, "OP_BV_SDIV"},
        {OP_BV_SREM, "OP_BV_SREM"},
        {OP_BV_SMOD, "OP_BV_SMOD"},
        {OP_BV_SHL, "OP_BV_SHL"},
        {OP_BV_LSHR, "OP_BV_LSHR"},
        {OP_BV_ASHR, "OP_BV_ASHR"},
        {OP_BV_ULT, "OP_BV_ULT"},
        {OP_BV_ULE, "OP_BV_ULE"},
        {OP_BV_UGT, "OP_BV_UGT"},
        {OP_BV_UGE, "OP_BV_UGE"},
        {OP_BV_SLT, "OP_BV_SLT"},
        {OP_BV_SLE, "OP_BV_SLE"},
        {OP_BV_SGT, "OP_BV_SGT"},
        {OP_BV_SGE, "OP_BV_SGE"},
    };

std::ostream& operator<<(std::ostream& out, OpKind kind);

OpKind op_kind_from_str(std::string& s);

using OpKindVector = std::vector<OpKind>;
using OpKindMap    = std::unordered_map<OpKind, OpKindData, OpKindHashFunction>;
using OpKinds = std::unordered_map<SortKind, OpKindVector>;

}  // namespace smtmbt

#endif
