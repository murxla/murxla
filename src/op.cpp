#include "op.hpp"
#include <iostream>

namespace smtmbt {

std::ostream&
operator<<(std::ostream& out, OpKind kind)
{
  switch (kind)
  {
    case UNDEFINED: out << "UNDEFINED"; break;
    case DISTINCT: out << "DISTINCT"; break;
    case EQUAL: out << "EQUAL"; break;
    case ITE: out << "ITE"; break;

    case AND: out << "AND"; break;
    case OR: out << "OR"; break;
    case NOT: out << "NOT"; break;
    case XOR: out << "XOR"; break;
    case IMPLIES: out << "IMPLIES"; break;

    case BV_EXTRACT: out << "BV_EXTRACT"; break;
    case BV_REPEAT: out << "BV_REPEAT"; break;
    case BV_ROTATE_LEFT: out << "BV_ROTATE_LEFT"; break;
    case BV_ROTATE_RIGHT: out << "BV_ROTATE_RIGHT"; break;
    case BV_SIGN_EXTEND: out << "BV_SIGN_EXTEND"; break;
    case BV_ZERO_EXTEND: out << "BV_ZERO_EXTEND"; break;

    case BV_CONCAT: out << "BV_CONCAT"; break;
    case BV_AND: out << "BV_AND"; break;
    case BV_OR: out << "BV_OR"; break;
    case BV_XOR: out << "BV_XOR"; break;
    case BV_MULT: out << "BV_MULT"; break;
    case BV_ADD: out << "BV_ADD"; break;
    case BV_NOT: out << "BV_NOT"; break;
    case BV_NEG: out << "BV_NEG"; break;
    case BV_REDOR: out << "BV_REDOR"; break;
    case BV_REDAND: out << "BV_REDAND"; break;
    case BV_NAND: out << "BV_NAND"; break;
    case BV_NOR: out << "BV_NOR"; break;
    case BV_XNOR: out << "BV_XNOR"; break;
    case BV_COMP: out << "BV_COMP"; break;
    case BV_SUB: out << "BV_SUB"; break;
    case BV_UDIV: out << "BV_UDIV"; break;
    case BV_UREM: out << "BV_UREM"; break;
    case BV_SDIV: out << "BV_SDIV"; break;
    case BV_SREM: out << "BV_SREM"; break;
    case BV_SMOD: out << "BV_SMOD"; break;
    case BV_SHL: out << "BV_SHL"; break;
    case BV_LSHR: out << "BV_LSHR"; break;
    case BV_ASHR: out << "BV_ASHR"; break;
    case BV_ULT: out << "BV_ULT"; break;
    case BV_ULE: out << "BV_ULE"; break;
    case BV_UGT: out << "BV_UGT"; break;
    case BV_UGE: out << "BV_UGE"; break;
    case BV_SLT: out << "BV_SLT"; break;
    case BV_SLE: out << "BV_SLE"; break;
    case BV_SGT: out << "BV_SGT"; break;
    case BV_SGE: out << "BV_SGE"; break;
    default: out << "UNKNOWN OPERATOR KIND!" << int(kind); break;
  }
  return out;
}

size_t
OpKindHashFunction::operator()(OpKind kind) const
{
  return kind;
}

bool OpKindData::operator == (const OpKindData& other) const
{
  return (d_kind == other.d_kind && d_arity == other.d_arity
          && d_theory_term == other.d_theory_term
          && d_theory_args == other.d_theory_args);
}

}  // namespace smtmbt

