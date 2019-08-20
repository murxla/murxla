#include "op.hpp"
#include <iostream>

namespace smtmbt {

std::ostream&
operator<<(std::ostream& out, OpKind kind)
{
  switch (kind)
  {
    case UNDEFINED: out << "OPERATOR_UNDEFINED"; break;
    case DISTINCT: out << "OPERATOR_DISTINCT"; break;
    case EQUAL: out << "OPERATOR_EQUAL"; break;
    case ITE: out << "OPERATOR_ITE"; break;

    case AND: out << "OPERATOR_AND"; break;
    case OR: out << "OPERATOR_OR"; break;
    case NOT: out << "OPERATOR_NOT"; break;
    case XOR: out << "OPERATOR_XOR"; break;
    case IMPLIES: out << "OPERATOR_IMPLIES"; break;

    case BV_EXTRACT: out << "OPERATOR_BV_EXTRACT"; break;
    case BV_REPEAT: out << "OPERATOR_BV_REPEAT"; break;
    case BV_ROTATE_LEFT: out << "OPERATOR_BV_ROTATE_LEFT"; break;
    case BV_ROTATE_RIGHT: out << "OPERATOR_BV_ROTATE_RIGHT"; break;
    case BV_SIGN_EXTEND: out << "OPERATOR_BV_SIGN_EXTEND"; break;
    case BV_ZERO_EXTEND: out << "OPERATOR_BV_ZERO_EXTEND"; break;

    case BV_CONCAT: out << "OPERATOR_BV_CONCAT"; break;
    case BV_AND: out << "OPERATOR_BV_AND"; break;
    case BV_OR: out << "OPERATOR_BV_OR"; break;
    case BV_XOR: out << "OPERATOR_BV_XOR"; break;
    case BV_MULT: out << "OPERATOR_BV_MULT"; break;
    case BV_ADD: out << "OPERATOR_BV_ADD"; break;
    case BV_NOT: out << "OPERATOR_BV_NOT"; break;
    case BV_NEG: out << "OPERATOR_BV_NEG"; break;
    case BV_REDOR: out << "OPERATOR_BV_REDOR"; break;
    case BV_REDAND: out << "OPERATOR_BV_REDAND"; break;
    case BV_NAND: out << "OPERATOR_BV_NAND"; break;
    case BV_NOR: out << "OPERATOR_BV_NOR"; break;
    case BV_XNOR: out << "OPERATOR_BV_XNOR"; break;
    case BV_COMP: out << "OPERATOR_BV_COMP"; break;
    case BV_SUB: out << "OPERATOR_BV_SUB"; break;
    case BV_UDIV: out << "OPERATOR_BV_UDIV"; break;
    case BV_UREM: out << "OPERATOR_BV_UREM"; break;
    case BV_SDIV: out << "OPERATOR_BV_SDIV"; break;
    case BV_SREM: out << "OPERATOR_BV_SREM"; break;
    case BV_SMOD: out << "OPERATOR_BV_SMOD"; break;
    case BV_SHL: out << "OPERATOR_BV_SHL"; break;
    case BV_LSHR: out << "OPERATOR_BV_LSHR"; break;
    case BV_ASHR: out << "OPERATOR_BV_ASHR"; break;
    case BV_ULT: out << "OPERATOR_BV_ULT"; break;
    case BV_ULE: out << "OPERATOR_BV_ULE"; break;
    case BV_UGT: out << "OPERATOR_BV_UGT"; break;
    case BV_UGE: out << "OPERATOR_BV_UGE"; break;
    case BV_SLT: out << "OPERATOR_BV_SLT"; break;
    case BV_SLE: out << "OPERATOR_BV_SLE"; break;
    case BV_SGT: out << "OPERATOR_BV_SGT"; break;
    case BV_SGE: out << "OPERATOR_BV_SGE"; break;
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

