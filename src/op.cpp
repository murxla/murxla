#include "op.hpp"
#include <iostream>

namespace smtmbt {

std::ostream&
operator<<(std::ostream& out, OpKind kind)
{
  out << op_kinds_to_str.at(kind);
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
          && d_sort_kind == other.d_sort_kind
          && d_sort_kind_args == other.d_sort_kind_args);
}

OpKind
op_kind_from_str(std::string& s)
{
  for (const auto& p : op_kinds_to_str)
  {
    if (p.second == s)
    {
      return p.first;
    }
  }
  return UNDEFINED;
}

}  // namespace smtmbt

