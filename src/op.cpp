#include "op.hpp"
#include <iostream>

namespace smtmbt {

std::ostream&
operator<<(std::ostream& out, OpKind kind)
{
  assert(op_kinds_to_str.find(kind) != op_kinds_to_str.end());
  out << op_kinds_to_str.at(kind);
  return out;
}

size_t
OpKindHashFunction::operator()(OpKind kind) const
{
  return kind;
}

bool
Op::operator==(const Op& other) const
{
  if (d_kind != other.d_kind || d_arity != other.d_arity
      || d_sort_kind != other.d_sort_kind)
    return false;

  if (d_sort_kind_args.size() != other.d_sort_kind_args.size()) return false;

  for (size_t i = 0, size = d_sort_kind_args.size(); i < size; ++i)
  {
    if (d_sort_kind_args[i] != other.d_sort_kind_args[i]) return false;
  }
  return true;
}

SortKind
Op::get_arg_sort_kind(size_t i) const
{
  if (i >= d_sort_kind_args.size())
  {
    /* All arguments have the same sort */
    assert(d_sort_kind_args.size() == 1);
    return d_sort_kind_args[0];
  }
  return d_sort_kind_args[i];
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
  return OP_UNDEFINED;
}

}  // namespace smtmbt

