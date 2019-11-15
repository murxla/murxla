#include "sort.hpp"
#include <iostream>

namespace smtmbt {

std::ostream&
operator<<(std::ostream& out, SortKind kind)
{
  out << sort_kinds_to_str.at(kind);
  return out;
}

size_t
SortKindHashFunction::operator()(SortKind kind) const
{
  return kind;
}

bool
operator==(const SortKindData& a, const SortKindData& b)
{
  return (a.d_kind == b.d_kind && a.d_arity == b.d_arity
          && a.d_theory == b.d_theory);
}

SortKind
sort_kind_from_str(std::string& s)
{
  for (const auto& p : sort_kinds_to_str)
  {
    if (p.second == s)
    {
      return p.first;
    }
  }
  return SORT_ANY;
}

}  // namespace smtmbt
