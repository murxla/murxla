#include "sort.hpp"
#include <iostream>

namespace smtmbt {

std::ostream&
operator<<(std::ostream& out, SortKind kind)
{
  switch (kind)
  {
    case SORT_BIT_VECTOR: out << "SORT_KIND_BIT_VECTOR"; break;
    case SORT_BOOLEAN: out << "SORT_KIND_BOOLEAN"; break;
    default: out << "UNKNOWN SORT KIND!" << int(kind); break;
  }
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
}  // namespace smtmbt
