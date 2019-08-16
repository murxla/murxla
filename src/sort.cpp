#include "sort.hpp"
#include <iostream>

namespace smtmbt {

std::ostream&
operator<<(std::ostream& out, SortKind kind)
{
  switch (kind)
  {
    case BIT_VECTOR: out << "SORT_KIND_BIT_VECTOR"; break;
    case BOOLEAN: out << "SORT_KIND_BOOLEAN"; break;
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
SortKindData::operator==(const SortKindData& other) const
{
  return (d_kind == other.d_kind && d_arity == other.d_arity
          && d_theory == other.d_theory);
}
}  // namespace smtmbt
