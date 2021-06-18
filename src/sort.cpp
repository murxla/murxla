#include "sort.hpp"
#include <iostream>

namespace murxla {

std::ostream&
operator<<(std::ostream& out, SortKind kind)
{
  out << sort_kinds_to_str.at(kind);
  return out;
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

}  // namespace murxla

namespace std {

size_t
hash<murxla::SortKind>::operator()(const murxla::SortKind& k) const
{
  return k;
};

}  // namespace std
