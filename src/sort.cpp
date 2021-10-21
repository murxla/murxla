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

SortKindSet
get_all_sort_kinds_for_any(const SortKindSet& excluded_sorts)
{
  SortKindSet res;
  for (uint32_t i = 0; i < SORT_ANY; ++i)
  {
    SortKind sort_kind = static_cast<SortKind>(i);
    if (excluded_sorts.find(sort_kind) == excluded_sorts.end())
    {
      res.insert(sort_kind);
    }
  }
  return res;
}

SortKind
sort_kind_from_str(const std::string& s)
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
