#ifndef __MURXLA__SORT_H
#define __MURXLA__SORT_H

#include <unordered_map>
#include <vector>

#include "theory.hpp"

namespace murxla {

enum SortKind
{
  SORT_ARRAY = 0,
  SORT_BAG,
  SORT_BOOL,
  SORT_BV,
  SORT_DT,
  SORT_FP,
  SORT_FUN,
  SORT_INT,
  SORT_REAL,
  SORT_RM,
  SORT_REGLAN,
  SORT_SEQ,
  SORT_SET,
  SORT_STRING,
  SORT_UNINTERPRETED,
  // must be last
  SORT_ANY,
};
}

namespace std {

template <>
struct hash<murxla::SortKind>
{
  size_t operator()(const murxla::SortKind& k) const;
};

}  // namespace std

namespace murxla {

static std::unordered_map<SortKind, std::string> sort_kinds_to_str{
    {SORT_ARRAY, "SORT_ARRAY"},
    {SORT_BAG, "SORT_BAG"},
    {SORT_BOOL, "SORT_BOOL"},
    {SORT_BV, "SORT_BV"},
    {SORT_DT, "SORT_DT"},
    {SORT_FP, "SORT_FP"},
    {SORT_FUN, "SORT_FUN"},
    {SORT_INT, "SORT_INT"},
    {SORT_REAL, "SORT_REAL"},
    {SORT_RM, "SORT_RM"},
    {SORT_SEQ, "SORT_SEQ"},
    {SORT_SET, "SORT_SET"},
    {SORT_REGLAN, "SORT_REGLAN"},
    {SORT_STRING, "SORT_STRING"},
    {SORT_UNINTERPRETED, "SORT_UNINTERPRETED"},
    {SORT_ANY, "SORT_ANY"}};

struct SortKindData
{
  SortKindData(SortKind kind   = SORT_BOOL,
               int32_t arity   = 0,
               TheoryId theory = THEORY_BOOL)
      : d_kind(kind), d_arity(arity), d_theory(theory)
  {
  }

  /* The Kind. */
  SortKind d_kind;
  /* The arity of this kind. */
  int32_t d_arity;
  /* The theory of a sort of this kind. */
  TheoryId d_theory;
};

using SortKindVector = std::vector<SortKind>;
using SortKindSet    = std::unordered_set<SortKind>;
using SortKindMap    = std::unordered_map<SortKind, SortKindData>;
using SortKinds      = std::unordered_map<TheoryId, SortKindVector>;

std::ostream& operator<<(std::ostream& out, SortKind kind);

SortKindSet get_all_sort_kinds_for_any(const SortKindSet& excluded_sorts = {});
SortKind sort_kind_from_str(const std::string& s);

bool operator==(const SortKindData& a, const SortKindData& b);

}  // namespace murxla

#endif
