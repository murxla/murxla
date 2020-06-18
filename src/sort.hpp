#ifndef __SMTMBT__SORT_H
#define __SMTMBT__SORT_H

#include <unordered_map>
#include <vector>

#include "theory.hpp"

namespace smtmbt {

enum SortKind
{
  SORT_ARRAY,
  SORT_BV,
  SORT_BOOL,
  SORT_ANY,
};

struct SortKindHashFunction
{
  size_t operator()(SortKind kind) const;
};

static std::unordered_map<SortKind, std::string, SortKindHashFunction>
    sort_kinds_to_str{{SORT_ARRAY, "SORT_ARRAY"},
                      {SORT_BV, "SORT_BV"},
                      {SORT_BOOL, "SORT_BOOL"},
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

std::ostream& operator<<(std::ostream& out, SortKind kind);

SortKind sort_kind_from_str(std::string& s);

bool operator==(const SortKindData& a, const SortKindData& b);

using SortKindVector = std::vector<SortKind>;
using SortKindMap =
    std::unordered_map<SortKind, SortKindData, SortKindHashFunction>;
using SortKinds = std::unordered_map<TheoryId, SortKindVector>;

}  // namespace smtmbt

#endif
