#ifndef __SMTMBT__SORT_H
#define __SMTMBT__SORT_H

#include <unordered_map>
#include <vector>

#include "theory.hpp"

namespace smtmbt {

enum SortKind
{
  BIT_VECTOR,
  BOOLEAN,
};

std::ostream& operator<<(std::ostream& out, SortKind kind);

struct SortKindHashFunction
{
  size_t operator()(SortKind kind) const;
};

struct SortKindData
{
  SortKindData(SortKind kind   = BOOLEAN,
               int32_t arity   = 0,
               TheoryId theory = THEORY_BOOL)
      : d_kind(kind), d_arity(arity), d_theory(theory)
  {
  }

  bool operator==(const SortKindData& other) const;

  /* The Kind. */
  SortKind d_kind;
  /* The arity of this kind. */
  int32_t d_arity;
  /* The theory of a sort of this kind. */
  TheoryId d_theory;
};

using SortKindVector = std::vector<SortKind>;
using SortKindMap =
    std::unordered_map<SortKind, SortKindData, SortKindHashFunction>;
using SortKinds = std::unordered_map<TheoryId, SortKindVector>;

}  // namespace smtmbt

#endif
