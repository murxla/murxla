#ifndef __MURXLA__THEORY_H
#define __MURXLA__THEORY_H

#include <iostream>
#include <unordered_set>
#include <vector>

namespace murxla {

enum TheoryId
{
  THEORY_ARRAY,
  THEORY_BAG,
  THEORY_BOOL,
  THEORY_BV,
  THEORY_DT,
  THEORY_FP,
  THEORY_INT,
  THEORY_QUANT,
  THEORY_REAL,
  THEORY_SEQ,
  THEORY_SET,
  THEORY_STRING,
  THEORY_TRANSCENDENTAL,
  THEORY_UF,
  THEORY_ALL, /* must be last */
};

using TheoryIdVector = std::vector<TheoryId>;
using TheoryIdSet    = std::unordered_set<TheoryId>;

std::ostream& operator<<(std::ostream& out, TheoryId theory);

}  // namespace murxla
#endif
