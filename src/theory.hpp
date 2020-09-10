#ifndef __SMTMBT__THEORY_H
#define __SMTMBT__THEORY_H

#include <iostream>
#include <unordered_set>
#include <vector>

namespace smtmbt {

enum TheoryId
{
  THEORY_ARRAY,
  THEORY_BOOL,
  THEORY_BV,
  THEORY_FP,
  THEORY_INT,
  THEORY_QUANT,
  THEORY_REAL,
  THEORY_STRING,
  THEORY_UF,
  THEORY_ALL, /* must be last */
};

using TheoryIdVector = std::vector<TheoryId>;
using TheoryIdSet    = std::unordered_set<TheoryId>;

std::ostream& operator<<(std::ostream& out, TheoryId theory);

}  // namespace smtmbt
#endif
