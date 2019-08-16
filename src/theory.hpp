#ifndef __SMTMBT__THEORY_H
#define __SMTMBT__THEORY_H

#include <iostream>
#include <vector>

namespace smtmbt {

enum TheoryId
{
  THEORY_BOOL,
  THEORY_BV,
  THEORY_ALL,
};

using TheoryIdVector = std::vector<TheoryId>;

std::ostream& operator<<(std::ostream& out, TheoryId theory);

}  // namespace smtmbt
#endif
