#include "theory.hpp"

namespace smtmbt {

std::ostream&
operator<<(std::ostream& out, TheoryId theory)
{
  switch (theory)
  {
    case THEORY_ARRAY: out << "THEORY_ARRAY"; break;
    case THEORY_BV: out << "THEORY_BV"; break;
    case THEORY_BOOL: out << "THEORY_BOOL"; break;
    default: out << "UNKNOWN THEORY!" << int(theory); break;
  }
  return out;
}
}  // namespace smtmbt
