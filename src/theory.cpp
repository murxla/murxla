/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include "theory.hpp"

namespace murxla {

std::ostream&
operator<<(std::ostream& out, TheoryId theory)
{
  switch (theory)
  {
    case THEORY_ARRAY: out << "THEORY_ARRAY"; break;
    case THEORY_BAG: out << "THEORY_BAG"; break;
    case THEORY_BOOL: out << "THEORY_BOOL"; break;
    case THEORY_BV: out << "THEORY_BV"; break;
    case THEORY_DT: out << "THEORY_DT"; break;
    case THEORY_FP: out << "THEORY_FP"; break;
    case THEORY_INT: out << "THEORY_INT"; break;
    case THEORY_QUANT: out << "THEORY_QUANT"; break;
    case THEORY_REAL: out << "THEORY_REAL"; break;
    case THEORY_SEQ: out << "THEORY_SEQ"; break;
    case THEORY_SET: out << "THEORY_SET"; break;
    case THEORY_STRING: out << "THEORY_STRING"; break;
    case THEORY_TRANSCENDENTAL: out << "THEORY_TRANSCENDENTAL"; break;
    case THEORY_UF: out << "THEORY_UF"; break;
    default: out << "UNKNOWN THEORY!" << int(theory); break;
  }
  return out;
}
}  // namespace murxla
