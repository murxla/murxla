/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include "result.hpp"

#include <cassert>

namespace murxla {

std::ostream&
operator<<(std::ostream& out, const Result& res)
{
  switch (res)
  {
    case Result::RESULT_OK: out << "ok"; break;
    case Result::RESULT_ERROR: out << "error"; break;
    case Result::RESULT_ERROR_CONFIG: out << "config error"; break;
    case Result::RESULT_ERROR_UNTRACE: out << "untrace error"; break;
    case Result::RESULT_TIMEOUT: out << "timeout"; break;
    default: assert(res == Result::RESULT_UNKNOWN); out << "unknown";
  }
  return out;
}

}  // namespace murxla
