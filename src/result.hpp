/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__RESULT_H
#define __MURXLA__RESULT_H

#include <iomanip>

namespace murxla {

/* -------------------------------------------------------------------------- */

enum Result
{
  RESULT_ERROR,
  RESULT_ERROR_CONFIG,
  RESULT_ERROR_UNTRACE,
  RESULT_OK,
  RESULT_TIMEOUT,
  RESULT_UNKNOWN,
};

std::ostream& operator<<(std::ostream& out, const Result& res);

/* -------------------------------------------------------------------------- */

}  // namespace murxla

#endif
