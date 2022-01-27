/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__EXIT_H
#define __MURXLA__EXIT_H

namespace murxla {

enum ExitCode
{
  EXIT_OK,
  EXIT_ERROR,
  EXIT_ERROR_CONFIG,
  EXIT_ERROR_UNTRACE,
};
}
#endif
