/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include "statistics.hpp"

#include "op.hpp"
#include "solver.hpp"

namespace murxla {
namespace statistics {

void
Statistics::print() const
{
  std::cout << std::endl;

  uint64_t sum = 0, sum_ok = 0;

  std::cout << "States:" << std::endl;
  for (uint32_t i = 0; i < MURXLA_MAX_N_STATES && d_state_kinds[i][0]; ++i)
  {
    std::cout << "  " << d_state_kinds[i] << ": " << d_states[i] << std::endl;
    sum += d_states[i];
  }
  std::cout << "  Total: " << sum << std::endl;

  sum = 0, sum_ok = 0;
  std::cout << "Actions:" << std::endl;
  for (uint32_t i = 0; i < MURXLA_MAX_N_ACTIONS && d_action_kinds[i][0]; ++i)
  {
    std::cout << "  " << d_action_kinds[i] << ": " << d_actions[i] << " ("
              << d_actions_ok[i] << ")" << std::endl;
    sum += d_actions[i];
    sum_ok += d_actions_ok[i];
  }
  std::cout << "  Total: " << sum << " (" << sum_ok << ")" << std::endl;

  sum = 0;
  std::cout << "Results:" << std::endl;
  for (uint32_t i = 0; i < 3; ++i)
  {
    std::cout << "  " << static_cast<Solver::Result>(i) << ": " << d_results[i]
              << std::endl;
    sum += d_results[i];
  }
  std::cout << "  Total: " << sum << std::endl;

  sum = 0, sum_ok = 0;
  std::cout << "Ops:" << std::endl;
  for (uint32_t i = 0; i < MURXLA_MAX_N_OPS && d_op_kinds[i][0]; ++i)
  {
    std::cout << "  " << d_op_kinds[i] << ": " << d_ops[i] << " ("
              << d_ops_ok[i] << ")" << std::endl;
    sum += d_ops[i];
    sum_ok += d_ops_ok[i];
  }
  std::cout << "  Total: " << sum << " (" << sum_ok << ")" << std::endl;

  sum = 0, sum_ok = 0;
  std::cout << "Sorts:" << std::endl;
  for (uint32_t i = 0; i < SORT_ANY; ++i)
  {
    std::cout << "  " << static_cast<SortKind>(i) << ": " << d_sorts[i] << " ("
              << d_sorts_ok[i] << ")" << std::endl;
    sum += d_sorts[i];
    sum_ok += d_sorts_ok[i];
  }
  std::cout << "  Total: " << sum << " (" << sum_ok << ")" << std::endl;
}

}  // namespace statistics
}  // namespace murxla
