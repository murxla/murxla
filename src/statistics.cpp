#include "statistics.hpp"

#include "fsm.hpp"  // TODO temporary until refactor is done

namespace smtmbt {
namespace statistics {

void
Statistics::print() const
{
  std::cout << std::endl;

  uint64_t sum = 0;

  std::cout << "States:" << std::endl;
  for (uint32_t i = State::Kind::UNDEFINED + 1; i < State::Kind::NUM_STATES;
       ++i)
  {
    std::cout << "  " << static_cast<State::Kind>(i) << ": " << d_states[i]
              << std::endl;
    sum += d_states[i];
  }
  std::cout << "  Total: " << sum << std::endl;

  sum = 0;
  std::cout << "Actions:" << std::endl;
  for (uint32_t i = 0; i < SMTMBT_MAX_N_ACTIONS && d_action_kinds[i][0]; ++i)
  {
    std::cout << "  " << d_action_kinds[i] << ": " << d_actions[i] << " ("
              << d_actions_ok[i] << ")" << std::endl;
    sum += d_actions[i];
  }
  std::cout << "  Total: " << sum << std::endl;

  sum = 0;
  std::cout << "Results:" << std::endl;
  for (uint32_t i = 0; i < 3; ++i)
  {
    std::cout << "  " << static_cast<Solver::Result>(i) << ": " << d_results[i]
              << std::endl;
    sum += d_results[i];
  }
  std::cout << "  Total: " << sum << std::endl;

  sum = 0;
  std::cout << "Ops:" << std::endl;
  for (uint32_t i = 0; i < OpKind::OP_ALL; ++i)
  {
    std::cout << "  " << static_cast<OpKind>(i) << ": " << d_ops[i] << " ("
              << d_ops_ok[i] << ")" << std::endl;
    sum += d_ops[i];
  }
  std::cout << "  Total: " << sum << std::endl;
}

}  // namespace statistics
}  // namespace smtmbt
