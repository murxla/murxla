#ifndef __SMTMBT__STATISTICS_H
#define __SMTMBT__STATISTICS_H

#include "fsm.hpp"
#include "op.hpp"

namespace smtmbt {

namespace statistics {

struct Statistics
{
  uint64_t d_results[3];
  uint64_t d_ops[OpKind::OP_ALL];
  uint64_t d_ops_ok[OpKind::OP_ALL];
  uint64_t d_states[State::Kind::NUM_STATES];
  uint64_t d_actions[Action::Kind::NUM_ACTIONS];
  uint64_t d_actions_ok[Action::Kind::NUM_ACTIONS];

  void print() const;
};

}  // namespace statistics
}  // namespace smtmbt
#endif
