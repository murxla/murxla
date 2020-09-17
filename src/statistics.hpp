#ifndef __SMTMBT__STATISTICS_H
#define __SMTMBT__STATISTICS_H

#include "config.hpp"
#include "op.hpp"

namespace smtmbt {

namespace statistics {

struct Statistics
{
  uint64_t d_results[3];
  uint64_t d_ops[OpKind::OP_ALL];
  uint64_t d_ops_ok[OpKind::OP_ALL];
  char d_state_kinds[SMTMBT_MAX_N_STATES][SMTMBT_MAX_LEN_STATE_KIND];
  uint64_t d_states[SMTMBT_MAX_N_STATES];
  char d_action_kinds[SMTMBT_MAX_N_ACTIONS][SMTMBT_MAX_LEN_ACTION_KIND];
  uint64_t d_actions[SMTMBT_MAX_N_ACTIONS];
  uint64_t d_actions_ok[SMTMBT_MAX_N_ACTIONS];

  void print() const;
};

}  // namespace statistics
}  // namespace smtmbt
#endif
