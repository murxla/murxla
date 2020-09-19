#ifndef __SMTMBT__STATISTICS_H
#define __SMTMBT__STATISTICS_H

#include "config.hpp"
#include "op.hpp"

namespace smtmbt {

namespace statistics {

struct Statistics
{
  uint64_t d_results[3];
  char d_op_kinds[SMTMBT_MAX_N_OPS][SMTMBT_MAX_KIND_LEN];
  uint64_t d_ops[SMTMBT_MAX_N_OPS];
  uint64_t d_ops_ok[SMTMBT_MAX_N_OPS];
  char d_state_kinds[SMTMBT_MAX_N_STATES][SMTMBT_MAX_KIND_LEN];
  uint64_t d_states[SMTMBT_MAX_N_STATES];
  char d_action_kinds[SMTMBT_MAX_N_ACTIONS][SMTMBT_MAX_KIND_LEN];
  uint64_t d_actions[SMTMBT_MAX_N_ACTIONS];
  uint64_t d_actions_ok[SMTMBT_MAX_N_ACTIONS];

  void print() const;
};

}  // namespace statistics
}  // namespace smtmbt
#endif
