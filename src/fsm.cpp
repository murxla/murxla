#include "fsm.hpp"

namespace smtmbt {

void
State::add(Action* a, uint32_t weight, State* next)
{
  d_actions.emplace_back(ActionTuple(a, next));
  d_weights.push_back(weight);
}

void
State::run()
{
  if (d_actions.empty()) return;
  uint32_t idx = s_rng.pick_weighted_uint32(d_weights);
  d_actions[idx].d_action->run();
}

State*
FSM::new_state()
{
  d_states.emplace_back(new State());
  return d_states.back().get();
}

void
FSM::set_init_state(State* init_state)
{
  d_cur_state = init_state;
}

void
FSM::set_final_state(State* final_state)
{
  d_final_state = final_state;
}

void
FSM::run()
{
  // TODO
}

}  // namespace smtmbt
