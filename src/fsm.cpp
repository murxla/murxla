#include "fsm.hpp"

namespace smtmbt {

void
State::add(Action* a, uint32_t weight, State* next)
{
  d_actions.push_back(ActionTuple(a, weight, next));
}

State*
State::pick()
{
  // TODO
  return nullptr;
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
