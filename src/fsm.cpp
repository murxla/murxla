#include "fsm.hpp"

#include <cassert>
#include <iostream>
#include <sstream>
#include <unordered_set>

#include "solver_manager.hpp"

namespace smtmbt {

void
State::add_action(Action* a, uint32_t weight, State* next)
{
  d_actions.emplace_back(ActionTuple(a, next));
  d_weights.push_back(weight);
}

State*
State::run()
{
  assert(!d_actions.empty());
  uint32_t idx = s_rng.pick_weighted_uint32(d_weights);
  d_actions[idx].d_action->run();
  return d_actions[idx].d_next;
}

State*
FSM::new_state(std::string id)
{
  d_states.emplace_back(new State(id));
  return d_states.back().get();
}

void
FSM::set_init_state(State* init_state)
{
  d_cur_state = init_state;
}

void
FSM::check_states()
{
  /* check for infinite loop */
  for (const auto& s : d_states)
  {
    assert(s->d_actions.size());
    std::unordered_set<State*> next_states;
    for (const auto& a : s->d_actions)
    {
      State* next = a.d_next;
      if (next != s.get()) next_states.insert(next);
    }
    SMTMBT_ABORT(next_states.empty())
        << "infinite loop in state '" << s->get_id() << "'";
  }
}

void
FSM::run()
{
  check_states();

  State* s = d_cur_state;
  while (s != nullptr)
  {
    s = s->run();
  }
}

}  // namespace smtmbt
