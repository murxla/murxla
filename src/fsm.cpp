#include "fsm.hpp"

#include <cassert>
#include <iostream>
#include <sstream>
#include <unordered_set>

#include "solver_manager.hpp"

#define SMTMBT_BW_MIN 1
#define SMTMBT_BW_MAX 128

namespace smtmbt {

void
State::add_action(Action* a, uint32_t weight, State* next)
{
  d_actions.emplace_back(ActionTuple(a, next == nullptr ? this : next));
  d_weights.push_back(weight);
}

State*
State::run(RNGenerator& rng)
{
  assert(!d_actions.empty());
  uint32_t idx      = rng.pick_uint32_weighted(d_weights);
  ActionTuple& atup = d_actions[idx];
  if (atup.d_action->run()
      && (atup.d_next->f_precond == nullptr || atup.d_next->f_precond()))
  {
    return d_actions[idx].d_next;
  }
  return this;
}

State*
FSM::new_state(std::string id, std::function<bool(void)> fun, bool is_final)
{
  d_states.emplace_back(new State(id, fun, is_final));
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
    if (s->is_final()) continue;
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
  while (!s->is_final())
  {
    s = s->run(d_rng);
  }
}

/* Defaul Actions ...................................................... */

class ActionNew : public Action
{
 public:
  ActionNew(SolverManager& smgr) : Action(smgr, "new") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (d_solver.is_initialized()) d_solver.delete_solver();
    d_solver.new_solver();
    //
    //    //////
    //    // TODO we will need a state to (randomly) select/configure options
    //    /* Enable/disable incremental solving. */
    //    bool inc = d_rng.pick_with_prob(500);
    //    d_smgr->set_incremental(inc);
    //    cvc4->setOption("incremental", inc ? "true" : "false");
    //    //////
    return true;
  }
  // void untrace(const char* s) override;
};

class ActionDelete : public Action
{
 public:
  ActionDelete(SolverManager& smgr) : Action(smgr, "delete") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    d_solver.delete_solver();
    return true;
  }
  // void untrace(const char* s) override;
};

class ActionMkBitVectorSort : public Action
{
 public:
  ActionMkBitVectorSort(SolverManager& smgr) : Action(smgr, "mkBitVectorSort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    uint32_t bw = d_rng.pick_uint32(SMTMBT_BW_MIN, SMTMBT_BW_MAX);
    Sort res    = d_solver.mk_sort(SortKind::BIT_VECTOR, bw);
    d_smgr.add_sort(res, THEORY_BV);
    return true;
  }
  // void untrace(const char* s) override;
};

/* Configure default FSM ............................................... */

void
FSM::configure()
{
  /* --------------------------------------------------------------------- */
  /* Actions                                                               */
  /* --------------------------------------------------------------------- */

  auto a_new    = new_action<ActionNew>();
  auto a_delete = new_action<ActionDelete>();

  auto a_mkbvsort = new_action<ActionMkBitVectorSort>();

  /* --------------------------------------------------------------------- */
  /* States                                                                */
  /* --------------------------------------------------------------------- */

  auto s_new    = new_state("new");
  auto s_delete = new_state("delete");
  auto s_final  = new_state("final", nullptr, true);

  auto s_inputs = new_state("create inputs");

  /* --------------------------------------------------------------------- */
  /* Transitions                                                           */
  /* --------------------------------------------------------------------- */

  /* State: new .......................................................... */
  s_new->add_action(a_new, 10, s_delete);

  /* State: delete ....................................................... */
  /* solver actions */
  s_delete->add_action(a_delete, 10, s_final);

  /* State: create inputs ................................................ */
  /* sort actions */
  s_inputs->add_action(a_mkbvsort, 2);

  /* --------------------------------------------------------------------- */
  /* Initial State                                                         */
  /* --------------------------------------------------------------------- */

  set_init_state(s_new);
}

}  // namespace smtmbt
