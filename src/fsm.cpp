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
  d_init_state = init_state;
  d_cur_state = init_state;
}

void
FSM::check_states()
{
  State* no_next_state = nullptr;
  std::unordered_set<State*> all_next_states;

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
    if (!no_next_state && next_states.empty()) no_next_state = s.get();
    all_next_states.insert(next_states.begin(), next_states.end());
  }

  /* check for unreachable state */
  for (const auto& s : d_states)
  {
    SMTMBT_WARN(s.get() != d_init_state
                && all_next_states.find(s.get()) == all_next_states.end())
        << "unreachable state '" << s->get_id() << "'";
  }

  /* check for infinite loop */
  SMTMBT_ABORT(
      no_next_state
      && (no_next_state == d_init_state
          || all_next_states.find(no_next_state) != all_next_states.end()))
      << "infinite loop in state '" << no_next_state->get_id() << "'";
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


/* ========================================================================== */
/* Default Actions                                                            */
/* ========================================================================== */

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
    d_smgr.clear();
    d_solver.delete_solver();
    return true;
  }
  // void untrace(const char* s) override;
};

class ActionMkSort : public Action
{
 public:
  ActionMkSort(SolverManager& smgr) : Action(smgr, "mkSort")
  {
    for (const auto& k : d_smgr.get_sort_kinds())
    {
      d_kinds[k.second.d_theory].push_back(k.first);
    }
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Sort res;
    TheoryId theory = d_smgr.pick_theory();
    std::cout << "picked theory " << theory << std::endl;
    SortKind kind = d_smgr.pick_sort_kind(d_kinds[theory]);
    std::cout << "picked sort " << kind << std::endl;
    switch (kind)
    {
      case SortKind::BIT_VECTOR:
      {
        uint32_t bw = d_rng.pick_uint32(SMTMBT_BW_MIN, SMTMBT_BW_MAX);
        res         = d_solver.mk_sort(SortKind::BIT_VECTOR, bw);
      }
      break;
      case SortKind::BOOLEAN: res = d_solver.mk_sort(SortKind::BOOLEAN); break;
      default: assert(false);
    }
    d_smgr.add_sort(res, theory);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Mapping from TheoryId of the sort to SortKinds of that theory. */
  std::unordered_map<TheoryId, SortKindVector> d_kinds;
};


/* ========================================================================== */
/* Configure default FSM                                                      */
/* ========================================================================== */

void
FSM::configure()
{
  /* --------------------------------------------------------------------- */
  /* Actions                                                               */
  /* --------------------------------------------------------------------- */

  auto a_new    = new_action<ActionNew>();
  auto a_delete = new_action<ActionDelete>();

  auto a_mksort = new_action<ActionMkSort>();

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
  s_new->add_action(a_new, 10, s_inputs);

  /* State: create inputs ................................................ */
  /* sort actions */
  s_inputs->add_action(a_mksort, 2, s_delete);

  /* State: delete ....................................................... */
  /* solver actions */
  s_delete->add_action(a_delete, 10, s_final);


  /* --------------------------------------------------------------------- */
  /* Initial State                                                         */
  /* --------------------------------------------------------------------- */

  set_init_state(s_new);
}

}  // namespace smtmbt
