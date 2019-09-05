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
/* Default Transitions (= empty actions)                                      */
/* ========================================================================== */

/**
 * Transition from creating inputs to the next state.
 *
 * State:      create inputs
 * Transition: if there exists at least one input
 */
class TransitionCreateInputs : public Action
{
 public:
  TransitionCreateInputs(SolverManager& smgr) : Action(smgr, "") {}
  bool run() override { return d_smgr.d_stats.inputs > 0; }
};

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
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Sort res;
    TheoryId theory = d_smgr.pick_theory();
    std::cout << "picked theory " << theory << std::endl;
    SortKinds kinds = d_smgr.get_theory_to_sort_kinds();
    assert(kinds.find(theory) != kinds.end());
    SortKind kind = d_smgr.pick_sort_kind(kinds[theory]);
    std::cout << "picked sort " << kind << std::endl;
    switch (kind)
    {
      case SortKind::BIT_VECTOR:
      {
        uint32_t bw = d_rng.pick_uint32(SMTMBT_BW_MIN, SMTMBT_BW_MAX);
        std::cout << "picked sort bw" << bw << std::endl;
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
};

class ActionMkTerm : public Action
{
 public:
  ActionMkTerm(SolverManager& smgr) : Action(smgr, "mkTerm") {}

  bool run() override
  {
    assert(d_smgr.get_enabled_theories().find(THEORY_BOOL)
           != d_smgr.get_enabled_theories().end());

    SMTMBT_TRACE << get_id();
    /* Pick theory of term argument(s).*/
    TheoryId theory_args = d_smgr.pick_theory_with_terms();

    /* Nothing to do if no kind with term arguments of picked theory exists. */
    OpKinds kinds = d_smgr.get_theory_to_op_kinds();
    if (kinds.find(theory_args) == kinds.end()
        && kinds.find(THEORY_ALL) == kinds.end())
    {
      return false;
    }

    /* Pick kind that expects arguments of picked theory. */
    const OpKindData& kind_data =
        kinds.find(THEORY_ALL) == kinds.end()
            ? d_smgr.pick_op_kind_data(kinds[theory_args])
            : d_smgr.pick_op_kind_data(kinds[theory_args], kinds[THEORY_ALL]);
    assert(d_smgr.get_enabled_theories().find(kind_data.d_theory_term)
           != d_smgr.get_enabled_theories().end());

    const OpKind kind       = kind_data.d_kind;
    const int32_t arity     = kind_data.d_arity;
    const uint32_t n_params = kind_data.d_nparams;

    /* Pick argument term(s). */
    Sort sort = nullptr;
    std::vector<Term> args;
    uint32_t n_args = arity == SMTMBT_MK_TERM_N_ARGS ? d_rng.pick_uint32(
                          SMTMBT_MK_TERM_N_ARGS_MIN, SMTMBT_MK_TERM_N_ARGS_MAX)
                                                     : arity;
    /* first argument */
    switch (kind)
    {
      case OpKind::ITE:
        if (!d_smgr.has_term(THEORY_BOOL)) return false;
        args.push_back(d_smgr.pick_term(THEORY_BOOL));
        break;
      default:
        args.push_back(d_smgr.pick_term(theory_args));
        sort = d_solver.get_sort(args[0]);
    }
    /* remaining arguments */
    for (uint32_t i = 1; i < n_args; ++i)
    {
      switch (kind)
      {
        case OpKind::BV_CONCAT:
          args.push_back(d_smgr.pick_term(theory_args));
          break;
        case OpKind::ITE:
          assert(i > 1 || sort == nullptr);
          if (i > 1)
          {
            args.push_back(d_smgr.pick_term(sort));
          }
          else
          {
            Term arg = d_smgr.pick_term(theory_args);
            sort     = d_solver.get_sort(arg);
            args.push_back(arg);
          }
          break;
        default: assert(sort); args.push_back(d_smgr.pick_term(sort));
      }
    }

    std::vector<uint32_t> params;
    if (n_params)
    {
      /* Numeral arguments for indexed operators. */
      uint32_t bw = sort->get_bv_size();
      switch (kind)
      {
        case BV_EXTRACT:
          assert(sort->is_bv());
          params.push_back(d_rng.pick_uint32(0, bw - 1));     // high
          params.push_back(d_rng.pick_uint32(0, params[0]));  // low
          break;
        case BV_REPEAT:
          assert(sort->is_bv());
          params.push_back(
              d_rng.pick_uint32(1, std::max<uint32_t>(1, SMTMBT_BW_MAX / bw)));
          break;
        case BV_ROTATE_LEFT:
        case BV_ROTATE_RIGHT:
          assert(sort->is_bv());
          params.push_back(d_rng.pick_uint32(0, bw));
          break;
        case BV_SIGN_EXTEND:
        case BV_ZERO_EXTEND:
          assert(sort->is_bv());
          params.push_back(d_rng.pick_uint32(0, SMTMBT_BW_MAX - bw));
          break;
        default: assert(false);
      }
    }

    /* Create term. */
    Term res = d_solver.mk_term(kind, args, params);

    std::cout << "mk_term res " << res << std::endl;
    d_smgr.add_term(res,
                    d_solver.get_sort(res),
                    kind_data.d_theory_term == THEORY_ALL
                        ? theory_args
                        : kind_data.d_theory_term);
    return true;
  }
  // void untrace(const char* s) override;
};

class ActionMkConst : public Action
{
 public:
  ActionMkConst(SolverManager& smgr) : Action(smgr, "mkConst") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick theory and sort of const. */
    if (!d_smgr.has_sort()) return false;
    TheoryId theory = d_smgr.pick_theory_with_sorts();
    Sort sort       = d_smgr.pick_sort(theory);
    /* Create const. */
    // TODO pick random symbol for const
    Term res = d_solver.mk_const(sort, "");
    std::cout << "res " << res << std::endl;
    d_smgr.add_input(res, d_solver.get_sort(res), theory);
    return true;
  }
  // void untrace(const char* s) override;
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

  auto a_mkconst = new_action<ActionMkConst>();
  auto a_mkterm  = new_action<ActionMkTerm>();

  auto t_inputs = new_action<TransitionCreateInputs>();

  /* --------------------------------------------------------------------- */
  /* States                                                                */
  /* --------------------------------------------------------------------- */

  auto s_new    = new_state("new");
  auto s_delete = new_state("delete");
  auto s_final  = new_state("final", nullptr, true);

  auto s_inputs = new_state("create inputs");
  auto s_terms  = new_state("create terms");

  /* --------------------------------------------------------------------- */
  /* Transitions                                                           */
  /* --------------------------------------------------------------------- */

  /* State: new .......................................................... */
  s_new->add_action(a_new, 10, s_inputs);

  /* State: create inputs ................................................ */
  s_inputs->add_action(a_mksort, 10);
  s_inputs->add_action(a_mkconst, 10);
  s_inputs->add_action(t_inputs, 10, s_terms);

  /* State: create terms ................................................. */
  s_terms->add_action(a_mkterm, 10, s_delete);

  /* State: delete ....................................................... */
  s_delete->add_action(a_delete, 10, s_final);


  /* --------------------------------------------------------------------- */
  /* Initial State                                                         */
  /* --------------------------------------------------------------------- */

  set_init_state(s_new);
}

}  // namespace smtmbt
