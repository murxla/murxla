#include "fsm.hpp"

#include <cassert>
#include <iostream>
#include <numeric>
#include <sstream>
#include <unordered_set>

#include "solver_manager.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */
/* State                                                                      */
/* -------------------------------------------------------------------------- */

void
State::add_action(Action* a, uint32_t priority, State* next)
{
  d_actions.emplace_back(ActionTuple(a, next == nullptr ? this : next));
  d_weights.push_back(priority);
}

void
State::disable_action(Action::Kind kind)
{
  for (size_t i = 0; i < d_actions.size(); ++i)
  {
    if (d_actions[i].d_action->get_kind() == kind)
    {
      d_weights[i] = 0;
    }
  }
}

State*
State::run(RNGenerator& rng)
{
  MURXLA_CHECK_CONFIG(!d_actions.empty()) << "no actions configured";

  uint32_t idx      = rng.pick_weighted<uint32_t>(d_weights);
  ActionTuple& atup = d_actions[idx];

  /* record state statistics */
  ++d_mbt_stats->d_states[get_id()];

  /* only pick empty transitions if precondition of this state is false */
  if (f_precond != nullptr && !f_precond())
  {
    while (!atup.d_action->empty())
    {
      idx  = rng.pick_weighted<uint32_t>(d_weights);
      atup = d_actions[idx];
    }
  }

  /* record action statistics */
  ++d_mbt_stats->d_actions[atup.d_action->get_id()];

  /* When adding terms of parameterized sort, e.g., bit-vectors or
   * floating-points, or when creating terms with a Real operator, that is
   * actually of sort Int, it can happen that the resulting term has yet unknown
   * sort, i.e., a sort that has not previously been created via ActionMksort.
   * In order to ensure that the untracer can map such sorts back correctly,
   * we have to trace a "phantom" action (= an action, that is only executed
   * when untracing) for new sorts. */
  atup.d_action->trace_get_sorts();

  if (atup.d_action->run()
      && (atup.d_next->f_precond == nullptr || atup.d_next->f_precond()))
  {
    /* record action statistics */
    ++d_mbt_stats->d_actions_ok[atup.d_action->get_id()];

    return d_actions[idx].d_next;
  }

  return this;
}

/* -------------------------------------------------------------------------- */
/* FSM                                                                        */
/* -------------------------------------------------------------------------- */

FSM::FSM(RNGenerator& rng,
         Solver* solver,
         std::ostream& trace,
         SolverOptions& options,
         bool arith_subtyping,
         bool arith_linear,
         bool trace_seeds,
         bool simple_symbols,
         bool smt,
         statistics::Statistics* stats,
         const TheoryIdVector& enabled_theories)
    : d_smgr(solver,
             rng,
             trace,
             options,
             arith_subtyping,
             arith_linear,
             trace_seeds,
             simple_symbols,
             stats,
             enabled_theories),
      d_rng(rng),
      d_arith_linear(arith_linear),
      d_smt(smt),
      d_mbt_stats(stats)
{
  auto smgr_enabled_theories = d_smgr.get_enabled_theories();
  if (smgr_enabled_theories.find(THEORY_QUANT) != smgr_enabled_theories.end())
  {
    bool force_quant_enabled =
        std::find(
            enabled_theories.begin(), enabled_theories.end(), THEORY_QUANT)
        != enabled_theories.end();
    auto disabled_quant_theories = solver->get_unsupported_quant_theories();
    if (!disabled_quant_theories.empty())
    {
      /* In case that quantifiers were not explicitly enabled via command line
       * and are not allowed in combination with a specific set of otherwise
       * supported theories, we decide to enable THEORY_QUANT with a probability
       * of 10%. */
      if (force_quant_enabled || d_rng.pick_with_prob(100))
      {
        for (TheoryId t : disabled_quant_theories)
        {
          d_smgr.disable_theory(t);
        }
      }
      else
      {
        d_smgr.disable_theory(THEORY_QUANT);
      }
    }
  }
}

SolverManager&
FSM::get_smgr()
{
  return d_smgr;
}

State*
FSM::new_state(const State::Kind& kind,
               std::function<bool(void)> fun,
               bool is_final)
{
  uint64_t id = d_states.size();

  MURXLA_CHECK_CONFIG(id < MURXLA_MAX_N_STATES)
      << "maximum number of states exceeded, increase limit by adjusting "
         "value of macro MURXLA_MAX_N_STATES in config.hpp";

  State* state;
  d_states.emplace_back(new State(kind, fun, is_final));

  state = d_states.back().get();
  state->set_id(id);
  state->d_mbt_stats = d_mbt_stats;
  strncpy(d_mbt_stats->d_state_kinds[id], kind.c_str(), kind.size());

  return state;
}

void
FSM::disable_action(Action::Kind kind)
{
  for (auto& s : d_states)
  {
    s->disable_action(kind);
  }
}

void
FSM::set_init_state(State* init_state)
{
  d_state_init = init_state;
  d_state_cur  = init_state;
}

void
FSM::check_states()
{
  for (const auto& s : d_states)
  {
    if (s.get() == d_state_init) continue;

    // check for reachability
    bool reachable = false;
    std::vector<State*> visit{d_state_init};
    std::unordered_set<State*> visited;
    while (!visit.empty())
    {
      State* cur = visit.back();
      visit.pop_back();
      if (visited.find(cur) != visited.end()) continue;
      visited.insert(cur);
      if (cur == s.get())
      {
        reachable = true;
        break;
      }
      for (const auto& a : cur->d_actions)
      {
        visit.push_back(a.d_next);
      }
    }
    MURXLA_WARN(!reachable) << "unreachable state '" << s->get_kind() << "'";

    // check if it's possible to transition into another state
    if (!s->is_final())
    {
      bool has_next_state = false;
      for (const auto& a : s->d_actions)
      {
        if (a.d_next != s.get())
        {
          has_next_state = true;
          break;
        }
      }
      MURXLA_WARN(!has_next_state)
          << "stuck at state '" << s->get_kind() << "'";
    }
  }
}

State*
FSM::get_state(const State::Kind& kind) const
{
  State* res = nullptr;
  for (const auto& s : d_states)
  {
    if (s->d_kind == kind)
    {
      res = s.get();
    }
  }
  MURXLA_CHECK_CONFIG(res != nullptr) << "undefined state '" << kind << "'";
  return res;
}

/* -------------------------------------------------------------------------- */

void
FSM::run()
{
  check_states();

  State* s = d_state_cur;
  while (!s->is_final())
  {
    s = s->run(d_rng);
  }
}

/* ========================================================================== */
/* Configure default FSM                                                      */
/* ========================================================================== */

void
FSM::configure()
{
  /* --------------------------------------------------------------------- */
  /* Actions                                                               */
  /* --------------------------------------------------------------------- */

  (void) new_action<ActionTermGetSort>();  // not added to any state

  auto a_new    = new_action<ActionNew>();
  auto a_delete = new_action<ActionDelete>();

  auto a_mksort = new_action<ActionMkSort>();

  auto a_mkval   = new_action<ActionMkValue>();
  auto a_mksval  = new_action<ActionMkSpecialValue>();
  auto a_mkconst = new_action<ActionMkConst>();
  auto a_mkvar   = new_action<ActionMkVar>();
  auto a_mkterm  = new_action<ActionMkTerm>();

  auto a_termchksort = new_action<ActionTermCheckSort>();

  auto a_assert = new_action<ActionAssertFormula>();

  auto a_failed = new_action<ActionGetUnsatAssumptions>();

  auto a_getvalue = new_action<ActionGetValue>();

  auto a_printmodel = new_action<ActionPrintModel>();

  auto a_sat     = new_action<ActionCheckSat>();
  auto a_sat_ass = new_action<ActionCheckSatAssuming>();

  auto a_push = new_action<ActionPush>();
  auto a_pop  = new_action<ActionPop>();

  auto a_reset_ass = new_action<ActionResetAssertions>();

  auto a_setoption = new_action<ActionSetOption>();

  auto t_default = new_action<TransitionDefault>();
  auto t_inputs  = new_action<TransitionCreateInputs>();
  auto t_model   = new_action<TransitionModel>();
  auto t_sorts   = new_action<TransitionCreateSorts>();

  /* --------------------------------------------------------------------- */
  /* States                                                                */
  /* --------------------------------------------------------------------- */

  auto s_new    = new_state(State::NEW);
  auto s_opt    = new_state(State::OPT);
  auto s_delete = new_state(State::DELETE);
  auto s_final  = new_state(State::FINAL, nullptr, true);

  auto s_sorts  = new_state(State::CREATE_SORTS);
  auto s_inputs = new_state(State::CREATE_INPUTS);
  auto s_terms =
      new_state(State::CREATE_TERMS, [this]() { return d_smgr.has_term(); });

  auto s_assert =
      new_state(State::ASSERT, [this]() { return d_smgr.has_term(SORT_BOOL); });

  auto s_model = new_state(State::MODEL, [this]() {
    return d_smgr.d_model_gen && d_smgr.d_sat_called
           && d_smgr.d_sat_result == Solver::Result::SAT;
  });

  auto s_sat = new_state(State::CHECK_SAT, [this]() {
    return d_smgr.d_n_sat_calls == 0 || d_smgr.d_incremental;
  });

  auto s_push_pop =
      new_state(State::PUSH_POP, [this]() { return d_smgr.d_incremental; });

  /* --------------------------------------------------------------------- */
  /* Add actions/transitions to states                                     */
  /* --------------------------------------------------------------------- */

  /* State: new .......................................................... */
  s_new->add_action(a_new, 1, s_opt);

  /* State: opt .......................................................... */
  s_opt->add_action(a_setoption, 1);
  s_opt->add_action(t_default, 5, s_sorts);

  s_sorts->add_action(a_mksort, 1);
  s_sorts->add_action(t_sorts, 5, s_inputs);

  /* State: create inputs ................................................ */
  s_inputs->add_action(a_mksort, 100, s_sorts);
  s_inputs->add_action(a_mkval, 10);
  s_inputs->add_action(a_mksval, 5);
  s_inputs->add_action(a_mkconst, 2);
  if (d_smgr.get_solver().supports_theory(THEORY_QUANT))
  {
    s_inputs->add_action(a_mkvar, 200);
  }
  s_inputs->add_action(a_termchksort, 10);
  s_inputs->add_action(t_inputs, 50, s_terms);
  s_inputs->add_action(t_inputs, 5000, s_sat);
  s_inputs->add_action(t_inputs, 500, s_push_pop);

  /* State: create terms ................................................. */
  s_terms->add_action(a_mkterm, 1);
  s_terms->add_action(a_termchksort, 10);
  s_terms->add_action(t_default, 250, s_assert);
  s_terms->add_action(t_default, 5000, s_sat);
  s_terms->add_action(t_inputs, 500, s_push_pop);

  /* State: assert/assume formula ........................................ */
  s_assert->add_action(a_assert, 1);
  s_assert->add_action(t_default, 20, s_sat);
  s_assert->add_action(t_inputs, 3, s_push_pop);
  s_assert->add_action(t_default, 50, s_terms);

  /* State: check sat .................................................... */
  s_sat->add_action(a_sat, 1);
  s_sat->add_action(a_sat_ass, 2);
  s_sat->add_action(a_failed, 5);
  s_sat->add_action(t_inputs, 2, s_push_pop);
  s_sat->add_action(t_inputs, 200, s_delete);

  /* State: model ........................................................ */
  s_model->add_action(a_printmodel, 1);
  s_model->add_action(a_getvalue, 1);
  add_action_to_all_states_next(t_default, 10, s_model, {State::OPT});
  add_action_to_all_states(t_model, 10, {State::OPT}, s_model);

  /* State: push_pop ..................................................... */
  s_push_pop->add_action(a_push, 1);
  s_push_pop->add_action(a_pop, 1);
  s_push_pop->add_action(t_default, 2, s_assert);
  add_action_to_all_states_next(t_default, 1, s_push_pop, {State::OPT});

  /* State: delete ....................................................... */
  s_delete->add_action(a_delete, 1, s_final);

  /* All States (with exceptions) ........................................ */
  add_action_to_all_states(a_reset_ass, 5000);

  /* --------------------------------------------------------------------- */
  /* Initial State                                                         */
  /* --------------------------------------------------------------------- */

  set_init_state(s_new);

  /* --------------------------------------------------------------------- */
  /* Configure solver specific actions/states                              */
  /* --------------------------------------------------------------------- */

  if (!d_smt) d_smgr.get_solver().configure_fsm(this);

  /* --------------------------------------------------------------------- */
  /* Add actions that are configured via add_action_to_all_states          */
  /* --------------------------------------------------------------------- */

  for (const auto& t : d_actions_all_states)
  {
    Action* action                                  = std::get<0>(t);
    uint32_t priority                               = std::get<1>(t);
    std::unordered_set<std::string> excluded_states = std::get<2>(t);
    State* next                                     = std::get<3>(t);
    for (const auto& s : d_states)
    {
      const auto kind = s->get_kind();
      if (kind == State::NEW || kind == State::DELETE || kind == State::FINAL
          || excluded_states.find(s->get_kind()) != excluded_states.end())
      {
        continue;
      }
      s->add_action(action, priority, next);
    }
  }

  /* --------------------------------------------------------------------- */
  /* Add actions that are configured via add_action_to_all_states_next     */
  /* --------------------------------------------------------------------- */

  for (const auto& t : d_actions_all_states_next)
  {
    Action* action                                  = std::get<0>(t);
    uint32_t priority                               = std::get<1>(t);
    State* state                                    = std::get<2>(t);
    std::unordered_set<std::string> excluded_states = std::get<3>(t);
    for (const auto& s : d_states)
    {
      const auto kind = s->get_kind();
      if (kind == State::NEW || kind == State::DELETE || kind == State::FINAL
          || excluded_states.find(s->get_kind()) != excluded_states.end())
      {
        continue;
      }
      state->add_action(action, priority, s.get());
    }
  }

  /* --------------------------------------------------------------------- */
  /* Compute actual weights based on given priorities                      */
  /* --------------------------------------------------------------------- */

  for (const auto& s : d_states)
  {
    uint32_t sum =
        std::accumulate(s->d_weights.begin(), s->d_weights.end(), 0u);
    uint32_t i = 0;
    for (uint32_t& w : s->d_weights)
    {
      if (w == 0) continue;
      w = sum / w;
      i += 1;
    }
  }
}

/* ========================================================================== */
/* Replay given trace.                                                        */
/* ========================================================================== */

void
FSM::untrace(const std::string& trace_file_name)
{
  assert(!trace_file_name.empty());

  uint32_t nline   = 0;
  std::vector<uint64_t> ret_val;
  Action* ret_action;
  std::string line;
  std::ifstream trace;

  trace.open(trace_file_name);
  MURXLA_CHECK_CONFIG(trace.is_open())
      << "untrace: unable to open file '" << trace_file_name << "'";

  try
  {
    while (std::getline(trace, line))
    {
      nline += 1;
      if (line.empty()) continue;
      if (line[0] == '#') continue;

      std::string id;
      std::vector<std::string> tokens;

      tokenize(line, id, tokens);

      if (id == "return")
      {
        throw MurxlaUntraceException(
            trace_file_name, nline, "stray 'return' statement");
      }
      else if (id == "set-seed")
      {
        std::stringstream sss;
        for (auto t : tokens) sss << " " << t;
        sss >> d_rng.get_engine();
      }
      else
      {
        if (d_actions.find(id) == d_actions.end())
        {
          std::stringstream ss;
          ss << "unknown action '" << id << "'";
          throw MurxlaUntraceException(trace_file_name, nline, ss);
        }

        Action* action = d_actions.at(id).get();

        if (action->returns() == Action::ReturnValue::NONE)
        {
          ret_val = action->untrace(tokens);
          assert(ret_val.empty());
        }
        else
        {
          try
          {
            ret_val = action->untrace(tokens);
            ret_action = action;
          }
          catch (MurxlaActionUntraceException& e)
          {
            throw MurxlaUntraceException(trace_file_name, nline, e.get_msg());
          }

          if (std::getline(trace, line))
          {
            nline += 1;

            std::string next_id;
            std::vector<std::string> next_tokens;

            tokenize(line, next_id, next_tokens);

            if (next_id != "return")
            {
              throw MurxlaUntraceException(
                  trace_file_name, nline, "expected 'return' statement");
            }

            if (action->returns() == Action::ReturnValue::ID)
            {
              if (ret_action->get_kind() == Action::MK_TERM)
              {
                if (next_tokens.size() != 2)
                {
                  throw MurxlaUntraceException(
                      trace_file_name,
                      nline,
                      "expected two arguments (term, sort) to 'return'");
                }
              }
              else if (next_tokens.size() != 1)
              {
                throw MurxlaUntraceException(
                    trace_file_name,
                    nline,
                    "expected single argument to 'return'");
              }
            }
            else if (action->returns() == Action::ReturnValue::ID_LIST
                     && next_tokens.size() < 1)
            {
              throw MurxlaUntraceException(
                  trace_file_name,
                  nline,
                  "expected at least one argument to 'return'");
            }

            assert(ret_val.size() == next_tokens.size());
            for (uint32_t i = 0, n = next_tokens.size(); i < n; ++i)
            {
              uint64_t rid = Action::untrace_str_to_id(next_tokens[i]);
              if (next_tokens[i][0] == 's')
              {
                if (!d_smgr.register_sort(rid, ret_val[i]))
                {
                  throw MurxlaUntraceException(
                      trace_file_name,
                      nline,
                      "unknown sort id '" + next_tokens[i] + "'");
                }
              }
              else
              {
                assert(next_tokens[i][0] == 't');
                d_smgr.register_term(rid, ret_val[i]);
              }
            }
          }
          ret_val = {};
        }
      }
    }
  }
  catch (MurxlaUntraceIdException& e)
  {
    throw MurxlaUntraceException(trace_file_name, nline, e.get_msg());
  }
  if (trace.is_open()) trace.close();
}

/* ========================================================================== */
}  // namespace murxla
