/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__FSM_H
#define __MURXLA__FSM_H

#include <cstdint>
#include <cstring>
#include <fstream>
#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "action.hpp"
#include "config.hpp"
#include "except.hpp"
#include "solver_manager.hpp"
#include "solver_option.hpp"
#include "statistics.hpp"

/* -------------------------------------------------------------------------- */

namespace murxla {

/* -------------------------------------------------------------------------- */

namespace statistics {
struct Statistics;
}

/**
 * A state of the FSM.
 *
 * Corresponds to a state of the solver under test.
 *
 * We distinguish three configuration kinds (State::ConfigKind) of states:
 * - **regular** states
 * - **decision** states
 * - **choice** states
 *
 * We further identify one state as the *initial* state, and one state as
 * the *final* state.
 *
 * A **decision state** is a state that only serves as decision point with a
 * single point of entrance and only specific transitions (the choices to be
 * made) out of the state. A decision state is not to be extended with any
 * other actions other than the transitions that represent the choices this
 * decision state has been created for. From a decision state, we may only
 * transition into the choice states that represent the valid choices for
 * this decision.
 *
 * A **choice state** is a state that represents a valid choice for a specific
 * decision. It represents a very specific solver state that is a precondition
 * for specific actions (solver API calls) to be executed.
 * Choice states may only be transitioned into from their corresponding
 * decision state.
 *
 * As an example, we use a decision state #DECIDE_SAT_UNSAT for handling
 * different solver states after a satisfiability check in state #CHECK_SAT.
 * From #CHECK_SAT, we transition into #DECIDE_SAT_UNSAT, from where we
 * transition into either choice state #SAT (when the result is *sat* or
 * *unknown*) or #UNSAT (when the result is *unsat*).
 * Each choice state configure actions to make additional queries to the
 * solver under the specific premise that a check-sat call has been issued and
 * the satisfiability result is either sat or unsat.
 */
class State
{
  friend class FSM;

 public:
  /**
   * The kind of a state.
   *
   * This is used a state identifier when retrieving states that have been
   * added to the FSM via FSM::get_state().
   * We use strings here to make the set of state kinds easily extensible
   * with solver-specific states.
   */
  using Kind = std::string;

  /** The undefined state. */
  inline static const Kind UNDEFINED = "undefined";
  /**
   * The state where an instance of the solver under test is created and
   * initialized.
   *
   * By default, this is configured as the **initial** state.
   */
  inline static const Kind NEW = "new";
  /** The state where the logic of the formulas to be created is configured. */
  inline static const Kind SET_LOGIC = "set_logic";
  /** The state where solver options are configured. */
  inline static const Kind OPT = "opt";
  /**
   * The state where solver options that are required based on the current
   * solver configuration are configured (see Solver::get_required_options()).
   */
  inline static const Kind OPT_REQ = "opt_req";
  /**
   * The state where the instance of the solver under test is deleted (**not**
   * the final state).
   */
  inline static const Kind DELETE = "delete";
  /**
   * The final state.
   *
   * By default, no actions are performed in this state.
   */
  inline static const Kind FINAL = "final";
  /** The state where sorts of enabled theories are created. */
  inline static const Kind CREATE_SORTS = "create_sorts";
  /** The state where inputs with avaible sorts are created. */
  inline static const Kind CREATE_INPUTS = "create_inputs";
  /**
   * The state where terms are created from available inputs and terms.
   *
   * **Precondition:** At least one term (input) must already have been
   *                   created.
   */
  inline static const Kind CREATE_TERMS = "create_terms";
  /**
   * The state where formulas (boolean terms) are asserted.
   *
   * **Precondition:** At least one boolean term must already have been created.
   */
  inline static const Kind ASSERT = "assert";
  /**
   * The state where satisfiability is checked, optionally under a given
   * set of assumptions.
   * formulas (boolean terms) are asserted.
   *
   * Depending on the result of the satisfiability check, by default, from this
   * state we *always* transition into the #DECIDE_SAT_UNSAT decision state.
   */
  inline static const Kind CHECK_SAT = "check_sat";
  /**
   * The choice state representing the solver state after a *sat* or *unknown*
   * result.
   *
   * @note If a solver disallows querying model values after an *unknown*
   * result, introduce a solver-specific choice state for *unknown* and
   * add a transition from #DECIDE_SAT_UNSAT to this new solver-specific state
   * accordingly.
   *
   * This state may only be entered from the #DECIDE_SAT_UNSAT decision state.
   */
  inline static const Kind SAT = "sat";
  /**
   * The choice state representing the solver state after an *unsat* result.
   *
   * This state may only be entered from the #DECIDE_SAT_UNSAT decision state.
   */
  inline static const Kind UNSAT = "unsat";
  /** The state where context levels are pushed and popped. */
  inline static const Kind PUSH_POP      = "push_pop";
  /**
   * The decision state that is reached immediately after an action is executed
   * in state #CHECK_SAT.
   * This state is where it is decided which one of the corresponding choice
   * states #SAT and #UNSAT to enter, depending on the satisfiability result.
   *
   * As a decision state, it only serves as decision point for which choice
   * state to transition into, with a single point of entrance (from state
   * #CHECK_SAT) and only specific transitions (the choices to be made) out of
   * the state.
   */
  inline static const Kind DECIDE_SAT_UNSAT = "decide-sat_unsat";

  /** The configuration kind of a state. */
  enum ConfigKind
  {
    /** Regular state. */
    REGULAR,
    /** Decision state. */
    DECISION,
    /** Choice state. */
    CHOICE,
  };

  /** Default constructor. */
  State() : d_kind(UNDEFINED), d_is_final(false) {}
  /**
   * Constructor.
   *
   * @param kind      The kind of the state.
   * @param fun       The precondition of the state.
   * @param ignore    True if the state should be ignored when adding actions
   *                  to all states (add_action_to_all_states), or adding all
   *                  configured states as next state for a transition
   *                  (add_action_to_all_states_next).
   * @param is_final  True if state is a final state.
   * @param config    The configuration kind of the state.
   */
  State(const Kind& kind,
        std::function<bool(void)> fun,
        bool ignore,
        bool is_final,
        ConfigKind config)
      : d_kind(kind),
        d_config(config),
        d_is_final(is_final),
        d_ignore(ignore),
        f_precond(fun)
  {
    MURXLA_CHECK_CONFIG(kind.size() <= MURXLA_MAX_KIND_LEN)
        << "'" << kind
        << "' exceeds maximum length for state kinds, increase limit by "
           "adjusting value of macro MURXLA_MAX_KIND_LEN in config.hpp";
  }

  /**
   * Get the kind of this state.
   * @return  The kind of this state.
   */
  const Kind& get_kind() { return d_kind; }

  /**
   * Get the configuration kind of this state.
   * @return  The configuration kind of this state.
   */
  ConfigKind get_config() { return d_config; }

  /**
   * Get the id of this state.
   * @return  The id of this state.
   */
  const uint64_t get_id() const { return d_id; }
  /**
   * Set the id of this state.
   * @param id  The unique identifier of this state.
   */
  void set_id(uint64_t id) { d_id = id; }

  /**
   * Determine if this state is a final state.
   * @return  True if this state is a final state.
   */
  bool is_final() { return d_is_final; }

  /**
   * Update the function defining the precondition for entering the state.
   * @param fun  The new precondition.
   */
  void update_precondition(std::function<bool(void)> fun) { f_precond = fun; }

  /**
   * Take one of the transitions (and execute its associated action) associated
   * with this state. Transitions with higher weight, are picked with a higher
   * probability.
   *
   * @param rng  The associated random number generator.
   * @return  The next state.
   */
  State* run(RNGenerator& rng);

  /**
   * Add action to this state.
   *
   * @param action    The action to add.
   * @param priority  The priority of the action, determines the weight, and
   *                  thus the probability to choose running the action. The
   *                  actual weight of the action is computed as
   *                  `sum/priority`, with `sum` being the sum of the
   *                  priorities of all actions in that state.
   * @param next      The state to transition into after running the action.
   *                  Optional, if not set, we stay in the current state.
   */
  void add_action(Action* action, uint32_t priority, State* next = nullptr);

  /**
   * Disable action of given `kind`. This will set the priority to 0.
   * @param kind  The kind of the action to disable.
   */
  void disable_action(Action::Kind kind);

 private:
  /** State kind. */
  const Kind& d_kind;

  /** The configuration of this state. */
  ConfigKind d_config = REGULAR;

  /** True if state is a final state. */
  bool d_is_final = false;
  /**
   * True if this state should be ignored when adding actions to all states
   * (add_action_to_all_states), or adding all configured states as next state
   * for a transition (add_action_to_all_states_next).
   */
  bool d_ignore = false;

  /** State id, assigned in the order they have been created. */
  uint64_t d_id = 0u;

  /** A function defining the precondition for entering the state. */
  std::function<bool(void)> f_precond;

  /** The actions that can be performed in this state. */
  std::vector<ActionTuple> d_actions;
  /** The weights of the actions associated with this state. */
  std::vector<uint32_t> d_weights;

  /** The associated statistics object. */
  statistics::Statistics* d_mbt_stats;
};

class FSM
{
 public:
  /** Constructor. */
  FSM(RNGenerator& rng,
      SolverSeedGenerator& sng,
      Solver* solver,
      SolverProfile& solver_profile,
      std::ostream& trace,
      SolverOptions& options,
      bool arith_linear,
      bool trace_seeds,
      bool simple_symbols,
      bool smt,
      bool fuzz_options,
      std::string fuzz_options_filter,
      statistics::Statistics* stats,
      const TheoryVector& enabled_theories,
      const TheorySet& disabled_theories,
      const std::vector<std::pair<std::string, std::string>> solver_options,
      bool in_untrace_replay_mode);

  /** Default constructor is disabled. */
  FSM() = delete;

  /** Get a reference to the associated solver manager. */
  SolverManager& get_smgr();

  /**
   * Return a mapping from Action id to Action kind.
   * Will be empty if not called after FSM::configure().
   *
   * We need this for printing statistics (shared memory) in the parent process
   * (which are filled in by the child process), to be able to map the data
   * in the statistics struct correctly to the actions. */
  std::unordered_map<uint64_t, std::string> get_action_id_mapping();

  /**
   * Create and add a new state.
   *
   * Use FSM::new_decision_state() for creating decision states,
   * FSM::new_choice_state() for creating choice states,
   * and FSM::new_final_state for creating the final state.
   *
   * @param kind      The kind of the state.
   * @param fun       The precondition of the state.
   * @param ignore    True if the state should be ignored when adding actions
   *                  to all states (add_action_to_all_states), or adding all
   *                  configured states as next state for a transition
   *                  (add_action_to_all_states_next).
   * @param is_final  True if state is a final state.
   * @param config    The configuration kind of the state.
   * @return  The created state.
   */
  State* new_state(const State::Kind& kind,
                   std::function<bool(void)> fun = nullptr,
                   bool ignore                   = false,
                   bool is_final                 = false,
                   State::ConfigKind config      = State::ConfigKind::REGULAR);
  /**
   * Create and add a new decision state.
   *
   * A decision state is a state that only serves as decision point with a
   * single point of entrance and only specific transitions (the choices to be
   * made) out of the state. A decision state is not to be extended with any
   * other actions other than the transitions that represent the choices this
   * decision state has been created for.
   * From a decision state, we may only transition into the choice states that
   * represent the valid choices for this decision.
   *
   * As an example, we use a decision state #DECIDE_SAT_UNSAT for handling
   * different solver states after a satisfiability check in state #CHECK_SAT.
   * From #CHECK_SAT, we transition into #DECIDE_SAT_UNSAT, from where we
   * transition into either choice state #SAT (when the result is *sat* or
   * *unknown*) or #UNSAT (when the result is *unsat*).
   * Each choice state configure actions to make additional queries to the
   * solver under the specific premise that a check-sat call has been issued and
   * the satisfiability result is either sat or unsat.
   *
   * @note  A decision state is never final.
   *
   * @param kind  A unique string identifying the state.
   * @param fun   The precondition for transitioning into the state.
   * @return  The created decision state.
   */
  State* new_decision_state(const std::string& kind,
                            std::function<bool(void)> fun = nullptr);

  /**
   * Create and add a new choice state.
   *
   * A choice state is a state that represents a valid choice for a specific
   * decision. It represents a very specific solver state that is a precondition
   * for specific actions (solver API calls) to be executed.
   * Choice states may only be transitioned into from their corresponding
   * decision state.
   *
   * As an example, states #SAT and #UNSAT are choice states.
   *
   * @note  A choice state can be final.
   *
   * @param kind  The kind of the state.
   * @param fun   The precondition for transitioning into the state.
   * @return  The created choice state.
   */
  State* new_choice_state(const std::string& kind,
                          std::function<bool(void)> fun = nullptr,
                          bool is_final                 = false);
  /**
   * Create and add a new final state.
   *
   * Final states are always ignored when adding actions to all states
   * (add_action_to_all_states), or adding all configured stats as next state
   * for a transition (add_action_to_all_states_next).
   *
   * @note  A final state is never a decision state.
   *
   * @param kind  The kind of the state.
   * @param fun   The precondition for transitioning into the state.
   * @return  The created choice state.
   */
  State* new_final_state(const std::string& kind,
                         std::function<bool(void)> fun = nullptr);

  /** Create new action of given type T. */
  template <class T>
  T* new_action();

  /** Disable action of kind `kind` in all states. */
  void disable_action(Action::Kind kind);

  /**
   * Add given action to all configured states (excl. the states defined in
   * d_actions_all_states_excluded and the given excluded states).
   *
   * To be processed after configuration of solver-specific states/actions.
   * The actual weight of the action is computed as priority/sum, with <sum>
   * being the sum of the priorities of all actions in that state.
   *
   * action         : The action to add to all states (with exceptions).
   * priority       : The priority of the action, determines the weight, and
   *                  thus the probability to choose running the action. The
   *                  actual weight of the action is computed as sum/priority,
   *                  with <sum> being the sum of the priorities of all actions
   *                  in that state.
   * excluded_states: The states to exclude the action from, additionally to
   *                  the states that are always excluded (defined in
   *                  d_actions_all_states_excluded).
   * next           : The state to transition into after running the action.
   *                  Optional, if not set, we stay in the current state.
   */
  template <class T>
  void add_action_to_all_states(
      T* action,
      uint32_t priority,
      const std::unordered_set<std::string>& excluded_states = {},
      State* next                                            = nullptr);

  /**
   * Add transition with given action from given state to all configured states
   * (excl. the states defined in d_actions_all_states_excluded and the given
   * excluded states).
   *
   * To be processed after configuration of solver-specific states/actions.
   * The actual weight of the action is computed as priority/sum, with <sum>
   * being the sum of the priorities of all actions in that state.
   *
   * action         : The action to add to all states (with exceptions).
   * priority       : The priority of the action, determines the weight, and
   *                  thus the probability to choose running the action. The
   *                  actual weight of the action is computed as sum/priority,
   *                  with <sum> being the sum of the priorities of all actions
   *                  in that state.
   * state          : The state to transition from.
   * excluded_states: The states to exclude the action from, additionally to
   *                  the states that are always excluded (defined in
   *                  d_actions_all_states_excluded).
   */
  template <class T>
  void add_action_to_all_states_next(
      T* action,
      uint32_t priority,
      State* state,
      const std::unordered_set<std::string>& excluded_states = {});

  /** Set given state as initial state. */
  void set_init_state(State* init_state);
  /** Check configured states for unreachable states and infinite loops. */
  void check_states();
  /** Get state with given id. */
  State* get_state(const State::Kind& kind) const;
  /** Run state machine. */
  void run();
  /** Configure state machine with base configuration. */
  void configure();
  /** Replay given trace. */
  void untrace(const std::string& trace_file_name);

  /** Print the current configuration of this FSM to stdout. */
  void print() const;

 private:
  /** The solver manager. */
  SolverManager d_smgr;
  /** The associated random number generator. */
  RNGenerator& d_rng;
  /** The set of configured states. */
  std::vector<std::unique_ptr<State>> d_states;
  /** The set of configured actions. */
  std::unordered_map<Action::Kind, std::unique_ptr<Action>> d_actions;

  /**
   * A temporary list with actions (incl. priorities, the next state and
   * excluded states) that will be added to all states (excluding states from
   * d_actions_all_states_excluded and the given excluded states) after
   * configuring solver-specific states and actions is finalized.
   */
  std::vector<
      std::tuple<Action*, uint32_t, std::unordered_set<State::Kind>, State*>>
      d_actions_all_states;
  /**
   * A temporary list with actions (incl. priorities) that will be added to
   * transition from given state to all states (excluding
   * d_actions_all_states_excluded and the given excluded states) after
   * configuring solver-specific states and actions is finalized.
   */
  std::vector<
      std::tuple<Action*, uint32_t, State*, std::unordered_set<State::Kind>>>
      d_actions_all_states_next;

  /**
   * The state kinds always to exclude when adding actions to all states
   * (add_action_to_all_states) or when adding all aconfigured states to an
   * action/transition (add_action_to_all_states_next). */
  std::unordered_set<std::string> d_actions_all_states_excluded = {
      State::NEW, State::DELETE, State::OPT, State::OPT_REQ, State::SET_LOGIC};

  /** The initial state. */
  State* d_state_init = nullptr;
  /** The current state. */
  State* d_state_cur = nullptr;

  /** True to restrict arithmetic to the linear fragment. */
  bool d_arith_linear = false;
  /** True to generate SMT-LIB compliant traces only. */
  bool d_smt = false;
  /** True to enable option fuzzing. */
  bool d_fuzz_options = false;
  /** Filter options to be fuzzed. */
  std::string d_fuzz_options_filter;

  statistics::Statistics* d_mbt_stats;

  std::vector<std::pair<std::string, std::string>> d_solver_options;

  SolverProfile& d_solver_profile;
};

template <class T>
T*
FSM::new_action()
{
  static_assert(std::is_base_of<Action, T>::value,
                "expected class (derived from) Action");
  T* action               = new T(d_smgr);
  const Action::Kind& kind = action->get_kind();
  assert(kind.size() <= MURXLA_MAX_KIND_LEN);
  if (d_actions.find(kind) == d_actions.end())
  {
    uint64_t id = d_actions.size();
    if (id >= MURXLA_MAX_N_ACTIONS)
    {
      delete action;
      throw MurxlaConfigException(
          "maximum number of actions exceeded, increase limit by adjusting "
          "value of macro MURXLA_MAX_N_ACTIONS in config.hpp");
    }
    action->set_id(id);
    d_actions[kind].reset(action);
    strncpy(d_mbt_stats->d_action_kinds[id], kind.c_str(), kind.size());
  }
  else
  {
    delete action;
  }
  return static_cast<T*>(d_actions[kind].get());
}

template <class T>
void
FSM::add_action_to_all_states(
    T* action,
    uint32_t priority,
    const std::unordered_set<State::Kind>& excluded_states,
    State* next)
{
  d_actions_all_states.push_back(
      std::tuple<Action*, uint32_t, std::unordered_set<State::Kind>, State*>(
          action, priority, excluded_states, next));
}

template <class T>
void
FSM::add_action_to_all_states_next(
    T* action,
    uint32_t priority,
    State* state,
    const std::unordered_set<State::Kind>& excluded_states)
{
  d_actions_all_states_next.push_back(
      std::tuple<Action*, uint32_t, State*, std::unordered_set<State::Kind>>(
          action, priority, state, excluded_states));
}

}  // namespace murxla
#endif
