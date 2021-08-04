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

class State
{
  friend class FSM;

 public:
  using Kind = std::string;

  /** Solver-specific states. */
  inline static const Kind UNDEFINED     = "undefined";
  inline static const Kind NEW           = "new";
  inline static const Kind OPT           = "opt";
  inline static const Kind DELETE        = "delete";
  inline static const Kind FINAL         = "final";
  inline static const Kind CREATE_SORTS  = "create_sorts";
  inline static const Kind CREATE_INPUTS = "create_inputs";
  inline static const Kind CREATE_TERMS  = "create_terms";
  inline static const Kind ASSERT        = "assert";
  inline static const Kind MODEL         = "model";
  inline static const Kind CHECK_SAT     = "check_sat";
  inline static const Kind PUSH_POP      = "push_pop";

  /** Default constructor. */
  State() : d_kind(UNDEFINED), d_is_final(false) {}
  /** Constructor. */
  State(const Kind& kind, std::function<bool(void)> fun, bool is_final)
      : d_kind(kind), d_is_final(is_final), f_precond(fun)
  {
    MURXLA_CHECK_CONFIG(kind.size() <= MURXLA_MAX_KIND_LEN)
        << "'" << kind
        << "' exceeds maximum length for state kinds, increase limit by "
           "adjusting value of macro MURXLA_MAX_KIND_LEN in config.hpp";
  }

  /** Returns the identifier of this state. */
  const Kind& get_kind() { return d_kind; }
  /** Return the id of this state. */
  const uint64_t get_id() const { return d_id; }
  /** Set the id of this state. */
  void set_id(uint64_t id) { d_id = id; }
  /** Returns true if state is a final state. */
  bool is_final() { return d_is_final; }

  /** Runs actions associated with this state. */
  State* run(RNGenerator& rng);

  /**
   * Add action to this state.
   * action  : The action to add.
   * priority: The priority of the action, determines the weight, and thus the
   *           probability to choose running the action. The actual weight of
   *           the action is computed as sum/priority, with <sum> being the
   *           sum of the priorities of all actions in that state.
   * next    : The state to transition into after running the action. Optional,
   *           if not set, we stay in the current state.
   */
  void add_action(Action* action, uint32_t priority, State* next = nullptr);

  /** Disable action of given `kind`. This will set the priority to 0. */
  void disable_action(Action::Kind kind);

 private:
  /* State kind. */
  const Kind& d_kind;
  /* True if state is a final state. */
  bool d_is_final = false;
  /* True if state represents the place holder for all states. */
  bool d_is_all = false;
  /* State id, assigned in the order they have been created. */
  uint64_t d_id = 0u;
  /* A function defining the precondition for entering the state. */
  std::function<bool(void)> f_precond;
  /* The actions that can be performed in this state. */
  std::vector<ActionTuple> d_actions;
  /* The weights of the actions associated with this state. */
  std::vector<uint32_t> d_weights;

  statistics::Statistics* d_mbt_stats;
};

class FSM
{
 public:
  /** Constructor. */
  FSM(RNGenerator& rng,
      Solver* solver,
      std::ostream& trace,
      SolverOptions& options,
      bool arith_subtyping,
      bool arith_linear,
      bool trace_seeds,
      bool simple_symbols,
      bool smt,
      statistics::Statistics* stats,
      const TheoryIdVector& enabled_theories);

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
   * kind    : A unique string identifying the state.
   * fun     : The precondition for transitioning to the next state.
   * is_final: True if this is the final state.
   */
  State* new_state(const std::string& kind,
                   std::function<bool(void)> fun = nullptr,
                   bool is_final                 = false);

  /** Create new action of given type T. */
  template <class T>
  T* new_action();

  /** Disable action of kind `kind` in all states. */
  void disable_action(Action::Kind kind);

  /**
   * Add given action to all configured states (excl. states "new" and "delete"
   * and the given excluded states).
   *
   * To be processed after configuration of solver-specific states/actions.
   * The actual weight of the action is computed as priority/sum, with <sum>
   * being the sum of the priorities of all actions in that state.
   */
  template <class T>
  void add_action_to_all_states(
      T* action,
      uint32_t priority,
      const std::unordered_set<std::string>& excluded_states = {},
      State* next                                            = nullptr);

  /* Add transition with given action from given state to all configured states
   * (excl. states "new" and "delete" and the given excluded states).
   *
   * To be processed after configuration of solver-specific states/actions.
   * The actual weight of the action is computed as priority/sum, with <sum>
   * being the sum of the priorities of all actions in that state.
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
  State* get_state(const std::string& kind) const;
  /** Run state machine. */
  void run();
  /** Configure state machine with base configuration. */
  void configure();
  /** Replay given trace. */
  void untrace(const std::string& trace_file_name);

 private:
  SolverManager d_smgr;
  RNGenerator& d_rng;
  std::vector<std::unique_ptr<State>> d_states;
  std::unordered_map<Action::Kind, std::unique_ptr<Action>> d_actions;

  /**
   * A temporary list with actions (incl. priorities, the next state and
   * excluded states) that will be added to all states (excl. states "new" and
   * "delete" and the given excluded states) after configuring solver-specific
   * states and actions is finalized.
   */
  std::vector<
      std::tuple<Action*, uint32_t, std::unordered_set<State::Kind>, State*>>
      d_actions_all_states;
  /**
   * A temporary list with actions (incl. priorities) that will be added to
   * transition from given state to all states (excl. state "new" and "delete"
   * and the given excluded states) after configuring solver-specific states
   * and actions is finalized.
   */
  std::vector<
      std::tuple<Action*, uint32_t, State*, std::unordered_set<State::Kind>>>
      d_actions_all_states_next;

  /** The initial state. */
  State* d_state_init = nullptr;
  /** The current state. */
  State* d_state_cur = nullptr;

  /** True to restrict arithmetic to the linear fragment. */
  bool d_arith_linear = false;
  /** True to generate SMT-LIB compliant traces only. */
  bool d_smt = false;

  statistics::Statistics* d_mbt_stats;
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
