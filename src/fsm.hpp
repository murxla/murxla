#ifndef __SMTMBT__FSM_HPP_INCLUDED
#define __SMTMBT__FSM_HPP_INCLUDED

#include <cstdint>
#include <cstring>
#include <fstream>
#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "config.hpp"
#include "solver_manager.hpp"
#include "solver_option.hpp"
#include "statistics.hpp"
#include "util.hpp"

/* -------------------------------------------------------------------------- */

#define SMTMBT_TRACE                      \
  OstreamVoider()                         \
      & FSM::TraceStream(d_smgr).stream() \
            << (d_smgr.d_trace_seeds ? d_smgr.trace_seed() : "")

#define SMTMBT_TRACE_RETURN \
  OstreamVoider() & FSM::TraceStream(d_smgr).stream() << "return "

#define SMTMBT_TRACE_GET_SORT \
  OstreamVoider() & FSM::TraceStream(d_smgr).stream() << TERM_GET_SORT << " "

/* -------------------------------------------------------------------------- */

namespace smtmbt {


/* -------------------------------------------------------------------------- */

class SmtMbtFSMException : public std::exception
{
 public:
  SmtMbtFSMException(const std::string& str) : d_msg(str) {}
  SmtMbtFSMException(const std::stringstream& stream) : d_msg(stream.str()) {}
  std::string get_msg() const { return d_msg; }
  const char* what() const noexcept override { return d_msg.c_str(); }

 private:
  std::string d_msg;
};

class SmtMbtFSMUntraceException : public SmtMbtFSMException
{
 public:
  SmtMbtFSMUntraceException(const std::string& str) : SmtMbtFSMException(str) {}
  SmtMbtFSMUntraceException(const std::stringstream& stream)
      : SmtMbtFSMException(stream)
  {
  }
};

class SmtMbtFSMConfigException : public SmtMbtFSMException
{
 public:
  SmtMbtFSMConfigException(const std::string& str) : SmtMbtFSMException(str) {}
  SmtMbtFSMConfigException(const std::stringstream& stream)
      : SmtMbtFSMException(stream)
  {
  }
};

/* -------------------------------------------------------------------------- */

namespace statistics {
struct Statistics;
}

class State;

/**
 * Transition from current state to next state while performing an action
 * (a call to the solver API), with or without preconditions.
 */
class Action
{
 public:
  /**
   * Default action kinds / trace strings.
   * We use strings here to make FSM::d_actions easily extendible with
   * solver-specific actions.
   */
  static const std::string UNDEFINED;
  static const std::string NEW;
  static const std::string DELETE;
  static const std::string MK_SORT;
  static const std::string MK_VALUE;
  static const std::string MK_CONST;
  static const std::string MK_VAR;
  static const std::string MK_TERM;
  static const std::string TERM_GET_SORT;
  static const std::string TERM_CHECK_SORT;
  static const std::string ASSERT_FORMULA;
  static const std::string GET_UNSAT_ASSUMPTIONS;
  static const std::string GET_VALUE;
  static const std::string PRINT_MODEL;
  static const std::string CHECK_SAT;
  static const std::string CHECK_SAT_ASSUMING;
  static const std::string PUSH;
  static const std::string POP;
  static const std::string RESET_ASSERTIONS;
  static const std::string SET_OPTION;
  static const std::string TRANS;
  static const std::string TRANS_CREATE_INPUTS;
  static const std::string TRANS_CREATE_SORTS;
  static const std::string TRANS_MODEL;

  /** Get Action kind from string representation. */
  const std::string& get_kind() { return d_kind; };

  /** Disallow default constructor. */
  Action() = delete;
  /** Constructor. */
  Action(SolverManager& smgr,
         const std::string& kind,
         bool returns,
         bool empty = false)
      : d_rng(smgr.get_rng()),
        d_solver(smgr.get_solver()),
        d_smgr(smgr),
        d_returns(returns),
        d_is_empty(empty),
        d_kind(kind)

  {
  }

  /** Destructor. */
  virtual ~Action()  = default;

  /** Execute the action. */
  virtual bool run() = 0;

  /**
   * Replay an action.
   *
   * Returns id of created object, if an object has been created, and 0
   * otherwise. Needed to be able to compare this id to the traced id in
   * the trace's return statement.
   */
  virtual uint64_t untrace(std::vector<std::string>& tokens) = 0;

  /** Return the string representing the kind of this action. */
  const std::string& get_kind() const { return d_kind; }
  /** Return the id of this action. */
  const uint64_t get_id() const { return d_id; }
  /** Set the id of this action. */
  void set_id(uint64_t id) { d_id = id; }
  /** Returns true if this action returns a Term or Sort. */
  bool returns() const { return d_returns; }
  /**
   * Returns true if this action is empty, i.e., a transition without
   * performing any API calls.
   */
  bool empty() const { return d_is_empty; }

  /**
   * Trace a ("phantom") action 'get-sort' for given term.
   *
   * When adding terms of parameterized sort, e.g., bit-vectors or
   * floating-points, or when creating terms with a Real operator, that is
   * actually of sort Int, it can happen that the resulting term has yet unknown
   * sort, i.e., a sort that has not previously been created via ActionMksort.
   * In order to ensure that the untracer can map such sorts back correctly,
   * we have to trace a "phantom" action (= an action, that is only executed
   * when untracing) for new sorts.
   */
  void trace_get_sorts() const;

 protected:
  void reset_sat();
  /** The random number generator associated with this action. */
  RNGenerator& d_rng;
  /** The solver associated with this action. */
  Solver& d_solver;
  /** The solver manager associated with this action. */
  SolverManager& d_smgr;
  /** True if this returns a Term or Sort. */
  bool d_returns = false;
  /** True if this is an empty transition. */
  bool d_is_empty = false;

 private:
  /* Action kind. */
  const std::string& d_kind = UNDEFINED;
  /* Action id, assigned in the order they have been created. */
  uint64_t d_id = 0u;
};

/**
 * (Empty) transition from current state to next state without pre-conditions.
 */
class Transition : public Action
{
 public:
  Transition(SolverManager& smgr, const std::string& kind)
      : Action(smgr, kind, false, true)
  {
  }
  bool run() override { return true; }
  uint64_t untrace(std::vector<std::string>& tokens) override { return 0; }
};

/**
 * Default (generic) transition.
 *
 * State:      create inputs
 * Transition: if there exists at least one input
 */
class TransitionDefault : public Transition
{
 public:
  TransitionDefault(SolverManager& smgr) : Transition(smgr, TRANS) {}
};

/** "Phantom" action that is only used for untracing.  */
class UntraceAction : public Action
{
 public:
  UntraceAction(SolverManager& smgr, const std::string& kind, bool returns)
      : Action(smgr, kind, returns)
  {
  }
  bool run() override { assert(false); }  // not to be used
  uint64_t untrace(std::vector<std::string>& tokens) override { return 0; }
};

struct ActionTuple
{
  ActionTuple(Action* a, State* next) : d_action(a), d_next(next){};

  Action* d_action;
  State* d_next;
};

class State
{
  friend class FSM;

 public:
  enum Kind
  {
    UNDEFINED,
    NEW,
    OPT,
    DELETE,
    FINAL,
    CREATE_SORTS,
    CREATE_INPUTS,
    CREATE_TERMS,
    ASSERT,
    MODEL,
    CHECK_SAT,
    PUSH_POP,

    /* Boolector specific states */
    BTOR_FIX_RESET_ASSUMPTIONS,

    NUM_STATES
  };

  /** Map State kind to string representation. */
  static const std::unordered_map<Kind, std::string> s_kind_to_str;

  /** Default constructor. */
  State() : d_kind(Kind::UNDEFINED), d_is_final(false) {}
  /** Constructor. */
  State(Kind kind, std::function<bool(void)> fun, bool is_final)
      : d_kind(kind), d_is_final(is_final), f_precond(fun)
  {
  }

  /** Returns the identifier of this state. */
  const Kind get_kind() { return d_kind; }
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

 private:
  /* State kind. */
  Kind d_kind;
  /* True if state is a final state. */
  bool d_is_final = false;
  /* True if state represents the place holder for all states. */
  bool d_is_all = false;
  /* A function defining the precondition for entering the state. */
  std::function<bool(void)> f_precond;
  /* The actions that can be performed in this state. */
  std::vector<ActionTuple> d_actions;
  /* The weights of the actions associated with this state. */
  std::vector<uint32_t> d_weights;

  statistics::Statistics* d_mbt_stats;
};

/* Overload for string representation of State kind. */
std::ostream& operator<<(std::ostream& out, State::Kind kind);

class FSM
{
 public:
  class TraceStream
  {
   public:
    TraceStream(SolverManager& smgr);
    ~TraceStream();
    TraceStream(const TraceStream& astream) = default;

    std::ostream& stream();

   private:
    void flush();
    SolverManager& d_smgr;
  };

  /** Constructor. */
  FSM(RNGenerator& rng,
      Solver* solver,
      std::ostream& trace,
      SolverOptions& options,
      bool arith_linear,
      bool trace_seeds,
      bool cross_check,
      bool simple_symbols,
      bool smt,
      statistics::Statistics* stats,
      TheoryIdVector& enabled_theories);

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
   * id      : A unique string identifying the state.
   * fun     : The precondition for transitioning to the next state.
   * is_final: True if this is the final state.
   */
  State* new_state(State::Kind kind,
                   std::function<bool(void)> fun = nullptr,
                   bool is_final                 = false);

  /** Create new action of given type T. */
  template <class T>
  T* new_action();

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
      std::unordered_set<State::Kind> excluded_states = {},
      State* next                                     = nullptr);

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
      std::unordered_set<State::Kind> excluded_states = {});

  /** Set given state as initial state. */
  void set_init_state(State* init_state);
  /** Check configured states for unreachable states and infinite loops. */
  void check_states();
  /** Get state with given id. */
  State* get_state(const State::Kind kind) const;
  /** Run state machine. */
  void run();
  /** Configure state machine with base configuration. */
  void configure();
  /** Replay given trace. */
  void untrace(std::string& trace_file_name);

 private:
  SolverManager d_smgr;
  RNGenerator& d_rng;
  std::vector<std::unique_ptr<State>> d_states;
  std::unordered_map<std::string, std::unique_ptr<Action>> d_actions;

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
  const std::string& kind = action->get_kind();
  if (d_actions.find(kind) == d_actions.end())
  {
    uint64_t id = d_actions.size();
    if (id >= SMTMBT_MAX_N_ACTIONS)
    {
      delete action;
      throw SmtMbtFSMException(
          "maximum number of actions exceeded, increase limit by adjusting "
          "value "
          "of macro SMTMBT_MAX_N_ACTIONS in config.hpp");
    }
    action->set_id(id);
    d_actions[kind].reset(action);
    strncpy(d_mbt_stats->d_action_kinds[id], kind.c_str(), kind.size());
  }
  else
  {
    assert(std::string(d_mbt_stats->d_action_kinds[action->get_id()]) == kind);
    delete action;
  }
  if (kind.size() > SMTMBT_MAX_LEN_ACTION_KIND)
  {
    std::stringstream ss;
    ss << "'" << kind
       << "' exceeds maximum length for action kinds, increase limit by "
          "adjusting value of macro SMTMBT_MAX_LEN_ACTION_KIND in config.hpp";
    throw SmtMbtFSMException(ss);
  }
  return static_cast<T*>(d_actions[kind].get());
}

template <class T>
void
FSM::add_action_to_all_states(T* action,
                              uint32_t priority,
                              std::unordered_set<State::Kind> excluded_states,
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
    std::unordered_set<State::Kind> excluded_states)
{
  d_actions_all_states_next.push_back(
      std::tuple<Action*, uint32_t, State*, std::unordered_set<State::Kind>>(
          action, priority, state, excluded_states));
}

}  // namespace smtmbt
#endif
