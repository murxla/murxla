#ifndef __MURXLA__ACTION_H
#define __MURXLA__ACTION_H

#include <cassert>
#include <string>
#include <vector>

#include "solver.hpp"

/* -------------------------------------------------------------------------- */

#define MURXLA_TRACE                         \
  OstreamVoider()                            \
      & Action::TraceStream(d_smgr).stream() \
            << (d_smgr.d_trace_seeds ? d_smgr.trace_seed() : "")

#define MURXLA_TRACE_RETURN \
  OstreamVoider() & Action::TraceStream(d_smgr).stream() << "return "

#define MURXLA_TRACE_GET_SORT \
  OstreamVoider() & Action::TraceStream(d_smgr).stream() << TERM_GET_SORT << " "

/* -------------------------------------------------------------------------- */

namespace murxla {

/* -------------------------------------------------------------------------- */

using ActionKind = std::string;

class RNGenerator;
class SolverManager;
class State;

/* -------------------------------------------------------------------------- */

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
  static const ActionKind UNDEFINED;
  static const ActionKind NEW;
  static const ActionKind DELETE;
  static const ActionKind MK_SORT;
  static const ActionKind MK_VALUE;
  static const ActionKind MK_SPECIAL_VALUE;
  static const ActionKind MK_CONST;
  static const ActionKind MK_VAR;
  static const ActionKind MK_TERM;
  static const ActionKind TERM_GET_SORT;
  static const ActionKind TERM_CHECK_SORT;
  static const ActionKind ASSERT_FORMULA;
  static const ActionKind GET_UNSAT_ASSUMPTIONS;
  static const ActionKind GET_VALUE;
  static const ActionKind PRINT_MODEL;
  static const ActionKind CHECK_SAT;
  static const ActionKind CHECK_SAT_ASSUMING;
  static const ActionKind PUSH;
  static const ActionKind POP;
  static const ActionKind RESET_ASSERTIONS;
  static const ActionKind SET_OPTION;
  static const ActionKind TRANS;
  static const ActionKind TRANS_CREATE_INPUTS;
  static const ActionKind TRANS_CREATE_SORTS;
  static const ActionKind TRANS_MODEL;

  /**
   * Convert untraced sort or term id string to uint64_t.
   * Throws a MurxlaUntraceIdException if given string does not represent
   * a valid sort or term id.
   */
  static uint64_t untrace_str_to_id(const std::string& s);

  enum ReturnValue
  {
    NONE,
    ID,
    ID_LIST,
  };

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

  /** Get Action kind from string representation. */
  const ActionKind& get_kind() { return d_kind; };

  /** Disallow default constructor. */
  Action() = delete;
  /** Constructor. */
  Action(SolverManager& smgr,
         const ActionKind& kind,
         ReturnValue returns,
         bool empty = false);

  /** Destructor. */
  virtual ~Action() = default;

  /** Execute the action. */
  virtual bool run() = 0;

  /**
   * Replay an action.
   *
   * Return a vector of ids of created objects, if objects have been created,
   * and an empty vector otherwise. Needed to be able to compare ids of created
   * objects to the traced ids in the trace's return statement.
   */
  virtual std::vector<uint64_t> untrace(std::vector<std::string>& tokens) = 0;

  /** Return the string representing the kind of this action. */
  const ActionKind& get_kind() const { return d_kind; }
  /** Return the id of this action. */
  const uint64_t get_id() const { return d_id; }
  /** Set the id of this action. */
  void set_id(uint64_t id) { d_id = id; }
  /** Return the kind of return value this action returns. */
  ReturnValue returns() const { return d_returns; }
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
  /**
   * Reset solver and solver manager state into assert mode.
   *
   * After this call, actions that call
   *   - Solver::get_model()
   *   - Solver::get_unsat_assumptions()
   *   - Solver::get_unsat_core() and
   *   - Solver::get_proof()
   * may not be run until after the next SAT call.
   */
  void reset_sat();
  /** Helper to convert a sort kind string to a SortKind. */
  SortKind get_sort_kind_from_str(std::string& s);

  /** The random number generator associated with this action. */
  RNGenerator& d_rng;
  /** The solver associated with this action. */
  Solver& d_solver;
  /** The solver manager associated with this action. */
  SolverManager& d_smgr;
  /** True if this returns a Term or Sort. */
  ReturnValue d_returns = NONE;
  /** True if this is an empty transition. */
  bool d_is_empty = false;

 private:
  /* Action kind. */
  const ActionKind& d_kind = UNDEFINED;
  /* Action id, assigned in the order they have been created. */
  uint64_t d_id = 0u;
};

struct ActionTuple
{
  ActionTuple(Action* a, State* next) : d_action(a), d_next(next){};

  Action* d_action;
  State* d_next;
};

/* -------------------------------------------------------------------------- */
/* Default Transitions (= empty actions)                                      */
/* -------------------------------------------------------------------------- */

/**
 * (Empty) transition from current state to next state without pre-conditions.
 */
class Transition : public Action
{
 public:
  Transition(SolverManager& smgr, const ActionKind& kind)
      : Action(smgr, kind, NONE, true)
  {
  }
  bool run() override { return true; }
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    return {};
  }
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

/* -------------------------------------------------------------------------- */

/**
 * Transition from creating inputs to the next state.
 *
 * State:      create inputs
 * Transition: if there exists at least one input
 */
class TransitionCreateInputs : public Transition
{
 public:
  TransitionCreateInputs(SolverManager& smgr)
      : Transition(smgr, TRANS_CREATE_INPUTS)
  {
  }
  bool run() override;
};

class TransitionCreateSorts : public Transition
{
 public:
  TransitionCreateSorts(SolverManager& smgr)
      : Transition(smgr, TRANS_CREATE_SORTS)
  {
  }
  bool run() override;
};

class TransitionModel : public Transition
{
 public:
  TransitionModel(SolverManager& smgr) : Transition(smgr, TRANS_MODEL) {}
  bool run() override;
};

/* -------------------------------------------------------------------------- */
/* Phantom Actions (untracing only)                                           */
/* -------------------------------------------------------------------------- */

/** "Phantom" action that is only used for untracing.  */
class UntraceAction : public Action
{
 public:
  UntraceAction(SolverManager& smgr,
                const ActionKind& kind,
                ReturnValue returns)
      : Action(smgr, kind, returns)
  {
  }

  bool run() override { assert(false); }  // not to be used
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    return {};
  }
};

/* -------------------------------------------------------------------------- */

class ActionTermGetSort : public UntraceAction
{
 public:
  ActionTermGetSort(SolverManager& smgr)
      : UntraceAction(smgr, TERM_GET_SORT, ID)
  {
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  std::vector<uint64_t> _run(Term term);
};

class ActionTermCheckSort : public Action
{
 public:
  ActionTermCheckSort(SolverManager& smgr) : Action(smgr, TERM_CHECK_SORT, NONE)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run(Term term);
};

/* -------------------------------------------------------------------------- */

class ActionNew : public Action
{
 public:
  ActionNew(SolverManager& smgr) : Action(smgr, NEW, NONE) {}
  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionDelete : public Action
{
 public:
  ActionDelete(SolverManager& smgr) : Action(smgr, DELETE, NONE) {}
  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionSetOption : public Action
{
 public:
  ActionSetOption(SolverManager& smgr) : Action(smgr, SET_OPTION, NONE) {}

  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run(const std::string& opt, const std::string& value);
};

class ActionMkSort : public Action
{
 public:
  ActionMkSort(SolverManager& smgr) : Action(smgr, MK_SORT, ID) {}

  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  uint64_t _run(SortKind kind);
  uint64_t _run(SortKind kind, uint32_t bw);
  uint64_t _run(SortKind kind, uint32_t ew, uint32_t sw);
  uint64_t _run(SortKind kind, const std::vector<Sort>& sorts);
};

class ActionMkTerm : public Action
{
 public:
  ActionMkTerm(SolverManager& smgr) : Action(smgr, MK_TERM, ID) {}
  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  std::vector<uint64_t> _run(OpKind kind,
                             SortKind sort_kind,
                             std::vector<Term> args,
                             std::vector<uint32_t> params);
};

class ActionMkConst : public Action
{
 public:
  ActionMkConst(SolverManager& smgr) : Action(smgr, MK_CONST, ID) {}
  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  std::vector<uint64_t> _run(Sort sort, std::string& symbol);
};

class ActionMkVar : public Action
{
 public:
  ActionMkVar(SolverManager& smgr) : Action(smgr, MK_VAR, ID) {}
  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  std::vector<uint64_t> _run(Sort sort, std::string& symbol);
};

class ActionMkValue : public Action
{
 public:
  ActionMkValue(SolverManager& smgr) : Action(smgr, MK_VALUE, ID) {}
  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  uint64_t _run(Sort sort, bool val);
  uint64_t _run(Sort sort, std::string val);
  uint64_t _run(Sort sort, std::string val, size_t len);
  uint64_t _run(Sort sort, std::string v0, std::string v1);
  uint64_t _run(Sort sort, std::string val, Solver::Base base);
};

class ActionMkSpecialValue : public Action
{
 public:
  ActionMkSpecialValue(SolverManager& smgr) : Action(smgr, MK_SPECIAL_VALUE, ID)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  uint64_t _run(Sort sort, const Solver::SpecialValueKind& val);
};

class ActionAssertFormula : public Action
{
 public:
  ActionAssertFormula(SolverManager& smgr) : Action(smgr, ASSERT_FORMULA, NONE)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run(Term assertion);
};

class ActionCheckSat : public Action
{
 public:
  ActionCheckSat(SolverManager& smgr) : Action(smgr, CHECK_SAT, NONE) {}
  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionCheckSatAssuming : public Action
{
 public:
  ActionCheckSatAssuming(SolverManager& smgr)
      : Action(smgr, CHECK_SAT_ASSUMING, NONE)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run(std::vector<Term> assumptions);
};

class ActionGetUnsatAssumptions : public Action
{
 public:
  ActionGetUnsatAssumptions(SolverManager& smgr)
      : Action(smgr, GET_UNSAT_ASSUMPTIONS, NONE)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionGetValue : public Action
{
 public:
  ActionGetValue(SolverManager& smgr) : Action(smgr, GET_VALUE, ID_LIST) {}
  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  std::vector<uint64_t> _run(std::vector<Term> terms);
};

class ActionPush : public Action
{
 public:
  ActionPush(SolverManager& smgr) : Action(smgr, PUSH, NONE) {}
  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run(uint32_t n_levels);
};

class ActionPop : public Action
{
 public:
  ActionPop(SolverManager& smgr) : Action(smgr, POP, NONE) {}

  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run(uint32_t n_levels);
};

class ActionResetAssertions : public Action
{
 public:
  ActionResetAssertions(SolverManager& smgr)
      : Action(smgr, RESET_ASSERTIONS, NONE)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionPrintModel : public Action
{
 public:
  ActionPrintModel(SolverManager& smgr) : Action(smgr, PRINT_MODEL, NONE) {}

  bool run() override;
  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override;

 private:
  void _run();
};

/* -------------------------------------------------------------------------- */

}  // namespace murxla

#endif
