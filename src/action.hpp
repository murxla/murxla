/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__ACTION_H
#define __MURXLA__ACTION_H

#include <cassert>
#include <iomanip>
#include <string>
#include <vector>

#include "solver/solver.hpp"

/* -------------------------------------------------------------------------- */

#define MURXLA_TRACE                                                 \
  d_solver.get_rng().reseed(d_sng.seed()),                           \
      OstreamVoider()                                                \
          & Action::TraceStream(d_smgr).stream()                     \
                << (d_smgr.d_trace_seeds ? d_smgr.trace_seed() : "") \
                << std::setw(5) << d_sng.seed() << " "

#define MURXLA_TRACE_RETURN                                         \
  OstreamVoider()                                                   \
      & Action::TraceStream(d_smgr).stream() << std::setw(6) << " " \
                                             << "return "

/* -------------------------------------------------------------------------- */

namespace murxla {

/* -------------------------------------------------------------------------- */

class RNGenerator;
class Solver;
class SolverManager;
class State;

/* -------------------------------------------------------------------------- */

/**
 * The base class for actions.
 *
 * An action defines an interaction with the solver under test, .
 * Actions are responsible for (1) randomly generating API call arguments
 * (Action::generate()); (2) executing API calls with a given set of arguments
 * (member `run()` of derived actions); and (3) replaying a traced copy of
 * the action (Action::untrace()).
 */
class Action
{
 public:
  /**
   * The kind of an action.
   *
   * This is used as action identifier when tracing.
   * We further use strings here to make FSM::d_actions easily extensible
   * with solver-specific actions.
   */
  using Kind = std::string;

  /** The undefined action. */
  inline static const Kind UNDEFINED = "undefined";

  /**
   * Convert traced sort id (`"s<id>"`) or term id (`"t<id>"`) string to id.
   *
   * Throws a MurxlaUntraceIdException if given string does not represent
   * a valid sort or term id.
   *
   * @param s  The sort or term id string.
   * @return  The sort or term id.
   */
  static uint64_t untrace_str_to_id(const std::string& s);

  /**
   * Convert a sort kind string to a SortKind.
   *
   * @param s  The sort kind string.
   * @return  The sort kind.
   */
  static SortKind get_sort_kind_from_str(const std::string& s);

  /**
   * The kind of value this action is expected to return.
   *
   * This indicates how the return value of this action is traced, which is
   * mainly relevant for error checking when untracing.
   */
  enum ReturnValue
  {
    NONE,     ///> No return trace statement expected.
    ID,       ///> Returns a single sort or term id.
    ID_LIST,  ///> Returns a list of sort or term ids.
  };

  /** The output stream wrapper for tracing actions. */
  class TraceStream
  {
   public:
    /**
     * Constructor.
     * @param smgr  The associated solver manager.
     */
    TraceStream(SolverManager& smgr);
    /** Destructor. */
    ~TraceStream();
    /**
     * Copy constructor.
     * @param astream  The trace stream to copy.
     */
    TraceStream(const TraceStream& astream) = default;

    /**
     * Get the wrapped output stream.
     * @return  The output stream.
     */
    std::ostream& stream();

   private:
    /** Flush the output stream. */
    void flush();
    /** The associated solver manager. */
    SolverManager& d_smgr;
  };

  /** Disallow default constructor. */
  Action() = delete;
  /**
   * Constructor.
   * @param smgr     The associated solver manager.
   * @param kind     The kind of the action. By convention, the static
   *                 identifier `s_name` of a derived action should be passed
   *                 as the kind.
   * @param returns  The expected value this action traces as return statement.
   * @param empty    True if this action does not execute any solver API calls.
   *                 This is intended for transitions from one state to another
   *                 that don't perform an actual action.
   */
  Action(SolverManager& smgr,
         const Kind& kind,
         ReturnValue returns,
         bool empty = false);

  /** Destructor. */
  virtual ~Action() = default;

  /**
   * Generate API call arguments and execute the action.
   * @return  True if the generation and execution was successful. False
   *          if no arguments can be generated or the action cannot be executed
   *          in the current configuration or state of the solver under test.
   */
  virtual bool generate() = 0;

  /**
   * Indicates whether an action should be disabled after generate() has
   * returned false.
   * @return  True if the action should be disabled.
   */
  bool disabled() const { return d_disable; }

  /**
   * Replay an action.
   *
   * @param tokens  The tokens of the trace statement to replay.
   * @return  A vector of ids of created objects, if objects have been created,
   *          and an empty vector otherwise. Needed to be able to compare ids
   *          of created objects to the traced ids in the trace's return
   *          statement.
   */
  virtual std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) = 0;

  /**
   * Get the string representing the kind of this action.
   * @return  The kind of this action.
   */
  const Kind& get_kind() const { return d_kind; }
  /**
   * Get the id of this action.
   * @return  The id of this action.
   */
  const uint64_t get_id() const { return d_id; }
  /**
   * Set the id of this action.
   * @param id  The id of this action to set.
   */
  void set_id(uint64_t id) { d_id = id; }
  /**
   * Get the kind of return value this action returns.
   * @return  The return value of this action.
   */
  ReturnValue returns() const { return d_returns; }
  /**
   * Determine if this action is empty.
   * @return  True if this action is empty, i.e., a transition without
   *          performing any API calls.
   */
  bool empty() const { return d_is_empty; }

  /**
   * Generate next seed and seed solver RNG.
   * This should never be called when untracing.
   */
  void seed_solver_rng() const;

  /**
   * Get the untraced term with the given id.
   * Checks that such a term exists.
   * @param id  The id of the untraced term.
   * @return  The untraced term.
   */
  Term get_untraced_term(uint64_t id);
  /**
   * Get the untraced sort with the given id.
   * Checks that such a sort exists.
   * @param id  The id of the untraced sort.
   * @return  The untraced sort.
   */
  Sort get_untraced_sort(uint64_t id);

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

  /** The random number generator associated with this action. */
  RNGenerator& d_rng;
  /** The seed generator for the RNG of the solver. */
  SolverSeedGenerator& d_sng;
  /** The solver associated with this action. */
  Solver& d_solver;
  /** The solver manager associated with this action. */
  SolverManager& d_smgr;
  /** True if this returns a Term or Sort. */
  ReturnValue d_returns = NONE;
  /** True if this is an empty transition. */
  bool d_is_empty = false;
  /** True if this action should be disabled after generate() returns false. */
  bool d_disable = false;

 private:
  /* The kind of this action. */
  const Kind& d_kind = UNDEFINED;
  /* The id of this action, assigned in the order they have been created. */
  uint64_t d_id = 0u;
};

/** A tuple of action and associated next state. */
struct ActionTuple
{
  /**
   * Constructor.
   * @param a     The action.
   * @param next  The associated next state.
   */
  ActionTuple(Action* a, State* next) : d_action(a), d_next(next){};

  /** The action. */
  Action* d_action;
  /** The next state. */
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
  Transition(SolverManager& smgr, const Action::Kind& kind)
      : Action(smgr, kind, NONE, true)
  {
  }
  bool generate() override { return true; }
  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    return {};
  }
};

/** Default (generic) transition. */
class TransitionDefault : public Transition
{
 public:
  /** The name of this transition. */
  inline static const Kind s_name = "t_default";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  TransitionDefault(SolverManager& smgr) : Transition(smgr, s_name) {}
};

/* -------------------------------------------------------------------------- */

/**
 * Transition from creating inputs to the next state if there exists at least
 * one input.
 */
class TransitionCreateInputs : public Transition
{
 public:
  /** The name of this transition. */
  inline static const Kind s_name = "t_inputs";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  TransitionCreateInputs(SolverManager& smgr) : Transition(smgr, s_name) {}

  bool generate() override;
};

/**
 * Transition from creating sorts to the next state if there exists at least
 * one sort.
 */
class TransitionCreateSorts : public Transition
{
 public:
  /** The name of this transition. */
  inline static const Kind s_name = "t_sorts";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  TransitionCreateSorts(SolverManager& smgr) : Transition(smgr, s_name) {}

  bool generate() override;
};

/* ------------------------------------------------------------------------- */

class ActionNew : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "new";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionNew(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  /** The actual execution of the action. */
  void run();
};

class ActionDelete : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "delete";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionDelete(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run();
};

class ActionSetLogic : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "set-logic";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionSetLogic(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run(const std::string& logic);
};

class ActionSetOption : public Action
{
  friend class ActionSetOptionReq;

 public:
  /** The name this action. */
  inline static const Kind s_name = "set-option";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionSetOption(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run(const std::string& opt, const std::string& value);
};

class ActionSetOptionReq : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "set-option-req";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionSetOptionReq(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

  void init(
      const std::vector<std::pair<std::string, std::string>>& solver_options,
      ActionSetOption* setoption);

 private:
  std::vector<std::pair<std::string, std::string>> d_solver_options;
  ActionSetOption* d_setoption;
};

class ActionMkSort : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "mk-sort";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionMkSort(SolverManager& smgr);

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  std::vector<uint64_t> run(SortKind kind);
  std::vector<uint64_t> run(SortKind kind, const std::string& name);
  std::vector<uint64_t> run(SortKind kind, uint32_t bw);
  std::vector<uint64_t> run(SortKind kind, uint32_t ew, uint32_t sw);
  std::vector<uint64_t> run(SortKind kind, const std::vector<Sort>& sorts);
  std::vector<uint64_t> run(
      SortKind kind,
      const std::vector<std::string>& dt_names,
      const std::vector<std::vector<Sort>>& param_sorts,
      std::vector<AbsSort::DatatypeConstructorMap>& constructors);

  /** Perform checks on the created sort. */
  void check_sort(Sort sort, const std::string& name) const;

  /** Perform checks on the created sort. */
  void check_sort(Sort sort) const;

  std::vector<uint32_t> d_n_args_weights;

  SortKindSet d_exclude_array_element_sort_kinds;
  SortKindSet d_exclude_array_index_sort_kinds;
  SortKindSet d_exclude_bag_element_sort_kinds;
  SortKindSet d_exclude_dt_sel_codomain_sort_kinds;
  SortKindSet d_exclude_fun_sort_codomain_sort_kinds;
  SortKindSet d_exclude_fun_sort_domain_sort_kinds;
  SortKindSet d_exclude_seq_element_sort_kinds;
  SortKindSet d_exclude_set_element_sort_kinds;
  SortKindSet d_exclude_sort_param_sort_kinds;
};

class ActionMkTerm : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "mk-term";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionMkTerm(SolverManager& smgr);

  bool generate() override;

  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

  /** Perform checks on the created term. */
  void check_term(Term term);

  /** Create term of given operator kind. */
  bool generate(Op::Kind kind);

  /** Create term of a given sort kind. */
  bool generate(SortKind sort_kind);

 private:
  std::vector<uint64_t> run(Op::Kind kind,
                            SortKind sort_kind,
                            std::vector<Term>& args,
                            const std::vector<uint32_t>& indices);
  std::vector<uint64_t> run(Op::Kind kind,
                            SortKind sort_kind,
                            const std::vector<std::string> str_args,
                            const std::vector<Term>& args);
  std::vector<uint64_t> run(Op::Kind kind,
                            SortKind sort_kind,
                            Sort sort,
                            const std::vector<std::string> str_args,
                            std::vector<Term>& args);

  /** Helper to create array store chains. */
  Term mk_store(const Sort& array_sort,
                const Sort& index_sort,
                const Sort& element_sort);
  /**
   * Helper to create a canonical set value of the form
   *   (union
   *     (singleton c1) ...
   *     (union (singleton c_{n-1}) (singleton c_n))))
   * where c_1 ... c_n are values ordered by id s.t. c_1 > ... > c_n, ordered
   * by term id.
   */
  Term mk_set_value(const Sort& element_sort);

  std::vector<uint32_t> d_n_args_weights;

  SortKindSet d_exclude_bag_element_sort_kinds;
  SortKindSet d_exclude_dt_match_sort_kinds;
  SortKindSet d_exclude_seq_element_sort_kinds;
  SortKindSet d_exclude_set_element_sort_kinds;
};

class ActionMkConst : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "mk-const";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionMkConst(SolverManager& smgr) : Action(smgr, s_name, ID) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

  /** Create const of given sort. */
  bool generate(Sort sort);

 private:
  /** Perform checks on the created (first-order) constant. */
  void check_const(RNGenerator& rng, Term term);
  std::vector<uint64_t> run(Sort sort, const std::string& symbol);
  /**
   * The set of unsupported sort kinds.
   * Creating constants with SORT_REGLAN not supported by any solver right now.
   */
  SortKindSet d_exclude_sort_kinds = {SORT_REGLAN};
};

class ActionMkVar : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "mk-var";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionMkVar(SolverManager& smgr);

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;
  std::vector<uint64_t> run(Sort sort, const std::string& symbol);

 private:
  /** Perform checks on the created variable. */
  void check_variable(RNGenerator& rng, Term term);

  /** Unsupported variable sort kinds. */
  SortKindSet d_unsupported_sorts_kinds;
};

class ActionMkValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "mk-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionMkValue(SolverManager& smgr) : Action(smgr, s_name, ID) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;


  /** Perform checks on created value. */
  void check_value(Term term);

  /** Create value of given sort. */
  bool generate(Sort sort);

 private:
  uint64_t run(Sort sort, bool val);
  uint64_t run(Sort sort, const std::string& val);
  uint64_t run(Sort sort, const std::string& val, size_t len);
  uint64_t run(Sort sort, const std::string& v0, const std::string& v1);
  uint64_t run(Sort sort, const std::string& val, Solver::Base base);
  /** The set of unsupported sort kinds. */
  SortKindSet d_exclude_sort_kinds = {SORT_ARRAY,
                                      SORT_FUN,
                                      SORT_BAG,
                                      SORT_DT,
                                      SORT_SEQ,
                                      SORT_SET,
                                      SORT_RM,
                                      SORT_REGLAN,
                                      SORT_UNINTERPRETED};
};

class ActionMkSpecialValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "mk-special-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionMkSpecialValue(SolverManager& smgr) : Action(smgr, s_name, ID) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

  /** Create special value of given sort. */
  bool generate(Sort sort);

 private:
  /** Perform checks on created special value. */
  void check_special_value(RNGenerator& rng,
                           Term term,
                           const AbsTerm::SpecialValueKind& kind);

  uint64_t run(Sort sort, const AbsTerm::SpecialValueKind& val);
};

class ActionInstantiateSort : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "instantiate-sort";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionInstantiateSort(SolverManager& smgr);

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;
  Sort run(Sort param_sort, const std::vector<Sort>& inst_sorts);

 private:
  Sort run(
      Sort param_sort,
      const std::vector<Sort>& sorts,
      std::unordered_map<Sort, std::vector<std::pair<std::vector<Sort>, Sort>>>&
          cache,
      std::vector<std::pair<std::string, Sort>>& to_trace);

  SortKindSet d_exclude_sort_param_sort_kinds;
};

class ActionAssertFormula : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "assert-formula";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionAssertFormula(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run(Term assertion);
};

class ActionCheckSat : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "check-sat";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionCheckSat(SolverManager& smgr) : Action(smgr, s_name, NONE) {}
  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run();
};

class ActionCheckSatAssuming : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "check-sat-assuming";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionCheckSatAssuming(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run(const std::vector<Term>& assumptions);
};

class ActionGetUnsatAssumptions : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "get-unsat-assumptions";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionGetUnsatAssumptions(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run();
};

class ActionGetUnsatCore : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "get-unsat-core";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionGetUnsatCore(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run();
};

class ActionGetValue : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "get-value";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionGetValue(SolverManager& smgr);

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run(const std::vector<Term>& terms);

  SortKindSet d_exclude_sort_kinds;
};

class ActionPush : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "push";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionPush(SolverManager& smgr) : Action(smgr, s_name, NONE) {}
  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run(uint32_t n_levels);
};

class ActionPop : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "pop";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionPop(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run(uint32_t n_levels);
};

class ActionReset : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "reset";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionReset(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run();
};

class ActionResetAssertions : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "reset-assertions";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionResetAssertions(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run();
};

class ActionPrintModel : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "print-model";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionPrintModel(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run();
};

class ActionTermGetChildren : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "term-get-children";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionTermGetChildren(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void run(Term term);
};

class ActionMkFun : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "mk-fun";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  ActionMkFun(SolverManager& smgr);

  bool generate() override;

  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  std::vector<uint64_t> run(const std::string& name,
                            const std::vector<Term>& args,
                            Term body);

  ActionMkTerm d_mkterm;
  ActionMkVar d_mkvar;

  SortKindSet d_exclude_fun_domain_sort_kinds;
  SortKindSet d_exclude_fun_codomain_sort_kinds;
};

/* -------------------------------------------------------------------------- */

}  // namespace murxla

#endif
