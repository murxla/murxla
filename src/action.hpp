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
 * Transition from current state to next state (which may be the same as the
 * current state) while performing an action (one or more calls to the solver
 * API), with or without preconditions.
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
  inline static const Kind UNDEFINED             = "undefined";
  inline static const Kind NEW                   = "new";
  inline static const Kind DELETE                = "delete";
  inline static const Kind SET_LOGIC             = "set-logic";
  inline static const Kind MK_SORT               = "mk-sort";
  inline static const Kind MK_VALUE              = "mk-value";
  inline static const Kind MK_SPECIAL_VALUE      = "mk-special-value";
  inline static const Kind MK_CONST              = "mk-const";
  inline static const Kind MK_VAR                = "mk-var";
  inline static const Kind MK_TERM               = "mk-term";
  inline static const Kind MK_FUN                = "mk-fun";
  inline static const Kind INSTANTIATE_SORT      = "instantiate-sort";
  inline static const Kind TERM_GET_CHILDREN     = "term-get-children";
  inline static const Kind ASSERT_FORMULA        = "assert-formula";
  inline static const Kind GET_UNSAT_ASSUMPTIONS = "get-unsat-assumptions";
  inline static const Kind GET_UNSAT_CORE        = "get-unsat-core";
  inline static const Kind GET_VALUE             = "get-value";
  inline static const Kind PRINT_MODEL           = "print-model";
  inline static const Kind CHECK_SAT             = "check-sat";
  inline static const Kind CHECK_SAT_ASSUMING    = "check-sat-assuming";
  inline static const Kind PUSH                  = "push";
  inline static const Kind POP                   = "pop";
  inline static const Kind RESET                 = "reset";
  inline static const Kind RESET_ASSERTIONS      = "reset-assertions";
  inline static const Kind SET_OPTION            = "set-option";
  inline static const Kind SET_OPTION_REQ        = "set-option-req";
  inline static const Kind TRANS                 = "t_default";
  inline static const Kind TRANS_CREATE_INPUTS   = "t_inputs";
  inline static const Kind TRANS_CREATE_SORTS    = "t_sorts";
  inline static const Kind TRANS_MODEL           = "t_model";

  /**
   * Convert untraced sort or term id string to uint64_t.
   * Throws a MurxlaUntraceIdException if given string does not represent
   * a valid sort or term id.
   */
  static uint64_t untrace_str_to_id(const std::string& s);

  /** Helper to convert a sort kind string to a SortKind. */
  static SortKind get_sort_kind_from_str(const std::string& s);

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

  /** Disallow default constructor. */
  Action() = delete;
  /** Constructor. */
  Action(SolverManager& smgr,
         const Kind& kind,
         ReturnValue returns,
         bool empty = false);

  /** Destructor. */
  virtual ~Action() = default;

  /** Execute the action. */
  virtual bool run() = 0;

  /** Indicates whether action should be disabled after run() returns false. */
  bool disable() const { return d_disable; }

  /**
   * Replay an action.
   *
   * Return a vector of ids of created objects, if objects have been created,
   * and an empty vector otherwise. Needed to be able to compare ids of created
   * objects to the traced ids in the trace's return statement.
   */
  virtual std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) = 0;

  /** Return the string representing the kind of this action. */
  const Kind& get_kind() const { return d_kind; }
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
   * Generate next seed and seed solver RNG.
   * This should never be called when untracing.
   */
  void seed_solver_rng() const;

  /**
   * Get the untraced term with the given id.
   * Checks that such a term exists.
   */
  Term get_untraced_term(uint64_t id);
  /**
   * Get the untraced sort with the given id.
   * Checks that such a sort exists.
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

  bool d_disable = false;

 private:
  /* Action kind. */
  const Kind& d_kind = UNDEFINED;
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
  Transition(SolverManager& smgr, const Action::Kind& kind)
      : Action(smgr, kind, NONE, true)
  {
  }
  bool run() override { return true; }
  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
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

/* ------------------------------------------------------------------------- */

class ActionNew : public Action
{
 public:
  ActionNew(SolverManager& smgr) : Action(smgr, NEW, NONE) {}
  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionDelete : public Action
{
 public:
  ActionDelete(SolverManager& smgr) : Action(smgr, DELETE, NONE) {}
  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionSetLogic : public Action
{
 public:
  ActionSetLogic(SolverManager& smgr) : Action(smgr, SET_LOGIC, NONE) {}
  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run(const std::string& logic);
};

class ActionSetOption : public Action
{
  friend class ActionSetOptionReq;

 public:
  ActionSetOption(SolverManager& smgr) : Action(smgr, SET_OPTION, NONE) {}

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run(const std::string& opt, const std::string& value);
};

class ActionSetOptionReq : public Action
{
 public:
  ActionSetOptionReq(SolverManager& smgr) : Action(smgr, SET_OPTION_REQ, NONE)
  {
  }

  bool run() override;
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
  ActionMkSort(SolverManager& smgr);

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  std::vector<uint64_t> _run(SortKind kind);
  std::vector<uint64_t> _run(SortKind kind, const std::string& name);
  std::vector<uint64_t> _run(SortKind kind, uint32_t bw);
  std::vector<uint64_t> _run(SortKind kind, uint32_t ew, uint32_t sw);
  std::vector<uint64_t> _run(SortKind kind, const std::vector<Sort>& sorts);
  std::vector<uint64_t> _run(
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
  ActionMkTerm(SolverManager& smgr);

  bool run() override;

  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

  /** Perform checks on the created term. */
  void check_term(Term term);

  /** Create term of given operator kind. */
  bool run(Op::Kind kind);

  /** Create term of a given sort kind. */
  bool run(SortKind sort_kind);

 private:
  std::vector<uint64_t> _run(Op::Kind kind,
                             SortKind sort_kind,
                             std::vector<Term>& args,
                             const std::vector<uint32_t>& indices);
  std::vector<uint64_t> _run(Op::Kind kind,
                             SortKind sort_kind,
                             const std::vector<std::string> str_args,
                             const std::vector<Term>& args);
  std::vector<uint64_t> _run(Op::Kind kind,
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
  ActionMkConst(SolverManager& smgr) : Action(smgr, MK_CONST, ID) {}
  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

  /** Create const of given sort. */
  bool run(Sort sort);

 private:
  /** Perform checks on the created (first-order) constant. */
  void check_const(RNGenerator& rng, Term term);
  std::vector<uint64_t> _run(Sort sort, const std::string& symbol);
  /**
   * The set of unsupported sort kinds.
   * Creating constants with SORT_REGLAN not supported by any solver right now.
   */
  SortKindSet d_exclude_sort_kinds = {SORT_REGLAN};
};

class ActionMkVar : public Action
{
 public:
  ActionMkVar(SolverManager& smgr);
  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;
  std::vector<uint64_t> _run(Sort sort, const std::string& symbol);

 private:
  /** Perform checks on the created variable. */
  void check_variable(RNGenerator& rng, Term term);

  /** Unsupported variable sort kinds. */
  SortKindSet d_unsupported_sorts_kinds;
};

class ActionMkValue : public Action
{
 public:
  ActionMkValue(SolverManager& smgr) : Action(smgr, MK_VALUE, ID) {}
  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;


  /** Perform checks on created value. */
  void check_value(Term term);

  /** Create value of given sort. */
  bool run(Sort sort);

 private:
  uint64_t _run(Sort sort, bool val);
  uint64_t _run(Sort sort, const std::string& val);
  uint64_t _run(Sort sort, const std::string& val, size_t len);
  uint64_t _run(Sort sort, const std::string& v0, const std::string& v1);
  uint64_t _run(Sort sort, const std::string& val, Solver::Base base);
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
  ActionMkSpecialValue(SolverManager& smgr) : Action(smgr, MK_SPECIAL_VALUE, ID)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

  /** Create special value of given sort. */
  bool run(Sort sort);

 private:
  /** Perform checks on created special value. */
  void check_special_value(RNGenerator& rng,
                           Term term,
                           const AbsTerm::SpecialValueKind& kind);

  uint64_t _run(Sort sort, const AbsTerm::SpecialValueKind& val);
};

class ActionInstantiateSort : public Action
{
 public:
  ActionInstantiateSort(SolverManager& smgr);

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;
  Sort _run(Sort param_sort, const std::vector<Sort>& inst_sorts);

 private:
  Sort _run(
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
  ActionAssertFormula(SolverManager& smgr) : Action(smgr, ASSERT_FORMULA, NONE)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run(Term assertion);
};

class ActionCheckSat : public Action
{
 public:
  ActionCheckSat(SolverManager& smgr) : Action(smgr, CHECK_SAT, NONE) {}
  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

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
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run(const std::vector<Term>& assumptions);
};

class ActionGetUnsatAssumptions : public Action
{
 public:
  ActionGetUnsatAssumptions(SolverManager& smgr)
      : Action(smgr, GET_UNSAT_ASSUMPTIONS, NONE)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionGetUnsatCore : public Action
{
 public:
  ActionGetUnsatCore(SolverManager& smgr) : Action(smgr, GET_UNSAT_CORE, NONE)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionGetValue : public Action
{
 public:
  ActionGetValue(SolverManager& smgr);
  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run(const std::vector<Term>& terms);

  SortKindSet d_exclude_sort_kinds;
};

class ActionPush : public Action
{
 public:
  ActionPush(SolverManager& smgr) : Action(smgr, PUSH, NONE) {}
  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run(uint32_t n_levels);
};

class ActionPop : public Action
{
 public:
  ActionPop(SolverManager& smgr) : Action(smgr, POP, NONE) {}

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run(uint32_t n_levels);
};

class ActionReset : public Action
{
 public:
  ActionReset(SolverManager& smgr) : Action(smgr, RESET, NONE) {}

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionResetAssertions : public Action
{
 public:
  ActionResetAssertions(SolverManager& smgr)
      : Action(smgr, RESET_ASSERTIONS, NONE)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionPrintModel : public Action
{
 public:
  ActionPrintModel(SolverManager& smgr) : Action(smgr, PRINT_MODEL, NONE) {}

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run();
};

class ActionTermGetChildren : public Action
{
 public:
  ActionTermGetChildren(SolverManager& smgr)
      : Action(smgr, TERM_GET_CHILDREN, NONE)
  {
  }

  bool run() override;
  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  void _run(Term term);
};

class ActionMkFun : public Action
{
 public:
  ActionMkFun(SolverManager& smgr);

  bool run() override;

  std::vector<uint64_t> untrace(
      const std::vector<std::string>& tokens) override;

 private:
  std::vector<uint64_t> _run(const std::string& name,
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
