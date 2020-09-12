#include "fsm.hpp"

#include <cassert>
#include <iostream>
#include <numeric>
#include <sstream>
#include <unordered_set>

#include "config.hpp"
#include "solver_manager.hpp"
#include "statistics.hpp"

/* -------------------------------------------------------------------------- */

namespace smtmbt {

const std::unordered_map<State::Kind, std::string> State::s_kind_to_str = {
    {State::Kind::NEW, "new"},
    {State::Kind::OPT, "opt"},
    {State::Kind::DELETE, "delete"},
    {State::Kind::FINAL, "final"},
    {State::Kind::CREATE_SORTS, "create_sorts"},
    {State::Kind::CREATE_INPUTS, "create_inputs"},
    {State::Kind::CREATE_TERMS, "create_terms"},
    {State::Kind::ASSERT, "assert"},
    {State::Kind::MODEL, "model"},
    {State::Kind::CHECK_SAT, "check_sat"},
    {State::Kind::PUSH_POP, "push_pop"},

    {State::Kind::BTOR_FIX_RESET_ASSUMPTIONS, "btor-fix-reset-assumptions"},
};

std::ostream&
operator<<(std::ostream& out, State::Kind kind)
{
  assert(State::s_kind_to_str.find(kind) != State::s_kind_to_str.end());
  out << State::s_kind_to_str.at(kind);
  return out;
}

const std::unordered_map<Action::Kind, std::string> Action::s_kind_to_str = {
    {Action::Kind::NEW, "new"},
    {Action::Kind::DELETE, "delete"},
    {Action::Kind::MK_SORT, "mk-sort"},
    {Action::Kind::MK_VALUE, "mk-value"},
    {Action::Kind::MK_CONST, "mk-const"},
    {Action::Kind::MK_VAR, "mk-var"},
    {Action::Kind::MK_TERM, "mk-term"},
    {Action::Kind::ASSERT_FORMULA, "assert-formula"},
    {Action::Kind::GET_UNSAT_ASSUMPTIONS, "get-unsat-assumptions"},
    {Action::Kind::GET_VALUE, "get-value"},
    {Action::Kind::PRINT_MODEL, "print-model"},
    {Action::Kind::CHECK_SAT, "check-sat"},
    {Action::Kind::CHECK_SAT_ASSUMING, "check-sat-assuming"},
    {Action::Kind::PUSH, "push"},
    {Action::Kind::POP, "pop"},
    {Action::Kind::RESET_ASSERTIONS, "reset-assertions"},
    {Action::Kind::SET_OPTION, "set-option"},

    /* default for all transitions */
    {Action::Kind::TRANS, "t_default"},
    {Action::Kind::TRANS_CREATE_INPUTS, "t_inputs"},
    {Action::Kind::TRANS_CREATE_SORTS, "t_sorts"},
    {Action::Kind::TRANS_MODEL, "t_model"},

    /* Boolector specific actions */
    {Action::Kind::BTOR_OPT_ITERATOR, "btor-opt-iterator"},
    {Action::Kind::BTOR_BV_ASSIGNMENT, "btor-bv-assignment"},
    {Action::Kind::BTOR_CLONE, "btor-clone"},
    {Action::Kind::BTOR_FAILED, "btor-failed"},
    {Action::Kind::BTOR_FIXATE_ASSUMPTIONS, "btor-fixate-assumptions"},
    {Action::Kind::BTOR_RESET_ASSUMPTIONS, "btor-reset-assumptions"},
    {Action::Kind::BTOR_RELEASE_ALL, "btor-release-all"},
    {Action::Kind::BTOR_SIMPLIFY, "btor-simplify"},
    {Action::Kind::BTOR_SET_SAT_SOLVER, "btor-set-sat-solver"},
    {Action::Kind::BTOR_SET_SYMBOL, "btor-set-symbol"},

    /* CVC4 specific actions */
    {Action::Kind::CVC4_CHECK_ENTAILED, "cvc4-check-entailed"},
    {Action::Kind::CVC4_SIMPLIFY, "cvc4-simplify"},
};

const Action::Kind
Action::get_kind(const std::string& s)
{
  for (const auto& it : Action::s_kind_to_str)
  {
    if (it.second == s)
    {
      return it.first;
    }
  }
  return Action::Kind::UNDEFINED;
}

void
Action::reset_sat()
{
  d_smgr.reset_sat();
  d_solver.reset_sat();
}

std::ostream&
operator<<(std::ostream& out, Action::Kind kind)
{
  assert(Action::s_kind_to_str.find(kind) != Action::s_kind_to_str.end());
  out << Action::s_kind_to_str.at(kind);
  return out;
}

/* -------------------------------------------------------------------------- */

void
State::add_action(Action* a, uint32_t priority, State* next)
{
  d_actions.emplace_back(ActionTuple(a, next == nullptr ? this : next));
  d_weights.push_back(priority);
}

/* -------------------------------------------------------------------------- */

State*
State::run(RNGenerator& rng)
{
  if (d_actions.empty())
  {
    throw SmtMbtFSMConfigException("no actions configured");
  }

  uint32_t idx      = rng.pick_weighted<uint32_t>(d_weights);
  ActionTuple& atup = d_actions[idx];

  /* record state statistics */
  ++d_mbt_stats->d_states[get_kind()];

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
  ++d_mbt_stats->d_actions[atup.d_action->get_kind()];

  if (atup.d_action->run()
      && (atup.d_next->f_precond == nullptr || atup.d_next->f_precond()))
  {
    /* record action statistics */
    ++d_mbt_stats->d_actions_ok[atup.d_action->get_kind()];

    return d_actions[idx].d_next;
  }

  return this;
}

/* -------------------------------------------------------------------------- */

FSM::FSM(RNGenerator& rng,
         Solver* solver,
         std::ostream& trace,
         SolverOptions& options,
         bool arith_linear,
         bool trace_seeds,
         bool cross_check,
         bool simple_symbols,
         bool smt,
         statistics::Statistics* stats,
         TheoryIdVector& enabled_theories)
    : d_smgr(solver,
             rng,
             trace,
             options,
             arith_linear,
             trace_seeds,
             cross_check,
             simple_symbols,
             stats,
             enabled_theories),
      d_rng(rng),
      d_arith_linear(arith_linear),
      d_smt(smt),
      d_mbt_stats(stats)
{
}

SolverManager&
FSM::get_smgr()
{
  return d_smgr;
}

State*
FSM::new_state(State::Kind kind, std::function<bool(void)> fun, bool is_final)
{
  State* new_state;
  d_states.emplace_back(new State(kind, fun, is_final));

  new_state              = d_states.back().get();
  new_state->d_mbt_stats = d_mbt_stats;
  return new_state;
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
    SMTMBT_WARN(s.get() != d_state_init
                && all_next_states.find(s.get()) == all_next_states.end())
        << "unreachable state '" << s->get_kind() << "'";
  }

  /* check for infinite loop */
  if (no_next_state
      && (no_next_state == d_state_init
          || all_next_states.find(no_next_state) != all_next_states.end()))
  {
    std::stringstream ss;
    ss << "infinite loop in state '" << no_next_state->get_kind() << "'";
    throw SmtMbtFSMConfigException(ss);
  }
}

State*
FSM::get_state(const State::Kind kind) const
{
  State* res = nullptr;
  for (const auto& s : d_states)
  {
    if (s->d_kind == kind)
    {
      res = s.get();
    }
  }
  if (res == nullptr)
  {
    std::stringstream ss;
    ss << "undefined state '" << kind << "'";
    throw SmtMbtFSMConfigException(ss);
  }
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

/* -------------------------------------------------------------------------- */

FSM::TraceStream::TraceStream(SolverManager& smgr) : d_smgr(smgr) { stream(); }

FSM::TraceStream::~TraceStream() { flush(); }

std::ostream&
FSM::TraceStream::stream()
{
  return d_smgr.get_trace();
}

void
FSM::TraceStream::flush()
{
  stream() << std::endl;
  stream().flush();
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
class TransitionCreateInputs : public Transition
{
 public:
  TransitionCreateInputs(SolverManager& smgr)
      : Transition(smgr, Action::Kind::TRANS_CREATE_INPUTS)
  {
  }
  bool run() override { return d_smgr.d_stats.inputs > 0; }
};

class TransitionCreateSorts : public Transition
{
 public:
  TransitionCreateSorts(SolverManager& smgr)
      : Transition(smgr, Action::Kind::TRANS_CREATE_SORTS)
  {
  }
  bool run() override { return d_smgr.d_stats.sorts > 0; }
};

class TransitionModel : public Transition
{
 public:
  TransitionModel(SolverManager& smgr)
      : Transition(smgr, Action::Kind::TRANS_MODEL)
  {
  }
  bool run() override { return d_smgr.d_sat_result == Solver::Result::SAT; }
};

/* ========================================================================== */
/* Default Actions                                                            */
/* ========================================================================== */

class ActionNew : public Action
{
 public:
  ActionNew(SolverManager& smgr) : Action(smgr, Action::Kind::NEW) {}

  bool run() override
  {
    if (d_solver.is_initialized()) d_solver.delete_solver();
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (!tokens.empty())
    {
      std::stringstream ss;
      ss << "unexpected argument(s) to '" << get_kind() << "'";
      throw SmtMbtFSMUntraceException(ss);
    }
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    d_solver.new_solver();
  }
};

class ActionDelete : public Action
{
 public:
  ActionDelete(SolverManager& smgr) : Action(smgr, Action::Kind::DELETE) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (!tokens.empty())
    {
      std::stringstream ss;
      ss << "unexpected argument(s) to '" << get_kind() << "'";
      throw SmtMbtFSMUntraceException(ss);
    }
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    d_smgr.clear();
    d_solver.delete_solver();
  }
};

class ActionSetOption : public Action
{
 public:
  ActionSetOption(SolverManager& smgr) : Action(smgr, Action::Kind::SET_OPTION)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    std::string opt, value;

    /**
     * We handle the following special options differently than the rest:
     * - setting these options has higher priority
     * - setting these options *must* be implemented in the solvers
     *   (even when no solver options are configured)
     * - no matter what the underlying solver API expects, we pass their
     *   Boolean values as "true" and "false" (the implementations of class
     *   Solver must support/consider this)
     */
    if (d_rng.pick_with_prob(10))
    {
      /* explicitly enable this option with higher priority */
      opt   = d_solver.get_option_name_incremental();
      value = d_smgr.d_incremental ? "false" : "true";
    }
    else if (d_rng.pick_with_prob(10))
    {
      /* explicitly enable this option with higher priority */
      opt   = d_solver.get_option_name_model_gen();
      value = d_smgr.d_model_gen ? "false" : "true";
    }
    else if (d_rng.pick_with_prob(10))
    {
      /* explicitly enable this option with higher priority */
      opt   = d_solver.get_option_name_unsat_assumptions();
      value = d_smgr.d_unsat_assumptions ? "false" : "true";
    }
    else
    {
      /* pick random option */
      std::tie(opt, value) = d_smgr.pick_option();
    }

    if (opt.empty()) /* No option available */
    {
      return false;
    }

    _run(opt, value);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (tokens.size() != 2)
    {
      std::stringstream ss;
      ss << "expected 2 arguments to '" << get_kind() << "', got "
         << tokens.size();
      throw SmtMbtFSMUntraceException(ss);
    }
    _run(tokens[0], tokens[1]);
    return 0;
  }

 private:
  void _run(const std::string& opt, const std::string& value)
  {
    SMTMBT_TRACE << get_kind() << " " << opt << " " << value;
    d_solver.set_opt(opt, value);
    d_smgr.d_incremental       = d_solver.option_incremental_enabled();
    d_smgr.d_model_gen         = d_solver.option_model_gen_enabled();
    d_smgr.d_unsat_assumptions = d_solver.option_unsat_assumptions_enabled();
  }
};

class ActionMkSort : public Action
{
 public:
  ActionMkSort(SolverManager& smgr) : Action(smgr, Action::Kind::MK_SORT) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    SortKind kind = d_smgr.pick_sort_kind_data().d_kind;
    RNGenerator::Choice pick;

    switch (kind)
    {
      case SORT_ARRAY:
      {
        // TODO: Disable nested arrays for now.
        //       Make this configurable via the solver: Solver tells FSM what
        //       sort kinds are allowed for array elements
        SortKindSet exclude_index_sorts   = {SORT_ARRAY, SORT_FUN, SORT_REGLAN};
        SortKindSet exclude_element_sorts = {SORT_ARRAY, SORT_FUN, SORT_REGLAN};
        if (!d_smgr.has_sort(exclude_index_sorts))
        {
          return false;
        }
        Sort index_sort = d_smgr.pick_sort(exclude_index_sorts, false);
        if (!d_smgr.has_sort(exclude_element_sorts))
        {
          return false;
        }
        Sort element_sort = d_smgr.pick_sort(exclude_element_sorts, false);
        _run(kind, {index_sort, element_sort});
        break;
      }

      case SORT_BV:
        _run(kind, d_rng.pick<uint32_t>(SMTMBT_BW_MIN, SMTMBT_BW_MAX));
        break;

      case SORT_FP:
        /* For now we only support Float16, Float32, Float64, Float128 */
        pick = d_rng.pick_one_of_four();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST: _run(kind, 5, 11); break;
          case RNGenerator::Choice::SECOND: _run(kind, 8, 24); break;
          case RNGenerator::Choice::THIRD: _run(kind, 11, 53); break;
          default:
            assert(pick == RNGenerator::Choice::FOURTH);
            _run(kind, 15, 113);
        }
        break;

      case SORT_FUN:
      {
        std::vector<Sort> sorts;
        // TODO: check why SORT_REGLAN is not allowed in CVC4
        SortKindSet exclude_sorts = {SORT_FUN, SORT_REGLAN};
        if (!d_smgr.has_sort(exclude_sorts))
        {
          return false;
        }
        uint32_t nsorts = d_rng.pick<uint32_t>(1, SMTMBT_MK_TERM_N_ARGS_MAX);
        for (uint32_t i = 0; i < nsorts; ++i)
        {
          sorts.push_back(d_smgr.pick_sort(exclude_sorts, false));
        }
        sorts.push_back(d_smgr.pick_sort(exclude_sorts, false));
        _run(kind, sorts);
        break;
      }

      case SORT_STRING:
      case SORT_REGLAN:
      case SORT_BOOL:
      case SORT_INT:
      case SORT_REAL:
      case SORT_RM: _run(kind); break;

      default: assert(false);
    }
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    size_t n_tokens = tokens.size();

    if (n_tokens == 0)
    {
      std::stringstream ss;
      ss << "expected at least 1 argument to '" << get_kind() << "', got "
         << n_tokens;
      throw SmtMbtFSMUntraceException(ss);
    }

    uint64_t res    = 0;
    SortKind kind   = sort_kind_from_str(tokens[0]);

    switch (kind)
    {
      case SORT_ARRAY:
      {
        if (n_tokens != 3)
        {
          std::stringstream ss;
          ss << "expected 3 arguments to '" << get_kind() << "' of sort '"
             << kind << "', got " << n_tokens;
          throw SmtMbtFSMUntraceException(ss);
        }
        std::vector<Sort> sorts;
        sorts.push_back(d_smgr.get_sort(str_to_uint32(tokens[1])));
        sorts.push_back(d_smgr.get_sort(str_to_uint32(tokens[2])));
        res = _run(kind, sorts);
        break;
      }

      case SORT_FUN:
      {
        std::vector<Sort> sorts;
        for (auto it = tokens.begin() + 1; it < tokens.end(); ++it)
        {
          sorts.push_back(d_smgr.get_sort(str_to_uint32(*it)));
        }
        res = _run(kind, sorts);
        break;
      }

      case SORT_BOOL:
      case SORT_INT:
      case SORT_REAL:
      case SORT_REGLAN:
      case SORT_RM:
      case SORT_STRING:
        if (n_tokens != 1)
        {
          std::stringstream ss;
          ss << "unexpected argument(s) to '" << get_kind() << "' of sort '"
             << kind;
          throw SmtMbtFSMUntraceException(ss);
        }
        res = _run(kind);
        break;

      case SORT_BV:
        if (n_tokens != 2)
        {
          std::stringstream ss;
          ss << "expected 1 arguments to '" << get_kind() << "' of sort '"
             << kind << "', got " << n_tokens - 1;
          throw SmtMbtFSMUntraceException(ss);
        }
        res = _run(kind, str_to_uint32(tokens[1]));
        break;

      case SORT_FP:
        if (n_tokens != 3)
        {
          std::stringstream ss;
          ss << "expected 2 arguments to '" << get_kind() << "' of sort '"
             << kind << "', got " << n_tokens - 1;
          throw SmtMbtFSMUntraceException(ss);
        }
        res = _run(kind, str_to_uint32(tokens[1]), str_to_uint32(tokens[2]));
        break;

      default:
      {
        std::stringstream ss;
        ss << "unknown sort kind " << tokens[0];
        throw SmtMbtFSMUntraceException(ss);
      }
    }
    return res;
  }

 private:
  uint64_t _run(SortKind kind)
  {
    SMTMBT_TRACE << get_kind() << " " << kind;
    Sort res = d_solver.mk_sort(kind);
    d_smgr.add_sort(res, kind);
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(SortKind kind, uint32_t bw)
  {
    SMTMBT_TRACE << get_kind() << " " << kind << " " << bw;
    assert(kind == SORT_BV);
    Sort res = d_solver.mk_sort(kind, bw);
    assert(res->get_bv_size() == bw);
    d_smgr.add_sort(res, kind);
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(SortKind kind, uint32_t ew, uint32_t sw)
  {
    SMTMBT_TRACE << get_kind() << " " << kind << " " << ew << " " << sw;
    assert(kind == SORT_FP);
    Sort res = d_solver.mk_sort(kind, ew, sw);
    assert(res->get_fp_exp_size() == ew);
    assert(res->get_fp_sig_size() == sw);
    d_smgr.add_sort(res, kind);
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(SortKind kind, const std::vector<Sort>& sorts)
  {
    std::stringstream ss;
    for (auto sort : sorts)
    {
      ss << " " << sort;
    }
    SMTMBT_TRACE << get_kind() << " " << kind << ss.str();
    Sort res = d_solver.mk_sort(kind, sorts);
    res->set_sorts(sorts);
    d_smgr.add_sort(res, kind);
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionMkTerm : public Action
{
 public:
  ActionMkTerm(SolverManager& smgr) : Action(smgr, Action::Kind::MK_TERM) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    assert(d_smgr.get_enabled_theories().find(THEORY_BOOL)
           != d_smgr.get_enabled_theories().end());
    assert(d_smgr.has_term());

    /* Op gets only picked if there already exist terms that can be used as
     * operands. */
    OpKind kind = d_smgr.pick_op_kind();
    assert(!d_smgr.d_arith_linear || kind != OP_INT_MOD);
    assert(!d_smgr.d_arith_linear || kind != OP_INT_DIV);
    assert(!d_smgr.d_arith_linear || kind != OP_REAL_DIV);
    if (kind == OP_UNDEFINED) return false;

    Op& op             = d_smgr.get_op(kind);
    int32_t arity      = op.d_arity;
    uint32_t n_params  = op.d_nparams;
    SortKind sort_kind = op.d_sort_kind;

    ++d_smgr.d_mbt_stats->d_ops[kind];

    std::vector<Term> args;
    Sort sort;

    /* Pick term arguments. */
    if (kind == OpKind::OP_BV_CONCAT)
    {
      if (!d_smgr.has_sort_bv_max(SMTMBT_BW_MAX - 1)) return false;
      sort        = d_smgr.pick_sort_bv_max(SMTMBT_BW_MAX - 1);
      uint32_t bw = SMTMBT_BW_MAX - sort->get_bv_size();
      if (!d_smgr.has_sort_bv_max(bw)) return false;
      args.push_back(d_smgr.pick_term(sort));
      do
      {
        sort = d_smgr.pick_sort_bv_max(bw);
        args.push_back(d_smgr.pick_term(sort));
        bw -= sort->get_bv_size();
      } while (d_smgr.has_sort_bv_max(bw) && d_rng.pick_one_of_three());
    }
    else if (kind == OpKind::OP_ITE)
    {
      if (!d_smgr.has_sort(SORT_BOOL)) return false;
      if (!d_smgr.has_sort(op.get_arg_sort_kind(1))) return false;
      sort = d_smgr.pick_sort(op.get_arg_sort_kind(1));
      args.push_back(d_smgr.pick_term(SORT_BOOL));
      args.push_back(d_smgr.pick_term(sort));
      args.push_back(d_smgr.pick_term(sort));
      sort_kind = sort->get_kind();
    }
    else if (kind == OpKind::OP_ARRAY_SELECT)
    {
      Sort array_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      const std::vector<Sort>& sorts = array_sort->get_sorts();
      assert(sorts.size() == 2);
      Sort index_sort = sorts[0];
      Sort element_sort = sorts[1];

      if (!d_smgr.has_term(array_sort)) return false;
      if (!d_smgr.has_term(index_sort)) return false;

      args.push_back(d_smgr.pick_term(array_sort));
      args.push_back(d_smgr.pick_term(index_sort));
      sort_kind = element_sort->get_kind();
    }
    else if (kind == OpKind::OP_ARRAY_STORE)
    {
      Sort array_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      assert(array_sort->is_array());
      const std::vector<Sort>& sorts = array_sort->get_sorts();
      assert(sorts.size() == 2);
      Sort index_sort   = sorts[0];
      Sort element_sort = sorts[1];

      if (!d_smgr.has_term(array_sort)) return false;
      if (!d_smgr.has_term(index_sort)) return false;
      if (!d_smgr.has_term(element_sort)) return false;

      args.push_back(d_smgr.pick_term(array_sort));
      args.push_back(d_smgr.pick_term(index_sort));
      args.push_back(d_smgr.pick_term(element_sort));
    }
    else if (kind == OpKind::OP_FP_FP)
    {
      if (!d_smgr.has_sort(SORT_FP)) return false;
      /* we have to pick an FP sort first here, since we don't support
       * arbitrary FP formats yet */
      sort        = d_smgr.pick_sort(SORT_FP);
      uint32_t ew = sort->get_fp_exp_size();
      uint32_t sw = sort->get_fp_sig_size();
      if (!d_smgr.has_sort_bv(1)) return false;
      if (!d_smgr.has_sort_bv(ew)) return false;
      if (!d_smgr.has_sort_bv(sw - 1)) return false;
      args.push_back(d_smgr.pick_term(d_smgr.pick_sort_bv(1)));
      args.push_back(d_smgr.pick_term(d_smgr.pick_sort_bv(ew)));
      args.push_back(d_smgr.pick_term(d_smgr.pick_sort_bv(sw - 1)));
    }
    else if (kind == OpKind::OP_FORALL || kind == OpKind::OP_EXISTS)
    {
      if (!d_smgr.has_var() || !d_smgr.has_quant_body()) return false;
      Term var  = d_smgr.pick_var();
      Term body = d_smgr.pick_quant_body();
      args.push_back(var);
      args.push_back(body);
    }
    else if (d_smgr.d_arith_linear
             && (kind == OP_INT_MUL || kind == OP_REAL_MUL))
    {
      if (!d_smgr.has_sort(sort_kind)) return false;
      sort = d_smgr.pick_sort(sort_kind);
      if (!d_smgr.has_value(sort)) return false;
      assert(arity == SMTMBT_MK_TERM_N_ARGS);
      arity = d_rng.pick<uint32_t>(SMTMBT_MK_TERM_N_ARGS_MIN(arity),
                                   SMTMBT_MK_TERM_N_ARGS_MAX);

      bool picked_non_const = false;
      /* pick arguments */
      for (int32_t i = 0; i < arity; ++i)
      {
        assert(d_smgr.has_term(sort));
        if (picked_non_const)
        {
          args.push_back(d_smgr.pick_value(sort));
          assert(args.back()->is_value());
        }
        else
        {
          args.push_back(d_smgr.pick_term(sort));
          if (!args.back()->is_value()) picked_non_const = true;
        }
      }
    }
    else if (kind == OpKind::OP_RE_RANGE)
    {
      if (!d_smgr.has_string_char_value()) return false;
      args.push_back(d_smgr.pick_string_char_value());
      args.push_back(d_smgr.pick_string_char_value());
    }
    else if (kind == OpKind::OP_UF_APPLY)
    {
      assert(d_smgr.has_term(SORT_FUN));

      Sort fun_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      assert(fun_sort->is_fun());
      if (!d_smgr.has_term(fun_sort)) return false;

      args.push_back(d_smgr.pick_term(fun_sort));

      const auto& sorts = fun_sort->get_sorts();
      /* last sort is the codomain */
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        if (!d_smgr.has_term(*it)) return false;
        args.push_back(d_smgr.pick_term(*it));
      }
      sort_kind = sorts.back()->get_kind();
    }
    else
    {
      if (arity == SMTMBT_MK_TERM_N_ARGS || arity == SMTMBT_MK_TERM_N_ARGS_BIN)
      {
        arity = d_rng.pick<uint32_t>(SMTMBT_MK_TERM_N_ARGS_MIN(arity),
                                     SMTMBT_MK_TERM_N_ARGS_MAX);
      }

      if (kind == OpKind::OP_EQUAL || kind == OpKind::OP_DISTINCT)
      {
        /* creating relations over SORT_REGLAN not supported by any solver
         * right now. */
        SortKindSet exclude = {SORT_REGLAN};
        sort                = d_smgr.pick_sort(exclude);
        if (sort == nullptr)
        {
          return false;
        }
        for (int32_t i = 0; i < arity; ++i)
        {
          assert(d_smgr.has_term(sort));
          args.push_back(d_smgr.pick_term(sort));
        }
      }
      else
      {
        /* Always pick the same sort for a given sort kind. */
        std::unordered_map<SortKind, Sort> sorts;
        SortKind skind;
        for (int32_t i = 0; i < arity; ++i)
        {
          skind   = op.get_arg_sort_kind(i);
          auto it = sorts.find(skind);
          if (it == sorts.end())
          {
            sort = d_smgr.pick_sort(skind);
            sorts.emplace(skind, sort);
          }
          else
          {
            sort = it->second;
          }
          assert(d_smgr.has_term(sort));
          args.push_back(d_smgr.pick_term(sort));
        }
      }
    }

    /* Numeral arguments for indexed operators. */
    std::vector<uint32_t> params;
    if (n_params)
    {
      uint32_t bw = sort->is_bv() ? sort->get_bv_size() : 0;
      switch (kind)
      {
        case OP_BV_EXTRACT:
          assert(sort->is_bv());
          assert(bw);
          assert(n_params == 2);
          params.push_back(d_rng.pick<uint32_t>(0, bw - 1));     // high
          params.push_back(d_rng.pick<uint32_t>(0, params[0]));  // low
          break;

        case OP_BV_REPEAT:
          assert(sort->is_bv());
          assert(bw);
          assert(n_params == 1);
          params.push_back(d_rng.pick<uint32_t>(
              1, std::max<uint32_t>(1, SMTMBT_BW_MAX / bw)));
          break;

        case OP_BV_ROTATE_LEFT:
        case OP_BV_ROTATE_RIGHT:
          assert(sort->is_bv());
          assert(bw);
          assert(n_params == 1);
          params.push_back(d_rng.pick<uint32_t>(0, bw));
          break;

        case OP_BV_SIGN_EXTEND:
        case OP_BV_ZERO_EXTEND:
          assert(sort->is_bv());
          assert(bw);
          assert(n_params == 1);
          params.push_back(d_rng.pick<uint32_t>(0, SMTMBT_BW_MAX - bw));
          break;

        case OP_FP_TO_FP_FROM_BV:
        case OP_FP_TO_FP_FROM_INT_BV:
        case OP_FP_TO_FP_FROM_UINT_BV:
          assert(sort->is_bv());
          assert(bw);
          assert(sort_kind == SORT_FP);
          assert(n_params == 2);
          /* term has FP sort, pick sort */
          if (!d_smgr.has_sort(SORT_FP)) return false;
          sort = d_smgr.pick_sort(SORT_FP, false);
          params.push_back(sort->get_fp_exp_size());
          params.push_back(sort->get_fp_sig_size());
          break;

        case OP_FP_TO_FP_FROM_FP:
          assert(sort->is_fp());
          assert(sort_kind == SORT_FP);
          assert(n_params == 2);
          /* term has new FP sort, pick sort */
          if (!d_smgr.has_sort(SORT_FP)) return false;
          sort = d_smgr.pick_sort(SORT_FP, false);
          params.push_back(sort->get_fp_exp_size());
          params.push_back(sort->get_fp_sig_size());
          break;

        case OP_FP_TO_SBV:
        case OP_FP_TO_UBV:
          assert(sort->is_fp());
          assert(sort_kind == SORT_BV);
          assert(n_params == 1);
          /* term has BV sort, pick bit-width */
          params.push_back(
              d_rng.pick<uint32_t>(1, std::max<uint32_t>(1, SMTMBT_BW_MAX)));
          break;

        case OP_FP_TO_FP_FROM_REAL:
          assert(sort->is_real());
          assert(sort_kind == SORT_FP);
          assert(n_params == 2);
          /* term has FP sort, pick sort */
          if (!d_smgr.has_sort(SORT_FP)) return false;
          sort = d_smgr.pick_sort(SORT_FP, false);
          params.push_back(sort->get_fp_exp_size());
          params.push_back(sort->get_fp_sig_size());
          break;

        case OP_INT_IS_DIV:
          assert(sort->is_int());
          assert(sort_kind == SORT_BOOL);
          assert(n_params == 1);
          params.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
          break;

        case OP_RE_LOOP:
          assert(sort->is_reglan());
          assert(sort_kind == SORT_REGLAN);
          assert(n_params == 2);
          params.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
          params.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
          break;

        case OP_RE_POW:
          assert(sort->is_reglan());
          assert(sort_kind == SORT_REGLAN);
          assert(n_params == 1);
          params.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
          break;

        default:
          /* solver-specific op */
          for (uint32_t i = 0; i < n_params; ++i)
          {
            // Note: We select a generic parameter value > 0. If solver expects
            //       a specific value range for param for given solver-specific
            //       operator, modify value accordingly in Solver::mk_term.
            //       See utils::uint32_to_value_in_range().
            params.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
          }
      }
    }

    /* Every OP with return sort SORT_ANY needs to set the kind above. */
    assert(sort_kind != SORT_ANY);
    _run(kind, sort_kind, args, params);

    ++d_smgr.d_mbt_stats->d_ops_ok[kind];

    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (tokens.size() < 3)
    {
      std::stringstream ss;
      ss << "expected at least 3 arguments (operator kind, sort id, number of "
            "arguments) to '"
         << get_kind() << ", got " << tokens.size();
      throw SmtMbtFSMUntraceException(ss);
    }

    std::vector<Term> args;
    std::vector<uint32_t> params;
    uint32_t n_tokens  = tokens.size();
    OpKind op_kind     = op_kind_from_str(tokens[0]);
    SortKind sort_kind = sort_kind_from_str(tokens[1]);
    uint32_t n_args    = str_to_uint32(tokens[2]);
    uint32_t idx       = 3;

    if (idx + n_args > n_tokens)
    {
      std::stringstream ss;
      ss << "expected " << n_args << " term arguments, got " << n_tokens - 3;
      throw SmtMbtFSMUntraceException(ss);
    }

    for (uint32_t i = 0; i < n_args; ++i, ++idx)
    {
      uint32_t id = str_to_uint32(tokens[idx]);
      Term t      = d_smgr.get_term(id);

      if (t == nullptr)
      {
        std::stringstream ss;
        ss << "unknown term id " << id;
        throw SmtMbtFSMUntraceException(ss);
      }
      args.push_back(t);
    }

    if (idx < tokens.size())
    {
      uint32_t n_params = str_to_uint32(tokens[idx++]);
      if (idx + n_params != n_tokens)
      {
        std::stringstream ss;
        ss << "expected " << n_args
           << " parameters to create indexed term, got "
           << n_tokens - 3 - n_args;
        throw SmtMbtFSMUntraceException(ss);
      }
      for (uint32_t i = 0; i < n_params; ++i, ++idx)
      {
        uint32_t param = str_to_uint32(tokens[idx]);
        params.push_back(param);
      }
    }
    return _run(op_kind, sort_kind, args, params);
  }

 private:
  uint64_t _run(OpKind kind,
                SortKind sort_kind,
                std::vector<Term> args,
                std::vector<uint32_t> params)
  {
    std::stringstream trace_str;
    trace_str << " " << kind << " " << sort_kind;
    trace_str << " " << args.size() << args;
    if (params.size())
    {
      trace_str << " " << params.size() << params;
    }
    SMTMBT_TRACE << get_kind() << trace_str.str();
    reset_sat();

    // Note: We remove the variable in _run instead of run so that we correclty
    // handle this case for untracing.
    if (kind == OP_FORALL || kind == OP_EXISTS)
    {
      d_smgr.remove_var(args[0]);
    }

    Term res = d_solver.mk_term(kind, args, params);

    /* Query solver for sort of newly created term. The returned sort is not
     * in smgr.d_sorts. Hence, we need to query d_smgr and lookup d_sorts if
     * we already have a matching sort. */
    Sort sort = d_solver.get_sort(res, sort_kind);
    sort->set_kind(sort_kind);
    /* If no matching sort is found, we use the sort returned by the solver. */
    Sort lookup = d_smgr.find_sort(sort);
    d_smgr.add_term(res, lookup, sort_kind, args);

    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionMkConst : public Action
{
 public:
  ActionMkConst(SolverManager& smgr) : Action(smgr, Action::Kind::MK_CONST) {}

  bool run() override
  {
    assert(d_solver.is_initialized());

    /* creating constants with SORT_REGLAN not supported by any solver right
     * now. */
    SortKindSet exclude = {SORT_REGLAN};

    /* Pick sort of const. */
    if (!d_smgr.has_sort(exclude)) return false;

    Sort sort          = d_smgr.pick_sort(exclude, false);
    std::string symbol = d_smgr.pick_symbol();
    /* Create const. */
    _run(sort, symbol);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (tokens.size() != 2)
    {
      std::stringstream ss;
      ss << "expected 2 arguments to '" << get_kind() << ", got "
         << tokens.size();
      throw SmtMbtFSMUntraceException(ss);
    }

    Sort sort = d_smgr.get_sort(str_to_uint32(tokens[0]));
    if (sort == nullptr)
    {
      std::stringstream ss;
      ss << "unknown sort id " << tokens[0];
      throw SmtMbtFSMUntraceException(ss);
    }
    std::string symbol = str_to_str(tokens[1]);
    return _run(sort, symbol);
  }

 private:
  uint64_t _run(Sort sort, std::string& symbol)
  {
    SMTMBT_TRACE << get_kind() << " " << sort << " \"" << symbol << "\"";
    reset_sat();
    Term res = d_solver.mk_const(sort, symbol);
    d_smgr.add_input(res, sort, sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionMkVar : public Action
{
 public:
  ActionMkVar(SolverManager& smgr) : Action(smgr, Action::Kind::MK_VAR) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    SortKindSet exclude = d_solver.get_unsupported_var_sort_kinds();

    /* Pick sort of const. */
    if (!d_smgr.has_sort(exclude)) return false;
    Sort sort          = d_smgr.pick_sort(exclude, false);
    std::string symbol = d_smgr.pick_symbol();
    /* Create var. */
    _run(sort, symbol);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (tokens.size() != 2)
    {
      std::stringstream ss;
      ss << "expected 2 arguments to '" << get_kind() << ", got "
         << tokens.size();
      throw SmtMbtFSMUntraceException(ss);
    }

    Sort sort = d_smgr.get_sort(str_to_uint32(tokens[0]));
    if (sort == nullptr)
    {
      std::stringstream ss;
      ss << "unknown sort id " << tokens[0];
      throw SmtMbtFSMUntraceException(ss);
    }
    std::string symbol = str_to_str(tokens[1]);
    return _run(sort, symbol);
  }

 private:
  uint64_t _run(Sort sort, std::string& symbol)
  {
    SMTMBT_TRACE << get_kind() << " " << sort << " \"" << symbol << "\"";
    reset_sat();
    Term res = d_solver.mk_var(sort, symbol);
    d_smgr.add_var(res, sort, sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionMkValue : public Action
{
 public:
  ActionMkValue(SolverManager& smgr) : Action(smgr, Action::Kind::MK_VALUE) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    /* Pick sort of value. */
    if (!d_smgr.has_sort()) return false;
    Sort sort          = d_smgr.pick_sort();
    SortKind sort_kind = sort->get_kind();
    RNGenerator::Choice pick;

    /* Pick value. */
    Term res;
    switch (sort_kind)
    {
      case SORT_ARRAY:
      case SORT_FUN: return false;

      case SORT_BOOL: _run(sort, d_rng.flip_coin()); break;

      case SORT_BV:
      {
        uint32_t bw = sort->get_bv_size();

        std::vector<Solver::Base> bases;
        for (auto b : d_solver.get_bases())
        {
          /* can not be expressed in hex */
          if (b == Solver::Base::HEX && bw % 4) continue;
          bases.push_back(b);
        }
        Solver::Base base =
            d_rng.pick_from_set<std::vector<Solver::Base>, Solver::Base>(bases);
        _run(sort, mk_value_bv_str(bw, base), base);
      }
      break;

      case SORT_FP:
        pick = d_rng.pick_one_of_five();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            _run<Solver::SpecialValueFP>(sort,
                                         Solver::SpecialValueFP::SMTMBT_FP_NAN);
            break;
          case RNGenerator::Choice::SECOND:
            _run<Solver::SpecialValueFP>(
                sort, Solver::SpecialValueFP::SMTMBT_FP_POS_INF);
            break;
          case RNGenerator::Choice::THIRD:
            _run<Solver::SpecialValueFP>(
                sort, Solver::SpecialValueFP::SMTMBT_FP_NEG_INF);
            break;
          case RNGenerator::Choice::FOURTH:
            _run<Solver::SpecialValueFP>(
                sort, Solver::SpecialValueFP::SMTMBT_FP_POS_ZERO);
            break;
          default:
            assert(pick == RNGenerator::Choice::FIFTH);
            _run<Solver::SpecialValueFP>(
                sort, Solver::SpecialValueFP::SMTMBT_FP_NEG_ZERO);
        }
        break;

      case SORT_INT:
        _run(sort,
             d_rng.pick_dec_int_string(
                 d_rng.pick<uint32_t>(1, SMTMBT_INT_LEN_MAX)));
        break;

      case SORT_REAL:
        pick = d_rng.pick_one_of_four();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            _run(sort,
                 d_rng.pick_dec_int_string(
                     d_rng.pick<uint32_t>(1, SMTMBT_INT_LEN_MAX)));
            break;
          case RNGenerator::Choice::SECOND:
            _run(sort,
                 d_rng.pick_dec_real_string(
                     d_rng.pick<uint32_t>(1, SMTMBT_REAL_LEN_MAX)));
            break;
          case RNGenerator::Choice::THIRD:
            _run(sort,
                 d_rng.pick_dec_rational_string(
                     d_rng.pick<uint32_t>(1, SMTMBT_REAL_LEN_MAX),
                     d_rng.pick<uint32_t>(1, SMTMBT_REAL_LEN_MAX)));
            break;
          default:
            assert(pick == RNGenerator::Choice::FOURTH);
            _run(sort,
                 d_rng.pick_dec_int_string(
                     d_rng.pick<uint32_t>(1, SMTMBT_REAL_LEN_MAX)),
                 d_rng.pick_dec_int_string(
                     d_rng.pick<uint32_t>(1, SMTMBT_REAL_LEN_MAX)));
        }
        break;

      case SORT_RM:
        pick = d_rng.pick_one_of_five();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            _run(sort, Solver::SpecialValueRM::SMTMBT_FP_RNE);
            break;
          case RNGenerator::Choice::SECOND:
            _run(sort, Solver::SpecialValueRM::SMTMBT_FP_RNA);
            break;
          case RNGenerator::Choice::THIRD:
            _run(sort, Solver::SpecialValueRM::SMTMBT_FP_RTN);
            break;
          case RNGenerator::Choice::FOURTH:
            _run(sort, Solver::SpecialValueRM::SMTMBT_FP_RTP);
            break;
          default:
            assert(pick == RNGenerator::Choice::FIFTH);
            _run<Solver::SpecialValueRM>(sort,
                                         Solver::SpecialValueRM::SMTMBT_FP_RTZ);
        }
        break;

      case SORT_STRING:
      {
        uint32_t len = d_rng.pick<uint32_t>(0, SMTMBT_STR_LEN_MAX);
        std::string value;
        if (len)
        {
          d_rng.pick_string_literal(len);
        }
        _run(sort, value);
      }
      break;

      case SORT_REGLAN:
        pick = d_rng.pick_one_of_three();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            _run(sort, Solver::SpecialValueString::SMTMBT_RE_ALL);
            break;
          case RNGenerator::Choice::SECOND:
            _run(sort, Solver::SpecialValueString::SMTMBT_RE_ALLCHAR);
            break;
          default:
            assert(pick == RNGenerator::Choice::THIRD);
            _run(sort, Solver::SpecialValueString::SMTMBT_RE_NONE);
        }
        break;

      default: assert(false);
    }

    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (tokens.empty())
    {
      std::stringstream ss;
      ss << "expected at least 1 argument to '" << get_kind() << ", got "
         << tokens.size();
      throw SmtMbtFSMUntraceException(ss);
    }

    uint64_t res = 0;
    Sort sort    = d_smgr.get_sort(str_to_uint32(tokens[0]));
    if (sort == nullptr)
    {
      std::stringstream ss;
      ss << "unknown sort id " << tokens[0];
      throw SmtMbtFSMUntraceException(ss);
    }
    switch (tokens.size())
    {
      case 3:
        if (sort->is_bv())
        {
          res = _run(sort,
                     str_to_str(tokens[1]),
                     static_cast<Solver::Base>(str_to_uint32(tokens[2])));
        }
        else
        {
          assert(sort->is_real());
          res = _run(sort, str_to_str(tokens[1]), str_to_str(tokens[2]));
        }
        break;

      default:
        if (tokens.size() != 2)
        {
          std::stringstream ss;
          ss << "expected 2 arguments to '" << get_kind() << ", got "
             << tokens.size();
          throw SmtMbtFSMUntraceException(ss);
        }
        if (tokens[1] == "true")
        {
          res = _run(sort, true);
        }
        else if (tokens[1] == "false")
        {
          res = _run(sort, false);
        }
        else if (sort->is_fp())
        {
          if (Solver::s_special_values_fp.find(tokens[1])
              == Solver::s_special_values_fp.end())
          {
            std::stringstream ss;
            ss << "unexpected special FP const value " << tokens[1];
            throw SmtMbtFSMUntraceException(ss);
          }
          res = _run(sort, Solver::s_special_values_fp.at(tokens[1]));
        }
        else if (sort->is_rm())
        {
          if (Solver::s_special_values_rm.find(tokens[1])
              == Solver::s_special_values_rm.end())
          {
            std::stringstream ss;
            ss << "unexpected special RM const value " << tokens[1];
            throw SmtMbtFSMUntraceException(ss);
          }
          res = _run(sort, Solver::s_special_values_rm.at(tokens[1]));
        }
        else if (sort->is_reglan())
        {
          if (Solver::s_special_values_string.find(tokens[1])
              == Solver::s_special_values_string.end())
          {
            std::stringstream ss;
            ss << "unexpected special String const value " << tokens[1];
            throw SmtMbtFSMUntraceException(ss);
          }
          res = _run(sort, Solver::s_special_values_string.at(tokens[1]));
        }
        else if (sort->is_string())
        {
          res = _run(sort, tokens[1]);
        }
        else
        {
          res = _run(sort, str_to_str(tokens[1]));
        }
    }

    return res;
  }

 private:
  uint64_t _run(Sort sort, bool val)
  {
    SMTMBT_TRACE << get_kind() << " " << sort << " "
                 << (val ? "true" : "false");
    reset_sat();
    Term res = d_solver.mk_value(sort, val);
    d_smgr.add_value(res, sort, sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(Sort sort, std::string val)
  {
    SMTMBT_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
    reset_sat();
    Term res = d_solver.mk_value(sort, val);
    d_smgr.add_value(res, sort, sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(Sort sort, std::string val, size_t len)
  {
    SMTMBT_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
    reset_sat();
    Term res = d_solver.mk_value(sort, val);
    d_smgr.add_value(res, sort, sort->get_kind());
    if (len == 1)
    {
      assert(sort->is_string());
      d_smgr.add_string_char_value(res);
    }
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(Sort sort, std::string v0, std::string v1)
  {
    SMTMBT_TRACE << get_kind() << " " << sort << " \"" << v0 << "\""
                 << " \"" << v1 << "\"";
    reset_sat();
    Term res = d_solver.mk_value(sort, v0, v1);
    d_smgr.add_value(res, sort, sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(Sort sort, std::string val, Solver::Base base)
  {
    SMTMBT_TRACE << get_kind() << " " << sort << " \"" << val << "\""
                 << " " << base;
    reset_sat();
    Term res = d_solver.mk_value(sort, val, base);
    d_smgr.add_value(res, sort, sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  template <typename T>
  uint64_t _run(Sort sort, T val)
  {
    SMTMBT_TRACE << get_kind() << " " << sort << " " << val;
    reset_sat();
    Term res = d_solver.mk_value(sort, val);
    d_smgr.add_value(res, sort, sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t mk_value_bv_uint64(uint32_t bw)
  {
    uint64_t val = 0u;
    if (d_rng.flip_coin())
    {
      /* use special value */
      Solver::SpecialValueBV sval =
          d_rng.pick_from_set<std::vector<Solver::SpecialValueBV>,
                              Solver::SpecialValueBV>(
              d_solver.get_special_values_bv());
      switch (sval)
      {
        case Solver::SpecialValueBV::SMTMBT_BV_ONE: val = 1u; break;
        case Solver::SpecialValueBV::SMTMBT_BV_ONES:
          val = bv_special_value_ones_uint64(bw);
          break;
        case Solver::SpecialValueBV::SMTMBT_BV_MIN_SIGNED:
          val = bv_special_value_min_signed_uint64(bw);
          break;
        case Solver::SpecialValueBV::SMTMBT_BV_MAX_SIGNED:
          val = bv_special_value_max_signed_uint64(bw);
          break;
        default:
          assert(sval == Solver::SpecialValueBV::SMTMBT_BV_ZERO);
          val = 0u;
      }
    }
    else
    {
      /* use random value */
      val = d_rng.pick<uint64_t>(0, (1 << bw) - 1);
    }
    return val;
  }

  std::string mk_value_bv_str(uint32_t bw, Solver::Base base)
  {
    std::string val;

    if (d_rng.flip_coin())
    {
      /* use special value */
      Solver::SpecialValueBV sval =
          d_rng.pick_from_set<std::vector<Solver::SpecialValueBV>,
                              Solver::SpecialValueBV>(
              d_solver.get_special_values_bv());
      switch (sval)
      {
        case Solver::SpecialValueBV::SMTMBT_BV_ONE:
          switch (base)
          {
            case Solver::Base::DEC:
              val = str_bin_to_dec(bv_special_value_one_str(bw));
              break;
            case Solver::Base::HEX:
              val = str_bin_to_hex(bv_special_value_one_str(bw));
              break;
            default:
              assert(base == Solver::Base::BIN);
              val = bv_special_value_one_str(bw);
          }
          break;
        case Solver::SpecialValueBV::SMTMBT_BV_ONES:
          switch (base)
          {
            case Solver::Base::DEC:
              val = str_bin_to_dec(bv_special_value_ones_str(bw));
              break;
            case Solver::Base::HEX:
              val = str_bin_to_hex(bv_special_value_ones_str(bw));
              break;
            default:
              assert(base == Solver::Base::BIN);
              val = bv_special_value_ones_str(bw);
          }
          break;
        case Solver::SpecialValueBV::SMTMBT_BV_MIN_SIGNED:
          switch (base)
          {
            case Solver::Base::DEC:
              val = str_bin_to_dec(bv_special_value_min_signed_str(bw));
              break;
            case Solver::Base::HEX:
              val = str_bin_to_hex(bv_special_value_min_signed_str(bw));
              break;
            default:
              assert(base == Solver::Base::BIN);
              val = bv_special_value_min_signed_str(bw);
          }
          break;
        case Solver::SpecialValueBV::SMTMBT_BV_MAX_SIGNED:
          switch (base)
          {
            case Solver::Base::DEC:
              val = str_bin_to_dec(bv_special_value_max_signed_str(bw));
              break;
            case Solver::Base::HEX:
              val = str_bin_to_hex(bv_special_value_max_signed_str(bw));
              break;
            default:
              assert(base == Solver::Base::BIN);
              val = bv_special_value_max_signed_str(bw);
          }
          break;
        default:
          assert(sval == Solver::SpecialValueBV::SMTMBT_BV_ZERO);
          switch (base)
          {
            case Solver::Base::DEC:
              val = str_bin_to_dec(bv_special_value_zero_str(bw));
              break;
            case Solver::Base::HEX:
              val = str_bin_to_hex(bv_special_value_zero_str(bw));
              break;
            default:
              assert(base == Solver::Base::BIN);
              val = bv_special_value_zero_str(bw);
          }
      }
    }
    else
    {
      /* use random value */
      switch (base)
      {
        case Solver::Base::DEC: val = d_rng.pick_dec_bin_string(bw); break;
        case Solver::Base::HEX: val = d_rng.pick_hex_bin_string(bw); break;
        default:
          assert(base == Solver::Base::BIN);
          val = d_rng.pick_bin_string(bw);
      }
    }
    return val;
  }
};

class ActionAssertFormula : public Action
{
 public:
  ActionAssertFormula(SolverManager& smgr)
      : Action(smgr, Action::Kind::ASSERT_FORMULA)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term(SORT_BOOL, 0)) return false;
    Term assertion = d_smgr.pick_term(SORT_BOOL, 0);

    _run(assertion);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (tokens.size() != 1)
    {
      std::stringstream ss;
      ss << "expected 1 argument to '" << get_kind() << ", got "
         << tokens.size();
      throw SmtMbtFSMUntraceException(ss);
    }
    Term t = d_smgr.get_term(str_to_uint32(tokens[0]));
    if (t == nullptr)
    {
      std::stringstream ss;
      ss << "unknown term id " << tokens[0];
      throw SmtMbtFSMUntraceException(ss);
    }
    _run(t);
    return 0;
  }

 private:
  void _run(Term assertion)
  {
    SMTMBT_TRACE << get_kind() << " " << assertion;
    reset_sat();
    d_solver.assert_formula(assertion);
  }
};

class ActionCheckSat : public Action
{
 public:
  ActionCheckSat(SolverManager& smgr) : Action(smgr, Action::Kind::CHECK_SAT) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.empty());
    if (!tokens.empty())
    {
      std::stringstream ss;
      ss << "unexpected argument(s) to '" << get_kind();
      throw SmtMbtFSMUntraceException(ss);
    }
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    reset_sat();
    d_smgr.d_sat_result = d_solver.check_sat();
    d_smgr.d_sat_called = true;
    d_smgr.d_n_sat_calls += 1;
    if (d_smgr.is_cross_check()) std::cout << d_smgr.d_sat_result << std::endl;

    d_smgr.d_mbt_stats->d_results[d_smgr.d_sat_result]++;
  }
};

class ActionCheckSatAssuming : public Action
{
 public:
  ActionCheckSatAssuming(SolverManager& smgr)
      : Action(smgr, Action::Kind::CHECK_SAT_ASSUMING)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_incremental) return false;
    if (!d_smgr.has_term(SORT_BOOL, 0)) return false;
    uint32_t n_assumptions =
        d_rng.pick<uint32_t>(1, SMTMBT_MAX_N_ASSUMPTIONS_CHECK_SAT);
    std::vector<Term> assumptions;
    for (uint32_t i = 0; i < n_assumptions; ++i)
    {
      assumptions.push_back(d_smgr.pick_assumption());
    }
    _run(assumptions);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (tokens.empty())
    {
      std::stringstream ss;
      ss << "expected at least 1 argument to '" << get_kind() << ", got "
         << tokens.size();
      throw SmtMbtFSMUntraceException(ss);
    }
    std::vector<Term> assumptions;
    uint32_t n_args = str_to_uint32(tokens[0]);
    for (uint32_t i = 0, idx = 1; i < n_args; ++i, ++idx)
    {
      uint32_t id = str_to_uint32(tokens[idx]);
      Term t      = d_smgr.get_term(id);
      if (t == nullptr)
      {
        std::stringstream ss;
        ss << "unknown term id " << id;
        throw SmtMbtFSMUntraceException(ss);
      }
      assumptions.push_back(t);
    }
    _run(assumptions);
    return 0;
  }

 private:
  void _run(std::vector<Term> assumptions)
  {
    SMTMBT_TRACE << get_kind() << " " << assumptions.size() << assumptions;
    reset_sat();
    d_smgr.d_sat_result = d_solver.check_sat_assuming(assumptions);
    d_smgr.d_sat_called = true;
    if (d_smgr.is_cross_check()) std::cout << d_smgr.d_sat_result << std::endl;
  }
};

class ActionGetUnsatAssumptions : public Action
{
 public:
  ActionGetUnsatAssumptions(SolverManager& smgr)
      : Action(smgr, Action::Kind::GET_UNSAT_ASSUMPTIONS)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_unsat_assumptions) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::UNSAT) return false;
    if (!d_smgr.d_incremental) return false;
    if (!d_smgr.has_assumed()) return false;
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (!tokens.empty())
    {
      std::stringstream ss;
      ss << "unexpected argument(s) to '" << get_kind();
      throw SmtMbtFSMUntraceException(ss);
    }
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    /* Note: The Terms in this vector are solver terms wrapped into Term,
     *       without sort information! */
    std::vector<Term> res = d_solver.get_unsat_assumptions();
    for (Term& fa : res)
    {
      Term t =
          d_smgr.find_term(fa, d_solver.get_sort(fa, SORT_BOOL), SORT_BOOL);
      assert(t != nullptr);
      assert(d_smgr.is_assumed(t));
      assert(d_solver.check_failed_assumption(t));
    }
    d_smgr.d_sat_called = true;
  }
};

class ActionGetValue : public Action
{
 public:
  ActionGetValue(SolverManager& smgr) : Action(smgr, Action::Kind::GET_VALUE) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;

    uint32_t n_terms = d_rng.pick<uint32_t>(1, SMTMBT_MAX_N_TERMS_GET_VALUE);
    std::vector<Term> terms;
    for (uint32_t i = 0; i < n_terms; ++i)
    {
      terms.push_back(d_smgr.pick_term());
    }
    _run(terms);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size() > 1);
    std::vector<Term> terms;
    uint32_t n_args = str_to_uint32(tokens[0]);
    for (uint32_t i = 0, idx = 1; i < n_args; ++i, ++idx)
    {
      uint32_t id = str_to_uint32(tokens[idx]);
      Term t      = d_smgr.get_term(id);
      if (t == nullptr)
      {
        std::stringstream ss;
        ss << "unknown term id " << id;
        throw SmtMbtFSMUntraceException(ss);
      }
      terms.push_back(t);
    }
    _run(terms);
    return 0;
  }

 private:
  void _run(std::vector<Term> terms)
  {
    SMTMBT_TRACE << get_kind() << " " << terms.size() << terms;
    /* Note: The Terms in this vector are solver terms wrapped into Term,
     *       without sort information! */
    std::vector<Term> res = d_solver.get_value(terms);
    assert(terms.size() == res.size());
    if (d_smgr.d_incremental && d_rng.flip_coin())
    {
      /* assume assignment and check if result is still SAT */
      std::vector<Term> assumptions;
      for (size_t i = 0, n = terms.size(); i < n; ++i)
      {
        std::vector<Term> args = {terms[i], res[i]};
        std::vector<uint32_t> params;
        assumptions.push_back(d_solver.mk_term(OP_EQUAL, args, params));
      }
      assert(d_solver.check_sat_assuming(assumptions) == Solver::Result::SAT);
    }
    else
    {
      /* add values to term database */
      for (size_t i = 0, n = terms.size(); i < n; ++i)
      {
        Sort sort = terms[i]->get_sort();
        assert(sort != nullptr);
        SortKind sort_kind = sort->get_kind();
        assert(sort_kind != SORT_ANY);
        d_smgr.add_term(res[i], sort, sort_kind);
      }
    }
  }
};

class ActionPush : public Action
{
 public:
  ActionPush(SolverManager& smgr) : Action(smgr, Action::Kind::PUSH) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    uint32_t n_levels = d_rng.pick<uint32_t>(1, SMTMBT_MAX_N_PUSH_LEVELS);
    _run(n_levels);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size() == 1);
    uint32_t n_levels = str_to_uint32(tokens[0]);
    _run(n_levels);
    return 0;
  }

 private:
  void _run(uint32_t n_levels)
  {
    SMTMBT_TRACE << get_kind() << " " << n_levels;
    reset_sat();
    d_solver.push(n_levels);
    d_smgr.d_n_push_levels += n_levels;
  }
};

class ActionPop : public Action
{
 public:
  ActionPop(SolverManager& smgr) : Action(smgr, Action::Kind::POP) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (d_smgr.d_n_push_levels == 0) return false;
    uint32_t n_levels = d_rng.pick<uint32_t>(1, d_smgr.d_n_push_levels);
    _run(n_levels);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size() == 1);
    uint32_t n_levels = str_to_uint32(tokens[0]);
    _run(n_levels);
    return 0;
  }

 private:
  void _run(uint32_t n_levels)
  {
    SMTMBT_TRACE << get_kind() << " " << n_levels;
    reset_sat();
    d_solver.pop(n_levels);
    d_smgr.d_n_push_levels -= n_levels;
  }
};

class ActionResetAssertions : public Action
{
 public:
  ActionResetAssertions(SolverManager& smgr)
      : Action(smgr, Action::Kind::RESET_ASSERTIONS)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (!tokens.empty())
    {
      std::stringstream ss;
      ss << "unexpected argument(s) to '" << get_kind();
      throw SmtMbtFSMUntraceException(ss);
    }
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    reset_sat();
    d_solver.reset_assertions();
    d_smgr.d_n_push_levels = 0;
  }
};

class ActionPrintModel : public Action
{
 public:
  ActionPrintModel(SolverManager& smgr)
      : Action(smgr, Action::Kind::PRINT_MODEL)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    if (!tokens.empty())
    {
      std::stringstream ss;
      ss << "unexpected argument(s) to '" << get_kind();
      throw SmtMbtFSMUntraceException(ss);
    }
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    d_solver.print_model();
  }
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

  auto a_mkval   = new_action<ActionMkValue>();
  auto a_mkconst = new_action<ActionMkConst>();
  auto a_mkvar   = new_action<ActionMkVar>();
  auto a_mkterm  = new_action<ActionMkTerm>();

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

  auto s_new    = new_state(State::Kind::NEW);
  auto s_opt    = new_state(State::Kind::OPT);
  auto s_delete = new_state(State::Kind::DELETE);
  auto s_final  = new_state(State::Kind::FINAL, nullptr, true);

  auto s_sorts  = new_state(State::Kind::CREATE_SORTS);
  auto s_inputs = new_state(State::Kind::CREATE_INPUTS);
  auto s_terms  = new_state(State::Kind::CREATE_TERMS,
                           [this]() { return d_smgr.has_term(); });

  auto s_assert = new_state(State::Kind::ASSERT,
                            [this]() { return d_smgr.has_term(SORT_BOOL); });

  auto s_model = new_state(State::Kind::MODEL, [this]() {
    return d_smgr.d_model_gen && d_smgr.d_sat_called
           && d_smgr.d_sat_result == Solver::Result::SAT;
  });

  auto s_sat = new_state(State::Kind::CHECK_SAT, [this]() {
    return d_smgr.d_n_sat_calls == 0 || d_smgr.d_incremental;
  });

  auto s_push_pop = new_state(State::Kind::PUSH_POP,
                              [this]() { return d_smgr.d_incremental; });

  /* --------------------------------------------------------------------- */
  /* Add actions/transitions to states                                     */
  /* --------------------------------------------------------------------- */

  /* State: new .......................................................... */
  s_new->add_action(a_new, 1, s_opt);

  /* State: opt .......................................................... */
  s_opt->add_action(a_setoption, 1);
  s_opt->add_action(t_default, 2, s_sorts);

  s_sorts->add_action(a_mksort, 1);
  s_sorts->add_action(t_sorts, 10, s_inputs);

  /* State: create inputs ................................................ */
  s_inputs->add_action(a_mksort, 100, s_sorts);
  s_inputs->add_action(a_mkval, 10);
  s_inputs->add_action(a_mkconst, 5);
  if (d_smgr.get_solver().supports_theory(THEORY_QUANT))
  {
    s_inputs->add_action(a_mkvar, 200);
  }
  s_inputs->add_action(t_inputs, 50, s_terms);
  s_inputs->add_action(t_inputs, 1000, s_sat);
  s_inputs->add_action(t_inputs, 1000, s_push_pop);

  /* State: create terms ................................................. */
  s_terms->add_action(a_mkterm, 1);
  s_terms->add_action(t_default, 100, s_assert);
  s_terms->add_action(t_default, 500, s_sat);
  s_terms->add_action(t_inputs, 1000, s_push_pop);

  /* State: assert/assume formula ........................................ */
  s_assert->add_action(a_assert, 1);
  s_assert->add_action(t_default, 50, s_delete);
  s_assert->add_action(t_default, 20, s_sat);
  s_assert->add_action(t_inputs, 50, s_push_pop);

  /* State: check sat .................................................... */
  s_sat->add_action(a_sat, 1);
  s_sat->add_action(a_sat_ass, 1);
  s_sat->add_action(t_inputs, 5, s_push_pop);
  s_sat->add_action(t_inputs, 10, s_delete);

  /* State: model ........................................................ */
  s_model->add_action(a_printmodel, 1);
  s_model->add_action(a_getvalue, 1);
  add_action_to_all_states_next(t_default, 1, s_model, {State::Kind::OPT});
  add_action_to_all_states(t_model, 10, {State::Kind::OPT}, s_model);

  /* State: push_pop ..................................................... */
  s_push_pop->add_action(a_push, 1);
  s_push_pop->add_action(a_pop, 1);
  add_action_to_all_states_next(t_default, 1, s_push_pop, {State::Kind::OPT});

  /* State: delete ....................................................... */
  s_delete->add_action(a_delete, 1, s_final);

  /* All States (with exceptions) ........................................ */
  add_action_to_all_states(a_failed, 100);
  add_action_to_all_states(a_reset_ass, 100);

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
    std::unordered_set<State::Kind> excluded_states = std::get<2>(t);
    State* next                                     = std::get<3>(t);
    for (const auto& s : d_states)
    {
      const auto id = s->get_kind();
      if (id == State::Kind::NEW || id == State::Kind::DELETE
          || id == State::Kind::FINAL
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
    std::unordered_set<State::Kind> excluded_states = std::get<3>(t);
    for (const auto& s : d_states)
    {
      const auto id = s->get_kind();
      if (id == State::Kind::NEW || id == State::Kind::DELETE
          || id == State::Kind::FINAL
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
      w = sum / w;
      i += 1;
    }
  }
}

/* ========================================================================== */
/* Replay given trace.                                                        */
/* ========================================================================== */

void
tokenize(std::string& line, std::string& id, std::vector<std::string>& tokens)
{
  std::stringstream ss;
  std::string token;
  std::stringstream tokenstream(line);
  bool open_str = false;

  /* Note: this std::getline() call also splits piped symbols that have
   *       spaces, e.g., "|a b|". We join these together again. */
  while (std::getline(tokenstream, token, ' '))
  {
    if (id.empty())
    {
      id = token;
    }
    else if (open_str)
    {
      ss << " " << token;
      if (token[token.size() - 1] == '"')
      {
        open_str = false;
        tokens.push_back(ss.str());
      }
    }
    else if (token[0] == '"' && token[token.size() - 1] != '"')
    {
      open_str = true;
      ss << token;
    }
    else
    {
      tokens.push_back(token);
    }
  }
}

void
FSM::untrace(std::string& trace_file_name)
{
  assert(!trace_file_name.empty());

  uint32_t nline   = 0;
  uint64_t ret_val = 0;
  std::string line;
  std::ifstream trace;

  trace.open(trace_file_name);
  if (!trace.is_open())
  {
    std::stringstream ss;
    ss << "untrace: unable to open file '" << trace_file_name << "'";
    throw SmtMbtFSMException(ss);
  }

  while (std::getline(trace, line))
  {
    nline += 1;
    if (line[0] == '#') continue;

    std::string id_str;
    std::vector<std::string> tokens;

    tokenize(line, id_str, tokens);

    if (id_str == "return")
    {
      if (tokens.size() != 1)
      {
        std::stringstream ss;
        ss << "untrace: " << trace_file_name << ":" << nline << " "
           << "expected single argument to 'return'";
        throw SmtMbtFSMException(ss);
      }
      uint64_t rid = str_to_uint64(tokens[0]);
      assert(rid == ret_val);
      ret_val = 0;
    }
    else if (id_str == "set-seed")
    {
      std::stringstream sss;
      for (auto t : tokens) sss << " " << t;
      sss >> d_rng.get_engine();
    }
    else
    {
      Action::Kind id = Action::get_kind(id_str);
      if (id == Action::Kind::UNDEFINED)
      {
        std::stringstream ss;
        ss << "untrace: " << trace_file_name << ":" << nline
           << ": unrecognized keyword '" << id_str << "'";
        throw SmtMbtFSMException(ss);
      }

      // TODO: we also need a register_sort in case sorts get removed while
      // delta debugging
      /* Make sure that ids for terms/sorts are the same as in the trace. */
      if (id == Action::Kind::MK_SORT || id == Action::Kind::MK_TERM
          || id == Action::Kind::MK_CONST || id == Action::Kind::MK_VALUE
          || id == Action::Kind::MK_VAR || id == Action::Kind::CVC4_SIMPLIFY)
      {
        assert(d_actions.find(id) != d_actions.end());

        try
        {
          ret_val = d_actions.at(id)->untrace(tokens);
        }
        catch (SmtMbtFSMUntraceException& e)
        {
          std::stringstream ss;
          ss << "untrace: " << trace_file_name << ":" << nline << ": "
             << e.get_msg();
          throw SmtMbtFSMException(ss);
        }

        if (std::getline(trace, line))
        {
          std::string next_id;
          std::vector<std::string> next_tokens;

          tokenize(line, next_id, next_tokens);

          if (next_id == "return")
          {
            if (next_tokens.size() != 1)
            {
              std::stringstream ss;
              ss << "untrace: " << trace_file_name << ":" << nline << " "
                 << "expected single argument to 'return'";
              throw SmtMbtFSMException(ss);
            }

            uint64_t rid = str_to_uint64(next_tokens[0]);
            if (id == Action::Kind::MK_SORT)
            {
              d_smgr.register_sort(rid, ret_val);
            }
            else
            {
              d_smgr.register_term(rid, ret_val);
            }
          }
          else
          {
            std::stringstream ss;
            ss << "untrace: " << trace_file_name << ":" << nline << " "
               << "expected 'return' statement";
            throw SmtMbtFSMException(ss);
          }
        }
        ret_val = 0;
        continue;
      }

      assert(d_actions.find(id) != d_actions.end());
      ret_val = d_actions.at(id)->untrace(tokens);
    }
  }
  if (trace.is_open()) trace.close();
}

/* ========================================================================== */
}  // namespace smtmbt
