#include "fsm.hpp"

#include <cassert>
#include <iostream>
#include <numeric>
#include <sstream>
#include <unordered_set>

#include "solver_manager.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */
/* Action                                                                     */
/* -------------------------------------------------------------------------- */

const ActionKind Action::UNDEFINED             = "undefined";
const ActionKind Action::NEW                   = "new";
const ActionKind Action::DELETE                = "delete";
const ActionKind Action::MK_SORT               = "mk-sort";
const ActionKind Action::MK_VALUE              = "mk-value";
const ActionKind Action::MK_SPECIAL_VALUE      = "mk-special-value";
const ActionKind Action::MK_CONST              = "mk-const";
const ActionKind Action::MK_VAR                = "mk-var";
const ActionKind Action::MK_TERM               = "mk-term";
const ActionKind Action::TERM_GET_SORT         = "term-get-sort";
const ActionKind Action::TERM_CHECK_SORT       = "term-check-sort";
const ActionKind Action::ASSERT_FORMULA        = "assert-formula";
const ActionKind Action::GET_UNSAT_ASSUMPTIONS = "get-unsat-assumptions";
const ActionKind Action::GET_VALUE             = "get-value";
const ActionKind Action::PRINT_MODEL           = "print-model";
const ActionKind Action::CHECK_SAT             = "check-sat";
const ActionKind Action::CHECK_SAT_ASSUMING    = "check-sat-assuming";
const ActionKind Action::PUSH                  = "push";
const ActionKind Action::POP                   = "pop";
const ActionKind Action::RESET_ASSERTIONS      = "reset-assertions";
const ActionKind Action::SET_OPTION            = "set-option";
const ActionKind Action::TRANS                 = "t_default";
const ActionKind Action::TRANS_CREATE_INPUTS   = "t_inputs";
const ActionKind Action::TRANS_CREATE_SORTS    = "t_sorts";
const ActionKind Action::TRANS_MODEL           = "t_model";

void
Action::trace_get_sorts() const
{
  std::vector<Term>& pending = d_smgr.get_pending_get_sorts();
  for (const auto& term : pending)
  {
    MURXLA_TRACE_GET_SORT << term;
    MURXLA_TRACE_RETURN << term->get_sort();
  }
  pending.clear();
}

void
Action::reset_sat()
{
  d_smgr.reset_sat();
  d_solver.reset_sat();
}

/* -------------------------------------------------------------------------- */
/* State                                                                      */
/* -------------------------------------------------------------------------- */

const StateKind State::UNDEFINED     = "undefined";
const StateKind State::NEW           = "new";
const StateKind State::OPT           = "opt";
const StateKind State::DELETE        = "delete";
const StateKind State::FINAL         = "final";
const StateKind State::CREATE_SORTS  = "create_sorts";
const StateKind State::CREATE_INPUTS = "create_inputs";
const StateKind State::CREATE_TERMS  = "create_terms";
const StateKind State::ASSERT        = "assert";
const StateKind State::MODEL         = "model";
const StateKind State::CHECK_SAT     = "check_sat";
const StateKind State::PUSH_POP      = "push_pop";

void
State::add_action(Action* a, uint32_t priority, State* next)
{
  d_actions.emplace_back(ActionTuple(a, next == nullptr ? this : next));
  d_weights.push_back(priority);
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
         bool arith_linear,
         bool trace_seeds,
         bool cross_check,
         bool simple_symbols,
         bool smt,
         statistics::Statistics* stats,
         const TheoryIdVector& enabled_theories)
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
FSM::new_state(const StateKind& kind,
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
FSM::get_state(const StateKind& kind) const
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

SortKind
get_sort_kind_from_str(std::string& s)
{
  SortKind res = sort_kind_from_str(s);
  MURXLA_CHECK_CONFIG(res != SORT_ANY) << "unknown sort kind '" << s << "'";
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
      : Transition(smgr, TRANS_CREATE_INPUTS)
  {
  }
  bool run() override { return d_smgr.d_stats.inputs > 0; }
};

class TransitionCreateSorts : public Transition
{
 public:
  TransitionCreateSorts(SolverManager& smgr)
      : Transition(smgr, TRANS_CREATE_SORTS)
  {
  }
  bool run() override { return d_smgr.d_stats.sorts > 0; }
};

class TransitionModel : public Transition
{
 public:
  TransitionModel(SolverManager& smgr) : Transition(smgr, TRANS_MODEL) {}
  bool run() override { return d_smgr.d_sat_result == Solver::Result::SAT; }
};

/* ========================================================================== */
/* Phantom Actions (untracing only)                                           */
/* ========================================================================== */

class ActionTermGetSort : public UntraceAction
{
 public:
  ActionTermGetSort(SolverManager& smgr)
      : UntraceAction(smgr, TERM_GET_SORT, ID)
  {
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term t = d_smgr.get_term(FSM::untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(t, tokens[0]);
    return _run(t);
  }

 private:
  std::vector<uint64_t> _run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    Sort res = term->get_sort();
    MURXLA_TRACE_RETURN << res;
    return {res->get_id()};
  }
};

/* ========================================================================== */
/* Default Actions                                                            */
/* ========================================================================== */

class ActionNew : public Action
{
 public:
  ActionNew(SolverManager& smgr) : Action(smgr, NEW, NONE) {}

  bool run() override
  {
    if (d_solver.is_initialized()) d_solver.delete_solver();
    _run();
    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    _run();
    return {};
  }

 private:
  void _run()
  {
    MURXLA_TRACE << get_kind();
    d_solver.new_solver();
  }
};

class ActionDelete : public Action
{
 public:
  ActionDelete(SolverManager& smgr) : Action(smgr, DELETE, NONE) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    _run();
    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    _run();
    return {};
  }

 private:
  void _run()
  {
    MURXLA_TRACE << get_kind();
    d_smgr.clear();
    d_solver.delete_solver();
  }
};

class ActionSetOption : public Action
{
 public:
  ActionSetOption(SolverManager& smgr) : Action(smgr, SET_OPTION, NONE) {}

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

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
    _run(tokens[0], tokens[1]);
    return {};
  }

 private:
  void _run(const std::string& opt, const std::string& value)
  {
    MURXLA_TRACE << get_kind() << " " << opt << " " << value;
    d_solver.set_opt(opt, value);
    d_smgr.d_incremental       = d_solver.option_incremental_enabled();
    d_smgr.d_model_gen         = d_solver.option_model_gen_enabled();
    d_smgr.d_unsat_assumptions = d_solver.option_unsat_assumptions_enabled();
  }
};

class ActionMkSort : public Action
{
 public:
  ActionMkSort(SolverManager& smgr) : Action(smgr, MK_SORT, ID) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    SortKind kind = d_smgr.pick_sort_kind_data().d_kind;
    RNGenerator::Choice pick;

    ++d_smgr.d_mbt_stats->d_sorts[kind];

    switch (kind)
    {
      case SORT_ARRAY:
      {
        SortKindSet exclude_index_sorts =
            d_solver.get_unsupported_array_index_sort_kinds();
        SortKindSet exclude_element_sorts =
            d_solver.get_unsupported_array_element_sort_kinds();

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
        _run(kind, d_rng.pick<uint32_t>(MURXLA_BW_MIN, MURXLA_BW_MAX));
        break;

      case SORT_FP:
        // TODO: support arbitrary formats (for now we only support Float16,
        //       Float32, Float64, Float128
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
        SortKindSet exclude_sorts =
            d_solver.get_unsupported_fun_domain_sort_kinds();
        if (!d_smgr.has_sort(exclude_sorts))
        {
          return false;
        }
        uint32_t nsorts = d_rng.pick<uint32_t>(1, MURXLA_MK_TERM_N_ARGS_MAX);
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

    ++d_smgr.d_mbt_stats->d_sorts_ok[kind];

    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    size_t n_tokens = tokens.size();

    MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);

    uint64_t res    = 0;
    SortKind kind   = get_sort_kind_from_str(tokens[0]);
    const auto& theories = d_smgr.get_enabled_theories();

    switch (kind)
    {
      case SORT_ARRAY:
      {
        MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                           || theories.find(THEORY_ARRAY) != theories.end())
            << "solver does not support theory of arrays";
        MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(3, n_tokens, kind);
        std::vector<Sort> sorts;
        sorts.push_back(d_smgr.get_sort(FSM::untrace_str_to_id(tokens[1])));
        MURXLA_CHECK_TRACE(sorts[0] != nullptr)
            << "unknown sort id '" << tokens[1] << "' as argument to "
            << get_kind();
        sorts.push_back(d_smgr.get_sort(FSM::untrace_str_to_id(tokens[2])));
        MURXLA_CHECK_TRACE(sorts[1] != nullptr)
            << "unknown sort id '" << tokens[2] << "' as argument to "
            << get_kind();
        res = _run(kind, sorts);
        break;
      }

      case SORT_FUN:
      {
        MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                           || theories.find(THEORY_UF) != theories.end())
            << "solver does not support theory of UF";
        std::vector<Sort> sorts;
        for (auto it = tokens.begin() + 1; it < tokens.end(); ++it)
        {
          Sort s = d_smgr.get_sort(FSM::untrace_str_to_id(*it));
          MURXLA_CHECK_TRACE(s != nullptr) << "unknown sort id '" << *it
                                           << "' as argument to " << get_kind();
          sorts.push_back(s);
        }
        res = _run(kind, sorts);
        break;
      }

      case SORT_BOOL:
        MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
        res = _run(kind);
        break;

      case SORT_INT:
        MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                           || theories.find(THEORY_INT) != theories.end())
            << "solver does not support theory of integers";
        MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
        res = _run(kind);
        break;

      case SORT_REAL:
        MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                           || theories.find(THEORY_REAL) != theories.end())
            << "solver does not support theory of reals";
        MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
        res = _run(kind);
        break;

      case SORT_REGLAN:
        MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                           || theories.find(THEORY_STRING) != theories.end())
            << "solver does not support theory of strings";
        MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
        res = _run(kind);
        break;

      case SORT_RM:
        MURXLA_CHECK_TRACE(theories.find(THEORY_FP) != theories.end()
                           || theories.find(THEORY_FP) != theories.end())
            << "solver does not support theory of floating-point arithmetic";
        MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
        res = _run(kind);
        break;

      case SORT_STRING:
        MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                           || theories.find(THEORY_STRING) != theories.end())
            << "solver does not support theory of strings";
        MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
        res = _run(kind);
        break;

      case SORT_BV:
        MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                           || theories.find(THEORY_BV) != theories.end())
            << "solver does not support theory of bit-vectors";
        MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(2, n_tokens, kind);
        res = _run(kind, str_to_uint32(tokens[1]));
        break;

      case SORT_FP:
        MURXLA_CHECK_TRACE(theories.find(THEORY_FP) != theories.end()
                           || theories.find(THEORY_FP) != theories.end())
            << "solver does not support theory of floating-point arithmetic";
        MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(3, n_tokens, kind);
        res = _run(kind, str_to_uint32(tokens[1]), str_to_uint32(tokens[2]));
        break;

      default: MURXLA_CHECK_TRACE(false) << "unknown sort kind " << tokens[0];
    }
    return {res};
  }

 private:
  uint64_t _run(SortKind kind)
  {
    MURXLA_TRACE << get_kind() << " " << kind;
    Sort res = d_solver.mk_sort(kind);
    d_smgr.add_sort(res, kind);
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(SortKind kind, uint32_t bw)
  {
    MURXLA_TRACE << get_kind() << " " << kind << " " << bw;
    assert(kind == SORT_BV);
    Sort res = d_solver.mk_sort(kind, bw);
    assert(res->get_bv_size() == bw);
    d_smgr.add_sort(res, kind);
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(SortKind kind, uint32_t ew, uint32_t sw)
  {
    MURXLA_TRACE << get_kind() << " " << kind << " " << ew << " " << sw;
    assert(kind == SORT_FP);
    Sort res = d_solver.mk_sort(kind, ew, sw);
    assert(res->get_fp_exp_size() == ew);
    assert(res->get_fp_sig_size() == sw);
    d_smgr.add_sort(res, kind);
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(SortKind kind, const std::vector<Sort>& sorts)
  {
    std::stringstream ss;
    for (auto sort : sorts)
    {
      ss << " " << sort;
    }
    MURXLA_TRACE << get_kind() << " " << kind << ss.str();
    Sort res = d_solver.mk_sort(kind, sorts);
    res->set_sorts(sorts);
    d_smgr.add_sort(res, kind);
    assert(res->get_sorts().size() == sorts.size());
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionMkTerm : public Action
{
 public:
  ActionMkTerm(SolverManager& smgr) : Action(smgr, MK_TERM, ID) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    assert(d_smgr.get_enabled_theories().find(THEORY_BOOL)
           != d_smgr.get_enabled_theories().end());
    assert(d_smgr.has_term());

    /* Op gets only picked if there already exist terms that can be used as
     * operands. */
    const OpKind& kind = d_smgr.pick_op_kind();
    assert(!d_smgr.d_arith_linear || kind != Op::INT_MOD);
    assert(!d_smgr.d_arith_linear || kind != Op::INT_DIV);
    assert(!d_smgr.d_arith_linear || kind != Op::REAL_DIV);
    if (kind == Op::UNDEFINED) return false;

    Op& op             = d_smgr.get_op(kind);
    int32_t arity      = op.d_arity;
    uint32_t n_params  = op.d_nparams;
    SortKind sort_kind = op.d_sort_kind;

    ++d_smgr.d_mbt_stats->d_ops[op.d_id];

    std::vector<Term> args;
    std::vector<uint32_t> params;

    /* Pick term arguments. */
    if (kind == Op::BV_CONCAT)
    {
      assert(!n_params);
      if (!d_smgr.has_sort_bv_max(MURXLA_BW_MAX - 1)) return false;
      Sort sort   = d_smgr.pick_sort_bv_max(MURXLA_BW_MAX - 1);
      uint32_t bw = MURXLA_BW_MAX - sort->get_bv_size();
      if (!d_smgr.has_sort_bv_max(bw)) return false;
      args.push_back(d_smgr.pick_term(sort));
      do
      {
        sort = d_smgr.pick_sort_bv_max(bw);
        args.push_back(d_smgr.pick_term(sort));
        bw -= sort->get_bv_size();
      } while (d_smgr.has_sort_bv_max(bw) && d_rng.pick_one_of_three());
    }
    else if (kind == Op::ITE)
    {
      assert(!n_params);
      assert(d_smgr.has_sort(SORT_BOOL));
      assert(d_smgr.has_sort(op.get_arg_sort_kind(1)));
      Sort sort = d_smgr.pick_sort(op.get_arg_sort_kind(1));
      args.push_back(d_smgr.pick_term(SORT_BOOL));
      args.push_back(d_smgr.pick_term(sort));
      args.push_back(d_smgr.pick_term(sort));
      sort_kind = sort->get_kind();
    }
    else if (kind == Op::ARRAY_SELECT)
    {
      assert(!n_params);
      Sort array_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      const std::vector<Sort>& sorts = array_sort->get_sorts();
      assert(sorts.size() == 2);
      Sort index_sort = sorts[0];
      Sort element_sort = sorts[1];

      assert(d_smgr.has_term(array_sort));
      if (!d_smgr.has_term(index_sort)) return false;

      args.push_back(d_smgr.pick_term(array_sort));
      args.push_back(d_smgr.pick_term(index_sort));
      sort_kind = element_sort->get_kind();
    }
    else if (kind == Op::ARRAY_STORE)
    {
      assert(!n_params);
      Sort array_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      assert(array_sort->is_array());
      assert(array_sort->get_id());
      const std::vector<Sort>& sorts = array_sort->get_sorts();
      assert(sorts.size() == 2);
      Sort index_sort   = sorts[0];
      Sort element_sort = sorts[1];

      assert(d_smgr.has_term(array_sort));
      if (!d_smgr.has_term(index_sort)) return false;
      if (!d_smgr.has_term(element_sort)) return false;

      args.push_back(d_smgr.pick_term(array_sort));
      args.push_back(d_smgr.pick_term(index_sort));
      args.push_back(d_smgr.pick_term(element_sort));
    }
    else if (kind == Op::FP_FP)
    {
      assert(!n_params);
      /* we have to pick an FP sort first here, since we don't support
       * arbitrary FP formats yet */
      if (!d_smgr.has_sort(SORT_FP)) return false;
      Sort sort   = d_smgr.pick_sort(SORT_FP, false);
      uint32_t ew = sort->get_fp_exp_size();
      uint32_t sw = sort->get_fp_sig_size();
      if (!d_smgr.has_sort_bv(1)) return false;
      if (!d_smgr.has_sort_bv(ew)) return false;
      if (!d_smgr.has_sort_bv(sw - 1)) return false;
      args.push_back(d_smgr.pick_term(d_smgr.pick_sort_bv(1)));
      args.push_back(d_smgr.pick_term(d_smgr.pick_sort_bv(ew)));
      args.push_back(d_smgr.pick_term(d_smgr.pick_sort_bv(sw - 1)));
    }
    else if (kind == Op::FP_TO_FP_FROM_BV)
    {
      assert(n_params == 2);
      /* we have to pick an FP sort first here, since we don't support
       * arbitrary FP formats yet */
      if (!d_smgr.has_sort(SORT_FP)) return false;
      Sort sort   = d_smgr.pick_sort(SORT_FP, false);
      uint32_t ew = sort->get_fp_exp_size();
      uint32_t sw = sort->get_fp_sig_size();
      uint32_t bw = ew + sw;
      if (!d_smgr.has_sort_bv(bw)) return false;
      args.push_back(d_smgr.pick_term(d_smgr.pick_sort_bv(bw)));

      /* pick index parameters */
      params.push_back(ew);
      params.push_back(sw);
    }
    else if (kind == Op::FORALL || kind == Op::EXISTS)
    {
      assert(!n_params);
      assert(d_smgr.has_var());
      assert(d_smgr.has_quant_body());
      Term var  = d_smgr.pick_var();
      Term body = d_smgr.pick_quant_body();
      args.push_back(var);
      args.push_back(body);
    }
    else if (d_smgr.d_arith_linear
             && (kind == Op::INT_MUL || kind == Op::REAL_MUL))
    {
      assert(!n_params);
      assert(d_smgr.has_sort(sort_kind));
      Sort sort = d_smgr.pick_sort(sort_kind);
      if (!d_smgr.has_value(sort)) return false;
      assert(arity == MURXLA_MK_TERM_N_ARGS);
      arity = d_rng.pick<uint32_t>(MURXLA_MK_TERM_N_ARGS_MIN(arity),
                                   MURXLA_MK_TERM_N_ARGS_MAX);

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
    else if (kind == Op::RE_RANGE)
    {
      assert(!n_params);
      if (!d_smgr.has_string_char_value()) return false;
      args.push_back(d_smgr.pick_string_char_value());
      args.push_back(d_smgr.pick_string_char_value());
    }
    else if (kind == Op::UF_APPLY)
    {
      assert(!n_params);
      assert(d_smgr.has_term(SORT_FUN));

      Sort fun_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      assert(fun_sort->is_fun());
      assert(d_smgr.has_term(fun_sort));

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
      if (arity == MURXLA_MK_TERM_N_ARGS || arity == MURXLA_MK_TERM_N_ARGS_BIN)
      {
        arity = d_rng.pick<uint32_t>(MURXLA_MK_TERM_N_ARGS_MIN(arity),
                                     MURXLA_MK_TERM_N_ARGS_MAX);
      }

      if (kind == Op::EQUAL || kind == Op::DISTINCT)
      {
        /* creating relations over SORT_REGLAN not supported by any solver
         * right now. */
        SortKindSet exclude = {SORT_REGLAN};
        Sort sort           = d_smgr.pick_sort(exclude);
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
          assert(d_smgr.has_term(skind));
          auto it = sorts.find(skind);
          Sort sort;
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

      /* Numeral arguments for indexed operators. */
      if (n_params)
      {
        if (kind == Op::BV_EXTRACT)
        {
          assert(n_params == 2);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_bv());
          assert(sort_kind == SORT_BV);
          uint32_t bw = args[0]->get_sort()->get_bv_size();
          params.push_back(d_rng.pick<uint32_t>(0, bw - 1));     // high
          params.push_back(d_rng.pick<uint32_t>(0, params[0]));  // low
        }
        else if (kind == Op::BV_REPEAT)
        {
          assert(n_params == 1);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_bv());
          assert(sort_kind == SORT_BV);
          uint32_t bw = args[0]->get_sort()->get_bv_size();
          params.push_back(d_rng.pick<uint32_t>(
              1, std::max<uint32_t>(1, MURXLA_BW_MAX / bw)));
        }
        else if (kind == Op::BV_ROTATE_LEFT || kind == Op::BV_ROTATE_RIGHT)
        {
          assert(n_params == 1);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_bv());
          assert(sort_kind == SORT_BV);
          uint32_t bw = args[0]->get_sort()->get_bv_size();
          params.push_back(d_rng.pick<uint32_t>(0, bw));
        }
        else if (kind == Op::BV_SIGN_EXTEND || kind == Op::BV_ZERO_EXTEND)
        {
          assert(n_params == 1);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_bv());
          assert(sort_kind == SORT_BV);
          uint32_t bw = args[0]->get_sort()->get_bv_size();
          params.push_back(d_rng.pick<uint32_t>(0, MURXLA_BW_MAX - bw));
        }
        else if (kind == Op::FP_TO_FP_FROM_SBV || kind == Op::FP_TO_FP_FROM_UBV)
        {
          assert(n_params == 2);
          assert(args.size() == 2);
          assert(args[0]->get_sort()->is_rm());
          assert(args[1]->get_sort()->is_bv());
          assert(sort_kind == SORT_FP);
          /* term has FP sort, pick sort */
          if (!d_smgr.has_sort(SORT_FP)) return false;
          Sort sort = d_smgr.pick_sort(SORT_FP, false);
          params.push_back(sort->get_fp_exp_size());
          params.push_back(sort->get_fp_sig_size());
        }
        else if (kind == Op::FP_TO_FP_FROM_FP)
        {
          assert(n_params == 2);
          assert(args.size() == 2);
          assert(args[0]->get_sort()->is_rm());
          assert(args[1]->get_sort()->is_fp());
          assert(sort_kind == SORT_FP);
          /* term has new FP sort, pick sort */
          if (!d_smgr.has_sort(SORT_FP)) return false;
          Sort sort = d_smgr.pick_sort(SORT_FP, false);
          params.push_back(sort->get_fp_exp_size());
          params.push_back(sort->get_fp_sig_size());
        }
        else if (kind == Op::FP_TO_SBV || kind == Op::FP_TO_UBV)
        {
          assert(n_params == 1);
          assert(args.size() == 2);
          assert(args[0]->get_sort()->is_rm());
          assert(args[1]->get_sort()->is_fp());
          assert(sort_kind == SORT_BV);
          /* term has BV sort, pick bit-width */
          params.push_back(
              d_rng.pick<uint32_t>(1, std::max<uint32_t>(1, MURXLA_BW_MAX)));
        }
        else if (kind == Op::FP_TO_FP_FROM_REAL)
        {
          assert(n_params == 2);
          assert(args.size() == 2);
          assert(args[0]->get_sort()->is_rm());
          assert(args[1]->get_sort()->is_real());
          assert(sort_kind == SORT_FP);
          /* term has FP sort, pick sort */
          if (!d_smgr.has_sort(SORT_FP)) return false;
          Sort sort = d_smgr.pick_sort(SORT_FP, false);
          params.push_back(sort->get_fp_exp_size());
          params.push_back(sort->get_fp_sig_size());
        }
        else if (kind == Op::INT_IS_DIV)
        {
          assert(n_params == 1);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_int());
          assert(sort_kind == SORT_BOOL);
          params.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
        }
        else if (kind == Op::RE_LOOP)
        {
          assert(n_params == 2);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_reglan());
          assert(sort_kind == SORT_REGLAN);
          params.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
          params.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
        }
        else if (kind == Op::RE_POW)
        {
          assert(n_params == 1);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_reglan());
          assert(sort_kind == SORT_REGLAN);
          params.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
        }
        else
        {
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
    }

    /* Every OP with return sort SORT_ANY needs to set the kind above. */
    assert(sort_kind != SORT_ANY);
    _run(kind, sort_kind, args, params);

    ++d_smgr.d_mbt_stats->d_ops_ok[op.d_id];

    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS_MIN(
        3, " (operator kind, sort id, number of arguments) ", tokens.size());

    std::vector<Term> args;
    std::vector<uint32_t> params;
    uint32_t n_tokens  = tokens.size();
    OpKind op_kind     = tokens[0];
    SortKind sort_kind = get_sort_kind_from_str(tokens[1]);
    uint32_t n_args    = str_to_uint32(tokens[2]);
    uint32_t idx       = 3;

    MURXLA_CHECK_TRACE(idx + n_args <= n_tokens)
        << "expected " << n_args << " term argument(s), got " << n_tokens - 3;

    for (uint32_t i = 0; i < n_args; ++i, ++idx)
    {
      uint32_t id = FSM::untrace_str_to_id(tokens[idx]);
      Term t      = d_smgr.get_term(id);
      MURXLA_CHECK_TRACE_TERM(t, id);
      args.push_back(t);
    }

    if (idx < tokens.size())
    {
      uint32_t n_params = str_to_uint32(tokens[idx++]);
      MURXLA_CHECK_TRACE(idx + n_params == n_tokens)
          << "expected " << n_args
          << " parameter(s) to create indexed term, got "
          << n_tokens - 3 - n_args;
      for (uint32_t i = 0; i < n_params; ++i, ++idx)
      {
        uint32_t param = str_to_uint32(tokens[idx]);
        params.push_back(param);
      }
    }
    return _run(op_kind, sort_kind, args, params);
  }

 private:
  std::vector<uint64_t> _run(OpKind kind,
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
    MURXLA_TRACE << get_kind() << trace_str.str();

    /* Note: We remove the variable in _run instead of run so that we correctly
     *       handle this case for untracing. */
    if (kind == Op::FORALL || kind == Op::EXISTS)
    {
      d_smgr.remove_var(args[0]);
    }

    Term res = d_solver.mk_term(kind, args, params);

    d_smgr.add_term(res, sort_kind, args);
    MURXLA_TRACE_RETURN << res;
    return {res->get_id()};
  }
};

class ActionMkConst : public Action
{
 public:
  ActionMkConst(SolverManager& smgr) : Action(smgr, MK_CONST, ID) {}

  bool run() override
  {
    assert(d_solver.is_initialized());

    /* Creating constants with SORT_REGLAN not supported by any solver right
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

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
    Sort sort = d_smgr.get_sort(FSM::untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
    std::string symbol = str_to_str(tokens[1]);
    return _run(sort, symbol);
  }

 private:
  std::vector<uint64_t> _run(Sort sort, std::string& symbol)
  {
    MURXLA_TRACE << get_kind() << " " << sort << " \"" << symbol << "\"";
    Term res = d_solver.mk_const(sort, symbol);
    d_smgr.add_input(res, sort, sort->get_kind());
    MURXLA_TRACE_RETURN << res;
    return {res->get_id()};
  }
};

class ActionMkVar : public Action
{
 public:
  ActionMkVar(SolverManager& smgr) : Action(smgr, MK_VAR, ID) {}

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

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
    Sort sort = d_smgr.get_sort(FSM::untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
    std::string symbol = str_to_str(tokens[1]);
    return _run(sort, symbol);
  }

 private:
  std::vector<uint64_t> _run(Sort sort, std::string& symbol)
  {
    MURXLA_TRACE << get_kind() << " " << sort << " \"" << symbol << "\"";
    Term res = d_solver.mk_var(sort, symbol);
    d_smgr.add_var(res, sort, sort->get_kind());
    MURXLA_TRACE_RETURN << res;
    return {res->get_id()};
  }
};

class ActionMkValue : public Action
{
 public:
  ActionMkValue(SolverManager& smgr) : Action(smgr, MK_VALUE, ID) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    /* Pick sort of value. */
    if (!d_smgr.has_sort()) return false;
    Sort sort          = d_smgr.pick_sort();
    SortKind sort_kind = sort->get_kind();
    RNGenerator::Choice pick;

    /* Pick value. */
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
        std::string val;
        /* use random value */
        switch (base)
        {
          case Solver::Base::DEC: val = d_rng.pick_dec_bin_string(bw); break;
          case Solver::Base::HEX: val = d_rng.pick_hex_bin_string(bw); break;
          default:
            assert(base == Solver::Base::BIN);
            val = d_rng.pick_bin_string(bw);
        }
        _run(sort, val, base);
      }
      break;

      case SORT_FP:
        return false;
        // TODO arbitrary values

      case SORT_INT:
        _run(sort,
             d_rng.pick_dec_int_string(
                 d_rng.pick<uint32_t>(1, MURXLA_INT_LEN_MAX)));
        break;

      case SORT_REAL:
        pick = d_rng.pick_one_of_four();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            _run(sort,
                 d_rng.pick_dec_int_string(
                     d_rng.pick<uint32_t>(1, MURXLA_INT_LEN_MAX)));
            break;
          case RNGenerator::Choice::SECOND:
            _run(sort,
                 d_rng.pick_dec_real_string(
                     d_rng.pick<uint32_t>(1, MURXLA_REAL_LEN_MAX)));
            break;
          case RNGenerator::Choice::THIRD:
            _run(sort,
                 d_rng.pick_dec_rational_string(
                     d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX),
                     d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX)));
            break;
          default:
            assert(pick == RNGenerator::Choice::FOURTH);
            _run(sort,
                 d_rng.pick_dec_int_string(
                     d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX)),
                 d_rng.pick_dec_int_string(
                     d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX)));
        }
        break;

      case SORT_RM: return false;

      case SORT_STRING:
      {
        uint32_t len = d_rng.pick<uint32_t>(0, MURXLA_STR_LEN_MAX);
        std::string value;
        if (len)
        {
          d_rng.pick_string_literal(len);
        }
        _run(sort, value);
      }
      break;

      case SORT_REGLAN: return false;

      default: assert(false);
    }

    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);

    uint64_t res = 0;
    Sort sort    = d_smgr.get_sort(FSM::untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
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

      case 4:
      {
        assert(sort->is_bv());
      }
      break;
      default:
        MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
        if (tokens[1] == "true")
        {
          res = _run(sort, true);
        }
        else if (tokens[1] == "false")
        {
          res = _run(sort, false);
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

    return {res};
  }

 private:
  uint64_t _run(Sort sort, bool val)
  {
    MURXLA_TRACE << get_kind() << " " << sort << " "
                 << (val ? "true" : "false");
    Term res = d_solver.mk_value(sort, val);
    d_smgr.add_value(res, sort, sort->get_kind());
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(Sort sort, std::string val)
  {
    MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
    Term res;
    res = d_solver.mk_value(sort, val);
    d_smgr.add_value(res, sort, sort->get_kind());
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(Sort sort, std::string val, size_t len)
  {
    MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
    Term res = d_solver.mk_value(sort, val);
    d_smgr.add_value(res, sort, sort->get_kind());
    if (len == 1)
    {
      assert(sort->is_string());
      d_smgr.add_string_char_value(res);
    }
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(Sort sort, std::string v0, std::string v1)
  {
    MURXLA_TRACE << get_kind() << " " << sort << " \"" << v0 << "\""
                 << " \"" << v1 << "\"";
    Term res = d_solver.mk_value(sort, v0, v1);
    d_smgr.add_value(res, sort, sort->get_kind());
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(Sort sort, std::string val, Solver::Base base)
  {
    MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\""
                 << " " << base;
    Term res = d_solver.mk_value(sort, val, base);
    d_smgr.add_value(res, sort, sort->get_kind());
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionMkSpecialValue : public Action
{
 public:
  ActionMkSpecialValue(SolverManager& smgr) : Action(smgr, MK_SPECIAL_VALUE, ID)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    /* Pick sort of value. */
    if (!d_smgr.has_sort()) return false;
    Sort sort                  = d_smgr.pick_sort();
    SortKind sort_kind         = sort->get_kind();
    const auto& special_values = d_solver.get_special_values(sort_kind);
    if (special_values.empty()) return false;
    _run(sort,
         d_rng.pick_from_set<std::unordered_set<Solver::SpecialValueKind>,
                             Solver::SpecialValueKind>(special_values));

    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());

    uint64_t res = 0;
    Sort sort    = d_smgr.get_sort(FSM::untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
    const auto& special_vals = d_solver.get_special_values(sort->get_kind());

    std::string value = str_to_str(tokens[1]);
    MURXLA_CHECK_TRACE(!special_vals.empty()
                       && special_vals.find(value) != special_vals.end())
        << "unknown special value " << value << " of sort kind "
        << sort->get_kind();

    res = _run(sort, value);

    return {res};
  }

 private:
  uint64_t _run(Sort sort, const Solver::SpecialValueKind& val)
  {
    MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
    Term res;
    res = d_solver.mk_special_value(sort, val);
    d_smgr.add_value(res, sort, sort->get_kind());
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionTermCheckSort : public Action
{
 public:
  ActionTermCheckSort(SolverManager& smgr) : Action(smgr, TERM_CHECK_SORT, NONE)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    Term term = d_smgr.pick_term();
    _run(term);
    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term t = d_smgr.get_term(FSM::untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(t, tokens[0]);
    _run(t);
    return {};
  }

 private:
  void _run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    Sort sort = term->get_sort();
    if (sort->is_array())
    {
      assert(term->is_array());
    }
    else if (sort->is_bool())
    {
      assert(term->is_bool());
    }
    else if (sort->is_bv())
    {
      assert(term->is_bv());
    }
    else if (sort->is_fp())
    {
      assert(term->is_fp());
    }
    else if (sort->is_fun())
    {
      assert(term->is_fun());
    }
    else if (sort->is_int())
    {
      assert(term->is_int());
    }
    else if (sort->is_real())
    {
      assert(term->is_real());
    }
    else if (sort->is_rm())
    {
      assert(term->is_rm());
    }
    else if (sort->is_string())
    {
      assert(term->is_string());
    }
    else if (sort->is_reglan())
    {
      assert(term->is_reglan());
    }
    else
    {
      assert(false);
    }
  }
};

class ActionAssertFormula : public Action
{
 public:
  ActionAssertFormula(SolverManager& smgr) : Action(smgr, ASSERT_FORMULA, NONE)
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

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term t = d_smgr.get_term(FSM::untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(t, tokens[0]);
    _run(t);
    return {};
  }

 private:
  void _run(Term assertion)
  {
    MURXLA_TRACE << get_kind() << " " << assertion;
    reset_sat();
    d_solver.assert_formula(assertion);
  }
};

class ActionCheckSat : public Action
{
 public:
  ActionCheckSat(SolverManager& smgr) : Action(smgr, CHECK_SAT, NONE) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    /* If the last call was unsat, call check-sat again with a lower
     * probability. */
    if (d_smgr.d_sat_result == Solver::UNSAT && d_rng.pick_with_prob(95))
    {
      return false;
    }
    _run();
    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.empty());
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    _run();
    return {};
  }

 private:
  void _run()
  {
    MURXLA_TRACE << get_kind();
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
      : Action(smgr, CHECK_SAT_ASSUMING, NONE)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_incremental) return false;
    if (!d_smgr.has_term(SORT_BOOL, 0)) return false;
    uint32_t n_assumptions =
        d_rng.pick<uint32_t>(1, MURXLA_MAX_N_ASSUMPTIONS_CHECK_SAT);
    std::vector<Term> assumptions;
    for (uint32_t i = 0; i < n_assumptions; ++i)
    {
      assumptions.push_back(d_smgr.pick_assumption());
    }
    _run(assumptions);
    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);
    std::vector<Term> assumptions;
    uint32_t n_args = str_to_uint32(tokens[0]);
    for (uint32_t i = 0, idx = 1; i < n_args; ++i, ++idx)
    {
      uint32_t id = FSM::untrace_str_to_id(tokens[idx]);
      Term t      = d_smgr.get_term(id);
      MURXLA_CHECK_TRACE_TERM(t, id);
      assumptions.push_back(t);
    }
    _run(assumptions);
    return {};
  }

 private:
  void _run(std::vector<Term> assumptions)
  {
    MURXLA_TRACE << get_kind() << " " << assumptions.size() << assumptions;
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
      : Action(smgr, GET_UNSAT_ASSUMPTIONS, NONE)
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

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    _run();
    return {};
  }

 private:
  void _run()
  {
    MURXLA_TRACE << get_kind();
    /* Note: The Terms in this vector are solver terms wrapped into Term,
     *       without sort information! */
    std::vector<Term> res = d_solver.get_unsat_assumptions();
    for (Term& fa : res)
    {
      Term t =
          d_smgr.find_term(fa, d_solver.get_sort(fa, SORT_BOOL), SORT_BOOL);
      assert(t != nullptr);
      assert(d_smgr.is_assumed(t));
      assert(d_solver.check_unsat_assumption(t));
    }
    d_smgr.d_sat_called = true;
  }
};

class ActionGetValue : public Action
{
 public:
  ActionGetValue(SolverManager& smgr) : Action(smgr, GET_VALUE, ID_LIST) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;

    uint32_t n_terms = d_rng.pick<uint32_t>(1, MURXLA_MAX_N_TERMS_GET_VALUE);
    std::vector<Term> terms;
    for (uint32_t i = 0; i < n_terms; ++i)
    {
      terms.push_back(d_smgr.pick_term());
    }
    _run(terms);
    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size() > 1);
    std::vector<Term> terms;
    uint32_t n_args = str_to_uint32(tokens[0]);
    for (uint32_t i = 0, idx = 1; i < n_args; ++i, ++idx)
    {
      uint32_t id = FSM::untrace_str_to_id(tokens[idx]);
      Term t      = d_smgr.get_term(id);
      MURXLA_CHECK_TRACE_TERM(t, id);
      terms.push_back(t);
    }
    return _run(terms);
  }

 private:
  std::vector<uint64_t> _run(std::vector<Term> terms)
  {
    MURXLA_TRACE << get_kind() << " " << terms.size() << terms;
    std::vector<uint64_t> res;
    /* Note: The Terms in this vector are solver terms wrapped into Term,
     *       without sort information! */
    std::vector<Term> res_terms = d_solver.get_value(terms);
    assert(terms.size() == res_terms.size());
    if (d_smgr.d_incremental && d_rng.flip_coin())
    {
      /* assume assignment and check if result is still SAT */
      std::vector<Term> assumptions;
      for (size_t i = 0, n = terms.size(); i < n; ++i)
      {
        std::vector<Term> args = {terms[i], res_terms[i]};
        std::vector<uint32_t> params;
        assumptions.push_back(d_solver.mk_term(Op::EQUAL, args, params));
      }
      assert(d_solver.check_sat_assuming(assumptions) == Solver::Result::SAT);
    }
    /* add values to term database */
    std::stringstream ss;
    for (size_t i = 0, n = terms.size(); i < n; ++i)
    {
      Sort sort = terms[i]->get_sort();
      assert(sort != nullptr);
      SortKind sort_kind = sort->get_kind();
      assert(sort_kind != SORT_ANY);
      d_smgr.add_term(res_terms[i], sort_kind);
      ss << (i > 0 ? " " : "") << res_terms[i];
      res.push_back(res_terms[i]->get_id());
    }
    MURXLA_TRACE_RETURN << ss.str();
    return res;
  }
};

class ActionPush : public Action
{
 public:
  ActionPush(SolverManager& smgr) : Action(smgr, PUSH, NONE) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    uint32_t n_levels = d_rng.pick<uint32_t>(1, MURXLA_MAX_N_PUSH_LEVELS);
    _run(n_levels);
    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size() == 1);
    uint32_t n_levels = str_to_uint32(tokens[0]);
    _run(n_levels);
    return {};
  }

 private:
  void _run(uint32_t n_levels)
  {
    MURXLA_TRACE << get_kind() << " " << n_levels;
    reset_sat();
    d_solver.push(n_levels);
    d_smgr.d_n_push_levels += n_levels;
  }
};

class ActionPop : public Action
{
 public:
  ActionPop(SolverManager& smgr) : Action(smgr, POP, NONE) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (d_smgr.d_n_push_levels == 0) return false;
    uint32_t n_levels = d_rng.pick<uint32_t>(1, d_smgr.d_n_push_levels);
    _run(n_levels);
    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size() == 1);
    uint32_t n_levels = str_to_uint32(tokens[0]);
    _run(n_levels);
    return {};
  }

 private:
  void _run(uint32_t n_levels)
  {
    MURXLA_TRACE << get_kind() << " " << n_levels;
    reset_sat();
    d_solver.pop(n_levels);
    d_smgr.d_n_push_levels -= n_levels;
  }
};

class ActionResetAssertions : public Action
{
 public:
  ActionResetAssertions(SolverManager& smgr)
      : Action(smgr, RESET_ASSERTIONS, NONE)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    _run();
    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    _run();
    return {};
  }

 private:
  void _run()
  {
    MURXLA_TRACE << get_kind();
    reset_sat();
    d_solver.reset_assertions();
    d_smgr.d_n_push_levels = 0;
  }
};

class ActionPrintModel : public Action
{
 public:
  ActionPrintModel(SolverManager& smgr) : Action(smgr, PRINT_MODEL, NONE) {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    _run();
    return true;
  }

  std::vector<uint64_t> untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    _run();
    return {};
  }

 private:
  void _run()
  {
    MURXLA_TRACE << get_kind();
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
  s_terms->add_action(t_default, 500, s_sat);
  s_terms->add_action(t_inputs, 500, s_push_pop);

  /* State: assert/assume formula ........................................ */
  s_assert->add_action(a_assert, 1);
  s_assert->add_action(t_default, 200, s_delete);
  s_assert->add_action(t_default, 20, s_sat);
  s_assert->add_action(t_inputs, 5, s_push_pop);
  s_assert->add_action(t_default, 50, s_terms);

  /* State: check sat .................................................... */
  s_sat->add_action(a_sat, 1);
  s_sat->add_action(a_sat_ass, 1);
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
FSM::untrace(const std::string& trace_file_name)
{
  assert(!trace_file_name.empty());

  uint32_t nline   = 0;
  std::vector<uint64_t> ret_val;
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
        }
        else
        {
          try
          {
            ret_val = action->untrace(tokens);
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

            if (action->returns() == Action::ReturnValue::ID
                && next_tokens.size() != 1)
            {
              throw MurxlaUntraceException(
                  trace_file_name,
                  nline,
                  "expected single argument to 'return'");
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
              uint64_t rid = untrace_str_to_id(next_tokens[i]);
              if (next_tokens[i][0] == 's')
              {
                d_smgr.register_sort(rid, ret_val[i]);
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

uint64_t
FSM::untrace_str_to_id(const std::string& s)
{
  if (s.size() < 2 || (s[0] != 's' && s[0] != 't'))
  {
    throw MurxlaUntraceIdException("invalid sort or term argument: " + s);
  }
  try
  {
    return str_to_uint64(std::string(s, 1));
  }
  catch (std::invalid_argument& e)
  {
    if (s[0] == 's')
    {
      throw MurxlaUntraceIdException("invalid sort argument: " + s);
    }
    throw MurxlaUntraceIdException("invalid term argument: " + s);
  }
}

/* ========================================================================== */
}  // namespace murxla
