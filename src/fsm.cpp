#include "fsm.hpp"

#include <cassert>
#include <iostream>
#include <numeric>
#include <sstream>
#include <unordered_set>

#include "solver_manager.hpp"

/* -------------------------------------------------------------------------- */

#define SMTMBT_LEN_SYMBOL_MAX 128

#define SMTMBT_MAX_N_ASSUMPTIONS_CHECK_SAT 5
#define SMTMBT_MAX_N_PUSH_LEVELS 5

/* -------------------------------------------------------------------------- */

namespace smtmbt {

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
  assert(!d_actions.empty());
  uint32_t idx      = rng.pick_uint32_weighted(d_weights);
  ActionTuple& atup = d_actions[idx];
  /* only pick empty transitions if precondition of this state is false */
  if (f_precond != nullptr && !f_precond())
  {
    while (!atup.d_action->empty())
    {
      idx  = rng.pick_uint32_weighted(d_weights);
      atup = d_actions[idx];
    }
  }
  if (atup.d_action->run()
      && (atup.d_next->f_precond == nullptr || atup.d_next->f_precond()))
  {
    return d_actions[idx].d_next;
  }
  return this;
}

/* -------------------------------------------------------------------------- */

FSM::FSM(RNGenerator& rng,
         Solver* solver,
         std::ostream& trace,
         SolverOptions& options)
    : d_smgr(solver, rng, trace, options), d_rng(rng)
{
}

SolverManager&
FSM::get_smgr()
{
  return d_smgr;
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
        << "unreachable state '" << s->get_id() << "'";
  }

  /* check for infinite loop */
  SMTMBT_ABORT(
      no_next_state
      && (no_next_state == d_state_init
          || all_next_states.find(no_next_state) != all_next_states.end()))
      << "infinite loop in state '" << no_next_state->get_id() << "'";
}

State*
FSM::get_state(const std::string& id) const
{
  State* res = nullptr;
  for (const auto& s : d_states)
  {
    if (s->d_id == id)
    {
      res = s.get();
    }
  }
  assert(res);
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
  TransitionCreateInputs(SolverManager& smgr) : Transition(smgr) {}
  bool run() override { return d_smgr.d_stats.inputs > 0; }
  uint64_t untrace(std::vector<std::string>& tokens) override { return 0; }
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
    if (d_solver.is_initialized()) d_solver.delete_solver();
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_id();
    d_solver.new_solver();
  }
};

class ActionDelete : public Action
{
 public:
  ActionDelete(SolverManager& smgr) : Action(smgr, "delete") {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_id();
    d_smgr.clear();
    d_solver.delete_solver();
  }
};

class ActionSetOption : public Action
{
 public:
  ActionSetOption(SolverManager& smgr) : Action(smgr, "set-option") {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    std::string opt, value;

    if (!d_smgr.d_incremental && d_rng.pick_with_prob(10))
    {
      /* explicitly enable this option with higher priority */
      opt   = d_solver.get_option_name_incremental();
      value = d_solver.get_option_value_enable_incremental();
    }
    else if (!d_smgr.d_model_gen && d_rng.pick_with_prob(10))
    {
      /* explicitly enable this option with higher priority */
      opt   = d_solver.get_option_name_model_gen();
      value = d_solver.get_option_value_enable_model_gen();
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
    assert(tokens.size() == 2);
    _run(tokens[0], tokens[1]);
    return 0;
  }

 private:
  void _run(const std::string& opt, const std::string& value)
  {
    SMTMBT_TRACE << get_id() << " " << opt << " " << value;
    d_solver.set_opt(opt, value);
    d_smgr.d_incremental = d_solver.option_incremental_enabled();
    d_smgr.d_model_gen   = d_solver.option_model_gen_enabled();
  }
};

class ActionMkSort : public Action
{
 public:
  ActionMkSort(SolverManager& smgr) : Action(smgr, "mk-sort") {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    SortKind kind = d_smgr.pick_sort_kind_data().d_kind;

    switch (kind)
    {
      case SORT_BOOL: _run(SORT_BOOL); break;

      case SORT_BV:
        _run(SORT_BV, d_rng.pick<uint32_t>(SMTMBT_BW_MIN, SMTMBT_BW_MAX));
        break;

      default: assert(false);
    }
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size());

    uint64_t res    = 0;
    size_t n_tokens = tokens.size();
    SortKind kind   = sort_kind_from_str(tokens[0]);

    switch (kind)
    {
      case SORT_BOOL:
        assert(n_tokens == 1);
        res = _run(kind);
        break;

      case SORT_BV:
        assert(n_tokens == 2);
        res = _run(kind, str_to_uint32(tokens[1]));
        break;

      default: assert(false);
    }
    return res;
  }

 private:
  uint64_t _run(SortKind kind)
  {
    SMTMBT_TRACE << get_id() << " " << kind;
    Sort res = d_solver.mk_sort(SORT_BOOL);
    d_smgr.add_sort(res, kind);
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(SortKind kind, uint32_t bw)
  {
    SMTMBT_TRACE << get_id() << " " << kind << " " << bw;
    Sort res = d_solver.mk_sort(SORT_BV, bw);
    assert(res->get_bv_size() == bw);
    d_smgr.add_sort(res, kind);
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionMkTerm : public Action
{
 public:
  ActionMkTerm(SolverManager& smgr) : Action(smgr, "mk-term") {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    assert(d_smgr.get_enabled_theories().find(THEORY_BOOL)
           != d_smgr.get_enabled_theories().end());
    assert(d_smgr.has_term());

    /* pick operator kind */
    OpKindData& kind_data   = d_smgr.pick_op_kind_data();
    OpKind kind             = kind_data.d_kind;
    int32_t arity           = kind_data.d_arity;
    uint32_t n_params       = kind_data.d_nparams;
    SortKind sort_kind      = kind_data.d_sort_kind;
    SortKind sort_kind_args = kind_data.d_sort_kind_args;

    if (!d_smgr.has_term(sort_kind_args)) return false;

    std::vector<Term> args;
    Sort sort;

    /* Pick term arguments. */
    if (kind == OpKind::OP_BV_CONCAT)
    {
      if (!d_smgr.has_sort_bv(SMTMBT_BW_MAX - 1)) return false;
      sort        = d_smgr.pick_sort_bv(SMTMBT_BW_MAX - 1);
      uint32_t bw = SMTMBT_BW_MAX - sort->get_bv_size();
      if (!d_smgr.has_sort_bv(bw)) return false;
      args.push_back(d_smgr.pick_term(sort));
      do
      {
        sort = d_smgr.pick_sort_bv(bw);
        args.push_back(d_smgr.pick_term(sort));
        bw -= sort->get_bv_size();
      } while (d_smgr.has_sort_bv(bw) && d_rng.pick_one_of_three());
    }
    else
    {
      sort = d_smgr.pick_sort(sort_kind_args);
      if (arity == SMTMBT_MK_TERM_N_ARGS)
      {
        arity = d_rng.pick<uint32_t>(SMTMBT_MK_TERM_N_ARGS_MIN,
                                     SMTMBT_MK_TERM_N_ARGS_MAX);
      }
      /* pick first argument */
      switch (kind)
      {
        case OpKind::OP_ITE:
          if (!d_smgr.has_term(SORT_BOOL)) return false;
          args.push_back(d_smgr.pick_term(SORT_BOOL));
          break;
        default:
          args.push_back(d_smgr.pick_term(sort));
          assert(!args[0]->get_sort()->is_bv()
                 || args[0]->get_sort()->get_bv_size() == sort->get_bv_size());
          assert(sort_kind_args == SORT_ANY
                 || sort_kind_args == sort->get_kind());
      }
      /* pick remaining arguments */
      for (int32_t i = 1; i < arity; ++i)
      {
        args.push_back(d_smgr.pick_term(sort));
      }
    }

    /* Numeral arguments for indexed operators. */
    std::vector<uint32_t> params;
    if (n_params)
    {
      uint32_t bw = sort->get_bv_size();
      switch (kind)
      {
        case OP_BV_EXTRACT:
          assert(sort->is_bv());
          params.push_back(d_rng.pick<uint32_t>(0, bw - 1));     // high
          params.push_back(d_rng.pick<uint32_t>(0, params[0]));  // low
          break;
        case OP_BV_REPEAT:
          assert(sort->is_bv());
          params.push_back(d_rng.pick<uint32_t>(
              1, std::max<uint32_t>(1, SMTMBT_BW_MAX / bw)));
          break;
        case OP_BV_ROTATE_LEFT:
        case OP_BV_ROTATE_RIGHT:
          assert(sort->is_bv());
          params.push_back(d_rng.pick<uint32_t>(0, bw));
          break;
        case OP_BV_SIGN_EXTEND:
        case OP_BV_ZERO_EXTEND:
          assert(sort->is_bv());
          params.push_back(d_rng.pick<uint32_t>(0, SMTMBT_BW_MAX - bw));
          break;
        default: assert(false);
      }
    }

    _run(kind,
         sort_kind == SORT_ANY ? sort->get_kind() : sort_kind,
         args,
         params);

    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size());

    std::vector<Term> args;
    std::vector<uint32_t> params;
    uint32_t n_tokens  = tokens.size();
    OpKind op_kind     = op_kind_from_str(tokens[0]);
    SortKind sort_kind = sort_kind_from_str(tokens[1]);
    uint32_t n_args    = str_to_uint32(tokens[2]);
    uint32_t idx       = 3;

    assert(idx + n_args <= n_tokens);
    for (uint32_t i = 0; i < n_args; ++i, ++idx)
    {
      uint32_t id = str_to_uint32(tokens[idx]);
      Term t      = d_smgr.get_term(id);
      assert(t != nullptr);
      args.push_back(t);
    }

    if (idx < tokens.size())
    {
      uint32_t n_params = str_to_uint32(tokens[idx++]);
      assert(idx + n_params == n_tokens);
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
    SMTMBT_TRACE << get_id() << trace_str.str();
    Term res = d_solver.mk_term(kind, args, params);
    d_smgr.add_term(res, d_solver.get_sort(res), sort_kind);
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionMkConst : public Action
{
 public:
  ActionMkConst(SolverManager& smgr) : Action(smgr, "mk-const") {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    /* Pick sort of const. */
    if (!d_smgr.has_sort()) return false;
    Sort sort          = d_smgr.pick_sort();
    uint32_t len       = d_rng.pick<uint32_t>(0, SMTMBT_LEN_SYMBOL_MAX);
    /* Pick piped vs simple symbol with 50% probability. */
    std::string symbol = len && d_rng.flip_coin()
                             ? d_rng.pick_piped_symbol(len)
                             : d_rng.pick_simple_symbol(len);

    /* Create const. */
    _run(sort, symbol);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size() == 2);

    Sort sort = d_smgr.get_sort(str_to_uint32(tokens[0]));
    assert(sort != nullptr);
    std::string symbol = str_to_str(tokens[1]);
    return _run(sort, symbol);
  }

 private:
  uint64_t _run(Sort sort, std::string& symbol)
  {
    SMTMBT_TRACE << get_id() << " " << sort << " \"" << symbol << "\"";
    Term res = d_solver.mk_const(sort, symbol);
    d_smgr.add_input(res, d_solver.get_sort(res), sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionMkValue : public Action
{
 public:
  ActionMkValue(SolverManager& smgr) : Action(smgr, "mk-value") {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    /* Pick sort of value. */
    if (!d_smgr.has_sort()) return false;
    Sort sort          = d_smgr.pick_sort();
    SortKind sort_kind = sort->get_kind();

    /* Pick value. */
    Term res;
    switch (sort_kind)
    {
      case SORT_BOOL: _run(sort, d_rng.flip_coin()); break;

      case SORT_BV:
      {
        uint32_t bw = sort->get_bv_size();

        Solver::SpecialValueBV sval =
            d_rng.pick_from_set<std::vector<Solver::SpecialValueBV>,
                                Solver::SpecialValueBV>(
                d_solver.get_special_values_bv());

        /* ------------ value: uint64_t ------------ */
        if (bw <= 64 && d_rng.flip_coin())
        {
          uint64_t val = 0u;
          if (d_rng.flip_coin())
          {
            /* use special value */
            switch (sval)
            {
              case Solver::SpecialValueBV::ONE: val = 1u; break;
              case Solver::SpecialValueBV::ONES:
                val = bv_special_value_ones_uint64(bw);
                break;
              case Solver::SpecialValueBV::MIN_SIGNED:
                val = bv_special_value_min_signed_uint64(bw);
                break;
              case Solver::SpecialValueBV::MAX_SIGNED:
                val = bv_special_value_max_signed_uint64(bw);
                break;
              default: assert(sval == Solver::SpecialValueBV::ZERO); val = 0u;
            }
          }
          else
          {
            /* use random value */
            val = d_rng.pick<uint64_t>(0, (1 << bw) - 1);
          }
          _run(sort, val);
        }
        /* ------------ value: string ------------ */
        else
        {
          Solver::Base base =
              d_rng.pick_from_set<std::vector<Solver::Base>, Solver::Base>(
                  d_solver.get_bases());
          std::string val;

          if (d_rng.flip_coin())
          {
            /* use special value */
            switch (sval)
            {
              case Solver::SpecialValueBV::ONE:
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
              case Solver::SpecialValueBV::ONES:
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
              case Solver::SpecialValueBV::MIN_SIGNED:
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
              case Solver::SpecialValueBV::MAX_SIGNED:
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
                assert(sval == Solver::SpecialValueBV::ZERO);
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
              case Solver::Base::DEC:
                val = d_rng.pick_dec_bin_string(bw);
                break;
              case Solver::Base::HEX:
                val = d_rng.pick_hex_bin_string(bw);
                break;
              default:
                assert(base == Solver::Base::BIN);
                val = d_rng.pick_bin_string(bw);
            }
          }
          _run(sort, val, base);
        }
      }
      break;
      default: assert(false);
    }

    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size());

    uint64_t res = 0;
    Sort sort    = d_smgr.get_sort(str_to_uint32(tokens[0]));
    assert(sort != nullptr);
    switch (tokens.size())
    {
      case 3:
        res = _run(sort,
                   str_to_str(tokens[1]),
                   static_cast<Solver::Base>(str_to_uint32(tokens[2])));
        break;

      default:
        assert(tokens.size() == 2);
        if (tokens[1] == "true")
        {
          res = _run(sort, true);
        }
        else if (tokens[1] == "false")
        {
          res = _run(sort, false);
        }
        else
        {
          res = _run(sort, str_to_uint64(tokens[1]));
        }
    }

    return res;
  }

 private:
  uint64_t _run(Sort sort, bool val)
  {
    SMTMBT_TRACE << get_id() << " " << sort << " " << (val ? "true" : "false");
    Term res = d_solver.mk_value(sort, val);
    d_smgr.add_input(res, d_solver.get_sort(res), sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(Sort sort, uint64_t val)
  {
    SMTMBT_TRACE << get_id() << " " << sort << " " << val;
    Term res = d_solver.mk_value(sort, val);
    d_smgr.add_input(res, d_solver.get_sort(res), sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }

  uint64_t _run(Sort sort, std::string val, Solver::Base base)
  {
    SMTMBT_TRACE << get_id() << " " << sort << " \"" << val << "\""
                 << " " << base;
    Term res = d_solver.mk_value(sort, val, base);
    d_smgr.add_input(res, d_solver.get_sort(res), sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }
};

class ActionAssertFormula : public Action
{
 public:
  ActionAssertFormula(SolverManager& smgr) : Action(smgr, "assert-formula") {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term(SORT_BOOL)) return false;
    Term assertion = d_smgr.pick_term(SORT_BOOL);

    _run(assertion);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size() == 1);
    Term t = d_smgr.get_term(str_to_uint32(tokens[0]));
    assert(t != nullptr);
    _run(t);
    return 0;
  }

 private:
  void _run(Term assertion)
  {
    SMTMBT_TRACE << get_id() << " " << assertion;
    if (d_smgr.d_sat_called)
    {
      d_smgr.clear_assumptions();
      d_smgr.d_sat_called = false;
    }
    d_solver.assert_formula(assertion);
  }
};

class ActionCheckSat : public Action
{
 public:
  ActionCheckSat(SolverManager& smgr) : Action(smgr, "check-sat") {}

  bool run() override
  {
    assert(d_solver.is_initialized());
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_id();
    if (d_smgr.d_sat_called)
    {
      d_smgr.clear_assumptions();
      d_smgr.d_sat_called = false;
    }
    d_smgr.d_sat_result = d_solver.check_sat();
    d_smgr.d_sat_called = true;
    d_smgr.d_n_sat_calls += 1;
  }
};

class ActionCheckSatAssuming : public Action
{
 public:
  ActionCheckSatAssuming(SolverManager& smgr)
      : Action(smgr, "check-sat-assuming")
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_incremental) return false;
    if (!d_smgr.has_term(SORT_BOOL)) return false;
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
    assert(tokens.size() > 1);
    std::vector<Term> assumptions;
    uint32_t n_args = str_to_uint32(tokens[0]);
    for (uint32_t i = 0, idx = 1; i < n_args; ++i, ++idx)
    {
      uint32_t id = str_to_uint32(tokens[idx]);
      Term t      = d_smgr.get_term(id);
      assert(t != nullptr);
      assumptions.push_back(t);
    }
    _run(assumptions);
    return 0;
  }

 private:
  void _run(std::vector<Term> assumptions)
  {
    SMTMBT_TRACE << get_id() << " " << assumptions.size() << assumptions;
    if (d_smgr.d_sat_called)
    {
      d_smgr.clear_assumptions();
      d_smgr.d_sat_called = false;
    }
    d_smgr.d_sat_result = d_solver.check_sat_assuming(assumptions);
    d_smgr.d_sat_called = true;
  }
};

class ActionGetUnsatAssumptions : public Action
{
 public:
  ActionGetUnsatAssumptions(SolverManager& smgr)
      : Action(smgr, "get-unsat-assumptions")
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::UNSAT) return false;
    if (!d_smgr.d_incremental) return false;
    if (!d_smgr.has_assumed()) return false;
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_id();
    /* Note: The Terms in this vector are solver terms wrapped into Term,
     *       without sort information! */
    std::vector<Term> res = d_solver.get_unsat_assumptions();
    for (Term& fa : res)
    {
      Term t = d_smgr.find_term(fa, d_solver.get_sort(fa), SORT_BOOL);
      assert(t != nullptr);
      assert(d_smgr.is_assumed(t));
      assert(d_solver.check_failed_assumption(t));
    }
    d_smgr.d_sat_called = true;
  }
};

class ActionPush : public Action
{
 public:
  ActionPush(SolverManager& smgr) : Action(smgr, "push") {}

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
    SMTMBT_TRACE << get_id() << " " << n_levels;
    d_solver.push(n_levels);
    d_smgr.d_n_push_levels += n_levels;
  }
};

class ActionPop : public Action
{
 public:
  ActionPop(SolverManager& smgr) : Action(smgr, "pop") {}

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
    SMTMBT_TRACE << get_id() << " " << n_levels;
    d_solver.pop(n_levels);
    d_smgr.d_n_push_levels -= n_levels;
  }
};

class ActionResetAssertions : public Action
{
 public:
  ActionResetAssertions(SolverManager& smgr) : Action(smgr, "reset-assertions")
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
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_id();
    d_solver.reset_assertions();
    d_smgr.d_n_push_levels = 0;
  }
};

class ActionPrintModel : public Action
{
 public:
  ActionPrintModel(SolverManager& smgr) : Action(smgr, "print-model") {}

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
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_id();
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
  auto a_mkterm  = new_action<ActionMkTerm>();

  auto a_assert = new_action<ActionAssertFormula>();

  auto a_failed = new_action<ActionGetUnsatAssumptions>();

  auto a_printmodel = new_action<ActionPrintModel>();

  auto a_sat     = new_action<ActionCheckSat>();
  auto a_sat_ass = new_action<ActionCheckSatAssuming>();

  auto a_push = new_action<ActionPush>();
  auto a_pop  = new_action<ActionPop>();

  auto a_reset_ass = new_action<ActionResetAssertions>();

  auto a_setoption = new_action<ActionSetOption>();

  auto t_default = new_action<Transition>();
  auto t_inputs  = new_action<TransitionCreateInputs>();

  /* --------------------------------------------------------------------- */
  /* States                                                                */
  /* --------------------------------------------------------------------- */

  auto s_new    = new_state("new");
  auto s_opt    = new_state("opt");
  auto s_delete = new_state("delete");
  auto s_final  = new_state("final", nullptr, true);

  auto s_inputs = new_state("create_inputs");
  auto s_terms =
      new_state("create_terms", [this]() { return d_smgr.has_term(); });

  auto s_assert =
      new_state("assert", [this]() { return d_smgr.has_term(SORT_BOOL); });

  auto s_sat = new_state("check_sat", [this]() {
    return d_smgr.d_n_sat_calls == 0 || d_smgr.d_incremental;
  });

  auto s_push_pop =
      new_state("push_pop", [this]() { return d_smgr.d_incremental; });

  /* --------------------------------------------------------------------- */
  /* Add actions/transitions to states                                     */
  /* --------------------------------------------------------------------- */

  /* State: new .......................................................... */
  s_new->add_action(a_new, 1, s_opt);

  /* State: opt .......................................................... */
  s_opt->add_action(a_setoption, 1);
  s_opt->add_action(t_default, 5, s_inputs);

  /* State: create inputs ................................................ */
  s_inputs->add_action(a_mksort, 1);
  s_inputs->add_action(a_mkval, 1);
  s_inputs->add_action(a_mkconst, 1);
  s_inputs->add_action(t_inputs, 1, s_terms);
  s_inputs->add_action(t_inputs, 5, s_sat);
  s_inputs->add_action(t_inputs, 5, s_push_pop);

  /* State: create terms ................................................. */
  s_terms->add_action(a_mkterm, 1);
  s_terms->add_action(t_default, 1, s_assert);
  s_terms->add_action(t_default, 5, s_sat);
  s_terms->add_action(t_inputs, 5, s_push_pop);

  /* State: assert/assume formula ........................................ */
  s_assert->add_action(a_assert, 1);
  s_assert->add_action(t_default, 5, s_delete);
  s_assert->add_action(t_default, 1, s_sat);
  s_assert->add_action(t_inputs, 5, s_push_pop);

  /* State: check sat .................................................... */
  s_sat->add_action(a_sat, 1);
  s_sat->add_action(a_sat_ass, 1);
  s_sat->add_action(t_inputs, 5, s_push_pop);
  s_sat->add_action(t_inputs, 10, s_delete);

  /* State: push_pop ..................................................... */
  s_push_pop->add_action(a_push, 1);
  s_push_pop->add_action(a_pop, 1);
  add_action_to_all_states_next(t_default, 2, s_push_pop);

  /* State: delete ....................................................... */
  s_delete->add_action(a_delete, 1, s_final);

  /* All States (with exceptions) ........................................ */
  add_action_to_all_states(a_failed, 100);
  add_action_to_all_states(a_printmodel, 100);
  add_action_to_all_states(a_reset_ass, 100);

  /* --------------------------------------------------------------------- */
  /* Initial State                                                         */
  /* --------------------------------------------------------------------- */

  set_init_state(s_new);

  /* --------------------------------------------------------------------- */
  /* Configure solver specific actions/states                              */
  /* --------------------------------------------------------------------- */

  d_smgr.get_solver().configure_fsm(this);

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
      const std::string& id = s->get_id();
      if (id == "new" || id == "delete" || id == "final"
          || excluded_states.find(s->get_id()) != excluded_states.end())
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
      const std::string& id = s->get_id();
      if (id == "new" || id == "delete" || id == "final"
          || excluded_states.find(s->get_id()) != excluded_states.end())
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
FSM::untrace(std::ifstream& trace)
{
  assert(trace.is_open());

  uint64_t ret_val = 0;
  std::string line;
  while (std::getline(trace, line))
  {
    if (line[0] == '#') continue;
    bool open_str = false;
    std::stringstream ss;
    std::stringstream tokenstream(line);
    std::string token;
    std::string id;
    std::vector<std::string> tokens;
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

    assert(ret_val == 0 || id == "return");
    if (id == "return")
    {
      assert(tokens.size() == 1);
      uint64_t id = str_to_uint64(tokens[0]);
      assert(id == ret_val);
      ret_val = 0;
      continue;
    }

    assert(d_actions.find(id) != d_actions.end());
    ret_val = d_actions.at(id)->untrace(tokens);
  }
}

/* ========================================================================== */
}  // namespace smtmbt
