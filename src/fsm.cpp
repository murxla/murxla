#include "fsm.hpp"

#include <cassert>
#include <iostream>
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
State::add_action(Action* a, uint32_t weight, State* next)
{
  d_actions.emplace_back(ActionTuple(a, next == nullptr ? this : next));
  d_weights.push_back(weight);
}

/* -------------------------------------------------------------------------- */

State*
State::run(RNGenerator& rng)
{
  assert(!d_actions.empty());
  uint32_t idx      = rng.pick_uint32_weighted(d_weights);
  ActionTuple& atup = d_actions[idx];
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
  d_init_state = init_state;
  d_cur_state  = init_state;
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
    SMTMBT_WARN(s.get() != d_init_state
                && all_next_states.find(s.get()) == all_next_states.end())
        << "unreachable state '" << s->get_id() << "'";
  }

  /* check for infinite loop */
  SMTMBT_ABORT(
      no_next_state
      && (no_next_state == d_init_state
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

  State* s = d_cur_state;
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
class TransitionCreateInputs : public Action
{
 public:
  TransitionCreateInputs(SolverManager& smgr) : Action(smgr, "") {}
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
    std::string opt, value;

    std::tie(opt, value) = d_smgr.pick_option();

    if (opt.empty()) /* No option available */
      return false;

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
    if (opt == d_solver.get_option_name_incremental())
    {
      d_smgr.d_incremental = value == "true";
    }
    else if (opt == d_solver.get_option_name_model_gen())
    {
      d_smgr.d_model_gen = value == "true";
    }
  }
};

class ActionMkSort : public Action
{
 public:
  ActionMkSort(SolverManager& smgr) : Action(smgr, "mk-sort") {}

  bool run() override
  {
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
    d_solver.check_sat();
    d_smgr.d_sat_called = true;
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
    d_solver.check_sat_assuming(assumptions);
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

class ActionReset : public Action
{
 public:
  ActionReset(SolverManager& smgr) : Action(smgr, "reset") {}

  bool run() override
  {
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
    d_solver.reset();
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

  auto a_sat     = new_action<ActionCheckSat>();
  auto a_sat_ass = new_action<ActionCheckSatAssuming>();

  auto a_push = new_action<ActionPush>();
  auto a_pop  = new_action<ActionPop>();

  auto a_failed = new_action<ActionGetUnsatAssumptions>();

  auto a_reset     = new_action<ActionReset>();
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

  auto s_sat = new_state("check_sat");

  auto s_push_pop =
      new_state("push_pop", [this]() { return d_smgr.d_incremental; });

  auto s_failed = new_state("failed", [this]() { return d_smgr.d_sat_called; });

  /* --------------------------------------------------------------------- */
  /* Transitions                                                           */
  /* --------------------------------------------------------------------- */

  /* State: new .......................................................... */
  s_new->add_action(a_new, 100, s_opt);

  /* State: opt .......................................................... */
  s_opt->add_action(a_setoption, 100);
  s_opt->add_action(t_default, 20, s_inputs);

  /* State: create inputs ................................................ */
  s_inputs->add_action(a_mksort, 100);
  s_inputs->add_action(a_mkval, 100);
  s_inputs->add_action(a_mkconst, 100);
  s_inputs->add_action(t_inputs, 100, s_terms);
  s_inputs->add_action(t_inputs, 10, s_sat);
  s_inputs->add_action(t_inputs, 10, s_push_pop);

  /* State: create terms ................................................. */
  s_terms->add_action(a_mkterm, 100);
  s_terms->add_action(t_default, 100, s_assert);
  s_terms->add_action(t_default, 10, s_sat);
  s_terms->add_action(t_inputs, 10, s_push_pop);

  /* State: assert/assume formula ........................................ */
  s_assert->add_action(a_assert, 100);
  s_assert->add_action(t_default, 10, s_delete);
  s_assert->add_action(t_default, 100, s_sat);
  s_assert->add_action(t_inputs, 10, s_push_pop);

  /* State: check sat .................................................... */
  s_sat->add_action(a_sat, 100);
  s_sat->add_action(a_sat_ass, 100);
  s_sat->add_action(t_inputs, 10, s_push_pop);
  s_sat->add_action(t_inputs, 10, s_failed);
  s_sat->add_action(t_inputs, 20, s_delete);

  /* State: push_pop ..................................................... */
  s_push_pop->add_action(a_push, 100, s_inputs);
  s_push_pop->add_action(a_push, 100, s_terms);
  s_push_pop->add_action(a_push, 100, s_assert);
  s_push_pop->add_action(a_push, 100, s_sat);
  s_push_pop->add_action(a_push, 50, s_delete);
  s_push_pop->add_action(a_pop, 100, s_inputs);
  s_push_pop->add_action(a_pop, 100, s_terms);
  s_push_pop->add_action(a_pop, 100, s_assert);
  s_push_pop->add_action(a_pop, 100, s_sat);
  s_push_pop->add_action(a_pop, 50, s_delete);

  /* State: failed ....................................................... */
  s_failed->add_action(a_failed, 100, s_sat);

  /* State: delete ....................................................... */
  s_delete->add_action(a_delete, 100, s_final);

  /* All States (with exceptions) ........................................ */
  add_action_to_all_states(a_reset, 1, {"new"});
  add_action_to_all_states(a_reset_ass, 1, {"new"});

  /* --------------------------------------------------------------------- */
  /* Initial State                                                         */
  /* --------------------------------------------------------------------- */

  set_init_state(s_new);

  d_smgr.get_solver().configure_fsm(this);

  for (const auto& t : d_actions_all_states)
  {
    for (const auto& s : d_states)
    {
      std::unordered_set<std::string> excluded_states = std::get<2>(t);
      if (excluded_states.find(s->get_id()) == excluded_states.end())
      {
        s->add_action(std::get<0>(t), std::get<1>(t));
      }
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
    std::stringstream tokenstream(line);
    std::string token;
    std::string id;
    std::vector<std::string> tokens;
    while (std::getline(tokenstream, token, ' '))
    {
      if (id.empty())
      {
        id = token;
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

    assert (d_actions.find(id) != d_actions.end());
    ret_val = d_actions.at(id)->untrace(tokens);
  }
}

/* ========================================================================== */
}  // namespace smtmbt
