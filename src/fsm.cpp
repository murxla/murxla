#include "fsm.hpp"

#include <cassert>
#include <iostream>
#include <sstream>
#include <unordered_set>

#include "solver_manager.hpp"

#define SMTMBT_LEN_SYMBOL_MAX 128

namespace smtmbt {

void
State::add_action(Action* a, uint32_t weight, State* next)
{
  d_actions.emplace_back(ActionTuple(a, next == nullptr ? this : next));
  d_weights.push_back(weight);
}

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
  d_cur_state = init_state;
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

/* ========================================================================== */
/* Default Transitions (= empty actions)                                      */
/* ========================================================================== */

/**
 * Transition from current state to next state without pre-conditions.
 */
class Transition : public Action
{
 public:
  Transition(SolverManager& smgr) : Action(smgr, "") {}
  bool run() override { return true; }
};

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
    SMTMBT_TRACE << get_id();
    if (d_solver.is_initialized()) d_solver.delete_solver();
    d_solver.new_solver();
    //
    //    //////
    //    // TODO we will need a state to (randomly) select/configure options
    //    /* Enable/disable incremental solving. */
    //    bool inc = d_rng.flip_coin();
    //    d_smgr->set_incremental(inc);
    //    cvc4->setOption("incremental", inc ? "true" : "false");
    //    //////
    return true;
  }
};

class ActionDelete : public Action
{
 public:
  ActionDelete(SolverManager& smgr) : Action(smgr, "delete") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    d_smgr.clear();
    d_solver.delete_solver();
    return true;
  }
};

class ActionMkSort : public Action
{
 public:
  ActionMkSort(SolverManager& smgr) : Action(smgr, "mk-sort") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    SortKindData& kind_data = d_smgr.pick_sort_kind_data();
    SortKind kind           = kind_data.d_kind;
    Sort res;
    switch (kind)
    {
      case SORT_BOOL: res = d_solver.mk_sort(SORT_BOOL); break;
      case SORT_BV:
      {
        uint32_t bw = d_rng.pick_uint32(SMTMBT_BW_MIN, SMTMBT_BW_MAX);
        res = d_solver.mk_sort(SORT_BV, bw);
        assert(res->get_bv_size() == bw);
      }
      break;
      default: assert(false);
    }
    d_smgr.add_sort(res, kind);
    return true;
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

    SMTMBT_TRACE << get_id() << " op " << kind;

    if (!d_smgr.has_term(sort_kind_args)) return false;

    std::vector<Term> args;
    Sort sort;

    if (kind == OpKind::BV_CONCAT)
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
        arity = d_rng.pick_uint32(SMTMBT_MK_TERM_N_ARGS_MIN,
                                  SMTMBT_MK_TERM_N_ARGS_MAX);
      }
      /* pick first argument */
      switch (kind)
      {
        case OpKind::ITE:
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

    std::vector<uint32_t> params;
    if (n_params)
    {
      /* Numeral arguments for indexed operators. */
      uint32_t bw = sort->get_bv_size();
      switch (kind)
      {
        case BV_EXTRACT:
          assert(sort->is_bv());
          params.push_back(d_rng.pick_uint32(0, bw - 1));     // high
          params.push_back(d_rng.pick_uint32(0, params[0]));  // low
          break;
        case BV_REPEAT:
          assert(sort->is_bv());
          params.push_back(
              d_rng.pick_uint32(1, std::max<uint32_t>(1, SMTMBT_BW_MAX / bw)));
          break;
        case BV_ROTATE_LEFT:
        case BV_ROTATE_RIGHT:
          assert(sort->is_bv());
          params.push_back(d_rng.pick_uint32(0, bw));
          break;
        case BV_SIGN_EXTEND:
        case BV_ZERO_EXTEND:
          assert(sort->is_bv());
          params.push_back(d_rng.pick_uint32(0, SMTMBT_BW_MAX - bw));
          break;
        default: assert(false);
      }
    }

    /* Create term. */
    Term res = d_solver.mk_term(kind, args, params);
    d_smgr.add_term(res,
                    d_solver.get_sort(res),
                    sort_kind == SORT_ANY ? sort->get_kind() : sort_kind);
    return true;
  }
};

class ActionMkConst : public Action
{
 public:
  ActionMkConst(SolverManager& smgr) : Action(smgr, "mk-const") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick sort of const. */
    if (!d_smgr.has_sort()) return false;
    Sort sort          = d_smgr.pick_sort();
    SortKind sort_kind = sort->get_kind();
    uint32_t len       = d_rng.pick_uint32(0, SMTMBT_LEN_SYMBOL_MAX);
    /* Pick piped vs simple symbol with 50% probability. */
    std::string symbol = len && d_rng.flip_coin()
                             ? d_rng.pick_piped_symbol(len)
                             : d_rng.pick_simple_symbol(len);
    /* Create const. */
    Term res = d_solver.mk_const(sort, symbol);
    d_smgr.add_input(res, d_solver.get_sort(res), sort_kind);
    return true;
  }
};

class ActionMkValue : public Action
{
 public:
  ActionMkValue(SolverManager& smgr) : Action(smgr, "mk-value") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick sort of value. */
    if (!d_smgr.has_sort()) return false;
    Sort sort          = d_smgr.pick_sort();
    SortKind sort_kind = sort->get_kind();
    /* Pick value. */
    Term res;
    switch (sort_kind)
    {
      case SORT_BOOL: res = d_solver.mk_value(sort, d_rng.flip_coin()); break;

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
            val = d_rng.pick_uint64(0, (1 << bw) - 1);
          }
          res = d_solver.mk_value(sort, val);
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
          res = d_solver.mk_value(sort, val, base);
        }
      }
      break;
      default: assert(false);
    }
    d_smgr.add_input(res, d_solver.get_sort(res), sort_kind);
    return true;
  }
};

class ActionAssertFormula : public Action
{
 public:
  ActionAssertFormula(SolverManager& smgr) : Action(smgr, "assert-formula") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr.has_term(SORT_BOOL)) return false;
    Term assertion = d_smgr.pick_term(SORT_BOOL);
    d_solver.assert_formula(assertion);
    return true;
  }
};

class ActionCheckSat : public Action
{
 public:
  ActionCheckSat(SolverManager& smgr) : Action(smgr, "check-sat") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    d_solver.check_sat();
    return true;
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
  auto a_sat    = new_action<ActionCheckSat>();

  auto t_default = new_action<Transition>();
  auto t_inputs  = new_action<TransitionCreateInputs>();

  /* --------------------------------------------------------------------- */
  /* States                                                                */
  /* --------------------------------------------------------------------- */

  auto s_new    = new_state("new");
  auto s_delete = new_state("delete");
  auto s_final  = new_state("final", nullptr, true);

  auto s_inputs = new_state("create inputs");
  auto s_terms =
      new_state("create terms", [this]() { return d_smgr.has_term(); });

  auto s_assert =
      new_state("assert", [this]() { return d_smgr.has_term(SORT_BOOL); });

  auto s_sat = new_state("check sat");

  /* --------------------------------------------------------------------- */
  /* Transitions                                                           */
  /* --------------------------------------------------------------------- */

  /* State: new .......................................................... */
  s_new->add_action(a_new, 10, s_inputs);

  /* State: create inputs ................................................ */
  s_inputs->add_action(a_mksort, 20);
  s_inputs->add_action(a_mkval, 20);
  s_inputs->add_action(a_mkconst, 20);
  s_inputs->add_action(t_inputs, 20, s_terms);
  s_inputs->add_action(t_inputs, 1, s_sat);

  /* State: create terms ................................................. */
  s_terms->add_action(a_mkterm, 20);
  s_terms->add_action(t_default, 20, s_assert);
  s_terms->add_action(t_default, 1, s_sat);

  /* State: assert/assume formula ........................................ */
  s_assert->add_action(a_assert, 10);
  s_assert->add_action(t_default, 1, s_delete);
  s_assert->add_action(t_default, 10, s_sat);

  /* State: check sat .................................................... */
  s_sat->add_action(a_sat, 10, s_delete);

  /* State: delete ....................................................... */
  s_delete->add_action(a_delete, 10, s_final);


  /* --------------------------------------------------------------------- */
  /* Initial State                                                         */
  /* --------------------------------------------------------------------- */

  set_init_state(s_new);
}

}  // namespace smtmbt
