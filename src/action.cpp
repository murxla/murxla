#include "action.hpp"

#include "config.hpp"
#include "except.hpp"
#include "solver_manager.hpp"
#include "statistics.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

uint64_t
Action::untrace_str_to_id(const std::string& s)
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

SortKind
Action::get_sort_kind_from_str(const std::string& s)
{
  SortKind res = sort_kind_from_str(s);
  MURXLA_CHECK_CONFIG(res != SORT_ANY) << "unknown sort kind '" << s << "'";
  return res;
}

Action::Action(SolverManager& smgr,
               const Kind& kind,
               ReturnValue returns,
               bool empty)
    : d_rng(smgr.get_rng()),
      d_solver(smgr.get_solver()),
      d_smgr(smgr),
      d_returns(returns),
      d_is_empty(empty),
      d_kind(kind)

{
  MURXLA_CHECK_CONFIG(kind.size() <= MURXLA_MAX_KIND_LEN)
      << "'" << kind
      << "' exceeds maximum length for action kinds, increase limit by "
         "adjusting value of macro MURXLA_MAX_KIND_LEN in config.hpp";
}

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

Action::TraceStream::TraceStream(SolverManager& smgr) : d_smgr(smgr)
{
  stream();
}

Action::TraceStream::~TraceStream() { flush(); }

std::ostream&
Action::TraceStream::stream()
{
  return d_smgr.get_trace();
}

void
Action::TraceStream::flush()
{
  stream() << std::endl;
  stream().flush();
}

/* -------------------------------------------------------------------------- */

bool
TransitionCreateInputs::run()
{
  return d_smgr.d_stats.inputs > 0;
}

/* -------------------------------------------------------------------------- */

bool
TransitionCreateSorts::run()
{
  return d_smgr.d_stats.sorts > 0;
}

/* -------------------------------------------------------------------------- */

std::vector<uint64_t>
ActionTermGetSort::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
  Term t = d_smgr.get_term(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_TERM(t, tokens[0]);
  return _run(t);
}

std::vector<uint64_t>
ActionTermGetSort::_run(Term term)
{
  MURXLA_TRACE << get_kind() << " " << term;
  Sort res = term->get_sort();
  MURXLA_TRACE_RETURN << res;
  return {res->get_id()};
}

/* -------------------------------------------------------------------------- */

bool
ActionTermCheckSort::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.has_term()) return false;
  Term term = d_smgr.pick_term();
  _run(term);
  return true;
}

std::vector<uint64_t>
ActionTermCheckSort::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
  Term t = d_smgr.get_term(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_TERM(t, tokens[0]);
  _run(t);
  return {};
}

void
ActionTermCheckSort::_run(Term term)
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

/* -------------------------------------------------------------------------- */

bool
ActionNew::run()
{
  if (d_solver.is_initialized()) d_solver.delete_solver();
  _run();
  return true;
}

std::vector<uint64_t>
ActionNew::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  _run();
  return {};
}

void
ActionNew::_run()
{
  MURXLA_TRACE << get_kind();

  d_solver.new_solver();

  d_smgr.d_incremental       = d_solver.option_incremental_enabled();
  d_smgr.d_model_gen         = d_solver.option_model_gen_enabled();
  d_smgr.d_unsat_assumptions = d_solver.option_unsat_assumptions_enabled();
  d_smgr.d_unsat_cores       = d_solver.option_unsat_cores_enabled();
}

/* -------------------------------------------------------------------------- */

bool
ActionDelete::run()
{
  assert(d_solver.is_initialized());
  _run();
  return true;
}

std::vector<uint64_t>
ActionDelete::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  _run();
  return {};
}

void
ActionDelete::_run()
{
  MURXLA_TRACE << get_kind();
  d_smgr.clear();
  d_solver.delete_solver();
}

/* -------------------------------------------------------------------------- */

bool
ActionSetOption::run()
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
  if (d_rng.pick_with_prob(100))
  {
    std::tie(opt, value) =
        d_smgr.pick_option(d_solver.get_option_name_incremental(),
                           d_smgr.d_incremental ? "false" : "true");
  }
  else if (opt.empty() && d_rng.pick_with_prob(100))
  {
    std::tie(opt, value) =
        d_smgr.pick_option(d_solver.get_option_name_model_gen(),
                           d_smgr.d_model_gen ? "false" : "true");
  }
  else if (opt.empty() && d_rng.pick_with_prob(100))
  {
    std::tie(opt, value) =
        d_smgr.pick_option(d_solver.get_option_name_unsat_assumptions(),
                           d_smgr.d_unsat_assumptions ? "false" : "true");
  }
  else if (opt.empty() && d_rng.pick_with_prob(100))
  {
    std::tie(opt, value) =
        d_smgr.pick_option(d_solver.get_option_name_unsat_cores(),
                           d_smgr.d_unsat_cores ? "false" : "true");
  }
  /* Pick random options. */
  else
  {
    std::tie(opt, value) = d_smgr.pick_option();
  }

  if (opt.empty()) /* No option available */
  {
    return false;
  }

  _run(opt, value);
  return true;
}

std::vector<uint64_t>
ActionSetOption::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
  _run(tokens[0], tokens[1]);
  return {};
}

void
ActionSetOption::_run(const std::string& opt, const std::string& value)
{
  MURXLA_TRACE << get_kind() << " " << opt << " " << value;
  d_solver.set_opt(opt, value);
  d_smgr.d_incremental       = d_solver.option_incremental_enabled();
  d_smgr.d_model_gen         = d_solver.option_model_gen_enabled();
  d_smgr.d_unsat_assumptions = d_solver.option_unsat_assumptions_enabled();
  d_smgr.d_unsat_cores       = d_solver.option_unsat_cores_enabled();
}

/* -------------------------------------------------------------------------- */

bool
ActionMkSort::run()
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

std::vector<uint64_t>
ActionMkSort::untrace(const std::vector<std::string>& tokens)
{
  size_t n_tokens = tokens.size();

  MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);

  uint64_t res         = 0;
  SortKind kind        = get_sort_kind_from_str(tokens[0]);
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
      sorts.push_back(d_smgr.get_sort(untrace_str_to_id(tokens[1])));
      MURXLA_CHECK_TRACE(sorts[0] != nullptr)
          << "unknown sort id '" << tokens[1] << "' as argument to "
          << get_kind();
      sorts.push_back(d_smgr.get_sort(untrace_str_to_id(tokens[2])));
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
        Sort s = d_smgr.get_sort(untrace_str_to_id(*it));
        MURXLA_CHECK_TRACE(s != nullptr)
            << "unknown sort id '" << *it << "' as argument to " << get_kind();
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

uint64_t
ActionMkSort::_run(SortKind kind)
{
  MURXLA_TRACE << get_kind() << " " << kind;
  Sort res = d_solver.mk_sort(kind);
  d_smgr.add_sort(res, kind);
  MURXLA_TRACE_RETURN << res;
  return res->get_id();
}

uint64_t
ActionMkSort::_run(SortKind kind, uint32_t bw)
{
  MURXLA_TRACE << get_kind() << " " << kind << " " << bw;
  assert(kind == SORT_BV);
  Sort res = d_solver.mk_sort(kind, bw);
  assert(res->get_bv_size() == bw);
  d_smgr.add_sort(res, kind);
  MURXLA_TRACE_RETURN << res;
  return res->get_id();
}

uint64_t
ActionMkSort::_run(SortKind kind, uint32_t ew, uint32_t sw)
{
  MURXLA_TRACE << get_kind() << " " << kind << " " << ew << " " << sw;
  assert(kind == SORT_FP);
  Sort res = d_solver.mk_sort(kind, ew, sw);
  assert(res->get_fp_exp_size() == ew);
  assert(res->get_fp_sig_size() == sw);
  d_smgr.add_sort(res, kind);
  MURXLA_TRACE_RETURN << res;
  /* Operator fp expects three bit-vector terms of size 1, ew and sw - 1 as
   * arguments. To increase the probability that terms of these sizes are
   * available, we also generate the corresponding bit-vector sorts. */
  _run(SORT_BV, 1);
  _run(SORT_BV, ew);
  _run(SORT_BV, sw - 1);
  return res->get_id();
}

uint64_t
ActionMkSort::_run(SortKind kind, const std::vector<Sort>& sorts)
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

/* -------------------------------------------------------------------------- */

bool
ActionMkTerm::run()
{
  assert(d_solver.is_initialized());
  assert(d_smgr.get_enabled_theories().find(THEORY_BOOL)
         != d_smgr.get_enabled_theories().end());
  assert(d_smgr.has_term());

  /* Op gets only picked if there already exist terms that can be used as
   * operands. */
  const Op::Kind& kind = d_smgr.pick_op_kind();
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
    Sort array_sort                = d_smgr.pick_sort(op.get_arg_sort_kind(0));
    const std::vector<Sort>& sorts = array_sort->get_sorts();
    assert(sorts.size() == 2);
    Sort index_sort   = sorts[0];
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
        skind = op.get_arg_sort_kind(i);
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
        params.push_back(
            d_rng.pick<uint32_t>(1, std::max<uint32_t>(1, MURXLA_BW_MAX / bw)));
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

std::vector<uint64_t>
ActionMkTerm::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS_MIN(
      3, " (operator kind, sort id, number of arguments) ", tokens.size());

  std::vector<Term> args;
  std::vector<uint32_t> params;
  uint32_t n_tokens  = tokens.size();
  Op::Kind op_kind   = tokens[0];
  SortKind sort_kind = get_sort_kind_from_str(tokens[1]);
  uint32_t n_args    = str_to_uint32(tokens[2]);
  uint32_t idx       = 3;

  MURXLA_CHECK_TRACE(idx + n_args <= n_tokens)
      << "expected " << n_args << " term argument(s), got " << n_tokens - 3;

  for (uint32_t i = 0; i < n_args; ++i, ++idx)
  {
    uint32_t id = untrace_str_to_id(tokens[idx]);
    Term t      = d_smgr.get_term(id);
    MURXLA_CHECK_TRACE_TERM(t, id);
    args.push_back(t);
  }

  if (idx < tokens.size())
  {
    uint32_t n_params = str_to_uint32(tokens[idx++]);
    MURXLA_CHECK_TRACE(idx + n_params == n_tokens)
        << "expected " << n_args << " parameter(s) to create indexed term, got "
        << n_tokens - 3 - n_args;
    for (uint32_t i = 0; i < n_params; ++i, ++idx)
    {
      uint32_t param = str_to_uint32(tokens[idx]);
      params.push_back(param);
    }
  }
  return _run(op_kind, sort_kind, args, params);
}

std::vector<uint64_t>
ActionMkTerm::_run(Op::Kind kind,
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
  Sort res_sort = res->get_sort();

  if (kind == Op::ARRAY_SELECT && d_rng.pick_with_prob(10))
  {
    Sort array_sort   = args[0]->get_sort();
    Sort index_sort   = array_sort->get_array_index_sort();
    Sort element_sort = array_sort->get_array_element_sort();
    assert(index_sort == nullptr || index_sort->equals(args[1]->get_sort()));
    assert(element_sort == nullptr || element_sort->equals(res_sort));
  }
  else if (kind == Op::ARRAY_STORE && d_rng.pick_with_prob(10))
  {
    Sort array_sort   = args[0]->get_sort();
    Sort index_sort   = array_sort->get_array_index_sort();
    Sort element_sort = array_sort->get_array_element_sort();
    assert(index_sort == nullptr || index_sort->equals(args[1]->get_sort()));
    assert(element_sort == nullptr
           || element_sort->equals(args[2]->get_sort()));
  }
  else if (kind == Op::UF_APPLY && d_rng.pick_with_prob(10))
  {
    Sort fun_sort                  = args[0]->get_sort();
    Sort codomain_sort             = fun_sort->get_fun_codomain_sort();
    std::vector<Sort> domain_sorts = fun_sort->get_fun_domain_sorts();
    assert(codomain_sort == nullptr || codomain_sort->equals(res_sort));
    if (!domain_sorts.empty())
    {
      assert(domain_sorts.size() == fun_sort->get_fun_arity());
      for (size_t i = 0, size = domain_sorts.size(); i < size; ++i)
      {
        assert(domain_sorts[i]->equals(args[i + 1]->get_sort()));
      }
    }
  }

  MURXLA_TRACE_RETURN << res << " " << res_sort;
  return {res->get_id(), res_sort->get_id()};
}

/* -------------------------------------------------------------------------- */

bool
ActionMkConst::run()
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

std::vector<uint64_t>
ActionMkConst::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
  Sort sort = d_smgr.get_sort(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
  std::string symbol = str_to_str(tokens[1]);
  return _run(sort, symbol);
}

std::vector<uint64_t>
ActionMkConst::_run(Sort sort, std::string& symbol)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << symbol << "\"";
  Term res = d_solver.mk_const(sort, symbol);
  d_smgr.add_input(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  return {res->get_id()};
}

/* -------------------------------------------------------------------------- */

bool
ActionMkVar::run()
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

std::vector<uint64_t>
ActionMkVar::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
  Sort sort = d_smgr.get_sort(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
  std::string symbol = str_to_str(tokens[1]);
  return _run(sort, symbol);
}

std::vector<uint64_t>
ActionMkVar::_run(Sort sort, std::string& symbol)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << symbol << "\"";
  Term res = d_solver.mk_var(sort, symbol);
  d_smgr.add_var(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  return {res->get_id()};
}

/* -------------------------------------------------------------------------- */

bool
ActionMkValue::run()
{
  assert(d_solver.is_initialized());
  /* Pick sort of value. */
  if (!d_smgr.has_sort()) return false;
  Sort sort          = d_smgr.pick_sort();
  SortKind sort_kind = sort->get_kind();

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
        case Solver::Base::DEC:
          val = d_rng.pick_dec_bin_string(bw, d_rng.flip_coin());
          break;
        case Solver::Base::HEX: val = d_rng.pick_hex_bin_string(bw); break;
        default:
          assert(base == Solver::Base::BIN);
          val = d_rng.pick_bin_string(bw);
      }
      _run(sort, val, base);
    }
    break;

    case SORT_FP:
    {
      uint32_t ew     = sort->get_fp_exp_size();
      uint32_t sw     = sort->get_fp_sig_size();
      std::string val = d_rng.pick_bin_string(ew + sw);
      _run(sort, val);
    }
    break;

    case SORT_INT:
      _run(sort,
           d_rng.pick_dec_int_string(
               d_rng.pick<uint32_t>(1, MURXLA_INT_LEN_MAX)));
      break;

    case SORT_REAL:
      /* RNGenerator::pick_real_string picks from 2 different options, hence
       * we pick between this and passing two decimal strings as rational
       * arguments with probability 50%. */
      if (d_rng.pick_with_prob(500))
      {
        _run(sort, d_rng.pick_real_string());
      }
      else
      {
        if (d_rng.flip_coin())
        {
          _run(sort,
               d_rng.pick_dec_rational_string(
                   d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX),
                   d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX)));
        }
        else
        {
          _run(sort,
               d_rng.pick_dec_int_string(
                   d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX)),
               d_rng.pick_dec_int_string(
                   d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX)));
        }
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

std::vector<uint64_t>
ActionMkValue::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);

  uint64_t res = 0;
  Sort sort    = d_smgr.get_sort(untrace_str_to_id(tokens[0]));
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

uint64_t
ActionMkValue::_run(Sort sort, bool val)
{
  MURXLA_TRACE << get_kind() << " " << sort << " " << (val ? "true" : "false");
  Term res = d_solver.mk_value(sort, val);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  return res->get_id();
}

uint64_t
ActionMkValue::_run(Sort sort, std::string val)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
  Term res;
  res = d_solver.mk_value(sort, val);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  return res->get_id();
}

uint64_t
ActionMkValue::_run(Sort sort, std::string val, size_t len)
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

uint64_t
ActionMkValue::_run(Sort sort, std::string v0, std::string v1)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << v0 << "\""
               << " \"" << v1 << "\"";
  Term res = d_solver.mk_value(sort, v0, v1);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  return res->get_id();
}

uint64_t
ActionMkValue::_run(Sort sort, std::string val, Solver::Base base)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\""
               << " " << base;
  Term res = d_solver.mk_value(sort, val, base);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  return res->get_id();
}

/* -------------------------------------------------------------------------- */

bool
ActionMkSpecialValue::run()
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

std::vector<uint64_t>
ActionMkSpecialValue::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());

  uint64_t res = 0;
  Sort sort    = d_smgr.get_sort(untrace_str_to_id(tokens[0]));
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

uint64_t
ActionMkSpecialValue::_run(Sort sort, const Solver::SpecialValueKind& val)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
  Term res;
  res = d_solver.mk_special_value(sort, val);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  return res->get_id();
}

/* -------------------------------------------------------------------------- */

bool
ActionAssertFormula::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.has_term(SORT_BOOL, 0)) return false;
  Term assertion = d_smgr.pick_term(SORT_BOOL, 0);

  _run(assertion);
  return true;
}

std::vector<uint64_t>
ActionAssertFormula::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
  Term t = d_smgr.get_term(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_TERM(t, tokens[0]);
  _run(t);
  return {};
}

void
ActionAssertFormula::_run(Term assertion)
{
  MURXLA_TRACE << get_kind() << " " << assertion;
  reset_sat();
  d_solver.assert_formula(assertion);
}

/* -------------------------------------------------------------------------- */

bool
ActionCheckSat::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_incremental && d_smgr.d_n_sat_calls > 0) return false;
  /* Only call action immediately again with low priority. */
  if (d_smgr.d_sat_called && d_rng.pick_with_prob(95)) return false;
  _run();
  return true;
}

std::vector<uint64_t>
ActionCheckSat::untrace(const std::vector<std::string>& tokens)
{
  assert(tokens.empty());
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  _run();
  return {};
}

void
ActionCheckSat::_run()
{
  MURXLA_TRACE << get_kind();
  reset_sat();
  d_smgr.d_sat_result = d_solver.check_sat();
  d_smgr.d_sat_called = true;
  d_smgr.d_n_sat_calls += 1;
  d_smgr.d_mbt_stats->d_results[d_smgr.d_sat_result]++;
}

/* -------------------------------------------------------------------------- */

bool
ActionCheckSatAssuming::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_incremental) return false;
  if (!d_smgr.has_term(SORT_BOOL, 0)) return false;
  /* Only call action immediately again with low priority. */
  if (d_smgr.d_sat_called && d_rng.pick_with_prob(95)) return false;
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

std::vector<uint64_t>
ActionCheckSatAssuming::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);
  std::vector<Term> assumptions;
  uint32_t n_args = str_to_uint32(tokens[0]);
  for (uint32_t i = 0, idx = 1; i < n_args; ++i, ++idx)
  {
    uint32_t id = untrace_str_to_id(tokens[idx]);
    Term t      = d_smgr.get_term(id);
    MURXLA_CHECK_TRACE_TERM(t, id);
    assumptions.push_back(t);
  }
  _run(assumptions);
  return {};
}

void
ActionCheckSatAssuming::_run(std::vector<Term> assumptions)
{
  MURXLA_TRACE << get_kind() << " " << assumptions.size() << assumptions;
  reset_sat();
  d_smgr.d_sat_result = d_solver.check_sat_assuming(assumptions);
  d_smgr.d_sat_called = true;
  d_smgr.d_n_sat_calls += 1;
  d_smgr.d_mbt_stats->d_results[d_smgr.d_sat_result]++;
}

/* -------------------------------------------------------------------------- */

bool
ActionGetUnsatAssumptions::run()
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

std::vector<uint64_t>
ActionGetUnsatAssumptions::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  _run();
  return {};
}

void
ActionGetUnsatAssumptions::_run()
{
  MURXLA_TRACE << get_kind();
  /* Note: The Terms in this vector are solver terms wrapped into Term,
   *       without sort information! */
  std::vector<Term> res = d_solver.get_unsat_assumptions();
  for (Term& fa : res)
  {
    Term t = d_smgr.find_term(fa, d_solver.get_sort(fa, SORT_BOOL), SORT_BOOL);
    assert(t != nullptr);
    assert(d_smgr.is_assumed(t));
    assert(d_solver.is_unsat_assumption(t));
  }
  if (d_rng.flip_coin())
  {
    assert(d_solver.check_sat_assuming(res) != Solver::Result::SAT);
  }
}

/* -------------------------------------------------------------------------- */

bool
ActionGetUnsatCore::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_unsat_cores) return false;
  if (!d_smgr.d_sat_called) return false;
  if (d_smgr.d_sat_result != Solver::Result::UNSAT) return false;
  _run();
  return true;
}

std::vector<uint64_t>
ActionGetUnsatCore::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  _run();
  return {};
}

void
ActionGetUnsatCore::_run()
{
  MURXLA_TRACE << get_kind();
  /* Note: The Terms in this vector are solver terms wrapped into Term,
   *       without sort information! */
  std::vector<Term> res = d_solver.get_unsat_core();
  for (Term& fa : res)
  {
    Term t = d_smgr.find_term(fa, d_solver.get_sort(fa, SORT_BOOL), SORT_BOOL);
    assert(t != nullptr);
  }
}

/* -------------------------------------------------------------------------- */

bool
ActionGetValue::run()
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

std::vector<uint64_t>
ActionGetValue::untrace(const std::vector<std::string>& tokens)
{
  assert(tokens.size() > 1);
  std::vector<Term> terms;
  uint32_t n_args = str_to_uint32(tokens[0]);
  for (uint32_t i = 0, idx = 1; i < n_args; ++i, ++idx)
  {
    uint32_t id = untrace_str_to_id(tokens[idx]);
    Term t      = d_smgr.get_term(id);
    MURXLA_CHECK_TRACE_TERM(t, id);
    terms.push_back(t);
  }
  return _run(terms);
}

std::vector<uint64_t>
ActionGetValue::_run(std::vector<Term> terms)
{
  MURXLA_TRACE << get_kind() << " " << terms.size() << terms;
  std::vector<uint64_t> res;
  /* Note: The Terms in this vector are solver terms wrapped into Term,
   *       without sort information! */
  std::vector<Term> res_terms = d_solver.get_value(terms);
  assert(terms.size() == res_terms.size());
  if (d_smgr.d_incremental)
  {
    /* assume assignment and check if result is still SAT */
    std::vector<Term> assumptions;
    for (size_t i = 0, n = terms.size(); i < n; ++i)
    {
      std::vector<Term> args = {terms[i], res_terms[i]};
      std::vector<uint32_t> params;
      assumptions.push_back(d_solver.mk_term(Op::EQUAL, args, params));
    }
    assert(d_solver.check_sat_assuming(assumptions) != Solver::Result::UNSAT);
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

/* -------------------------------------------------------------------------- */

bool
ActionPush::run()
{
  assert(d_solver.is_initialized());
  uint32_t n_levels = d_rng.pick<uint32_t>(1, MURXLA_MAX_N_PUSH_LEVELS);
  _run(n_levels);
  return true;
}

std::vector<uint64_t>
ActionPush::untrace(const std::vector<std::string>& tokens)
{
  assert(tokens.size() == 1);
  uint32_t n_levels = str_to_uint32(tokens[0]);
  _run(n_levels);
  return {};
}

void
ActionPush::_run(uint32_t n_levels)
{
  MURXLA_TRACE << get_kind() << " " << n_levels;
  reset_sat();
  d_solver.push(n_levels);
  d_smgr.d_n_push_levels += n_levels;
}

/* -------------------------------------------------------------------------- */

bool
ActionPop::run()
{
  assert(d_solver.is_initialized());
  if (d_smgr.d_n_push_levels == 0) return false;
  uint32_t n_levels = d_rng.pick<uint32_t>(1, d_smgr.d_n_push_levels);
  _run(n_levels);
  return true;
}

std::vector<uint64_t>
ActionPop::untrace(const std::vector<std::string>& tokens)
{
  assert(tokens.size() == 1);
  uint32_t n_levels = str_to_uint32(tokens[0]);
  _run(n_levels);
  return {};
}

void
ActionPop::_run(uint32_t n_levels)
{
  MURXLA_TRACE << get_kind() << " " << n_levels;
  reset_sat();
  d_solver.pop(n_levels);
  d_smgr.d_n_push_levels -= n_levels;
}

/* -------------------------------------------------------------------------- */

bool
ActionReset::run()
{
  assert(d_solver.is_initialized());
  _run();
  return true;
}

std::vector<uint64_t>
ActionReset::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  _run();
  return {};
}

void
ActionReset::_run()
{
  MURXLA_TRACE << get_kind();
  d_solver.reset();
  d_smgr.reset();
}

/* -------------------------------------------------------------------------- */

bool
ActionResetAssertions::run()
{
  assert(d_solver.is_initialized());
  _run();
  return true;
}

std::vector<uint64_t>
ActionResetAssertions::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  _run();
  return {};
}

void
ActionResetAssertions::_run()
{
  MURXLA_TRACE << get_kind();
  reset_sat();
  d_solver.reset_assertions();
  d_smgr.d_n_push_levels = 0;
}

/* -------------------------------------------------------------------------- */

bool
ActionPrintModel::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_model_gen) return false;
  if (!d_smgr.d_sat_called) return false;
  if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
  _run();
  return true;
}

std::vector<uint64_t>
ActionPrintModel::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  _run();
  return {};
}

void
ActionPrintModel::_run()
{
  MURXLA_TRACE << get_kind();
  d_solver.print_model();
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla
