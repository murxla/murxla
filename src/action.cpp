#include "action.hpp"

#include <algorithm>

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
      d_sng(smgr.get_sng()),
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
Action::seed_solver_rng() const
{
  assert(!d_sng.is_untrace_mode());
  uint32_t seed = d_sng.next_solver_seed();
  d_solver.get_rng().reseed(seed);
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

bool
ActionTermGetChildren::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.has_term()) return false;
  Term term = d_smgr.pick_term();
  _run(term);
  return true;
}

std::vector<uint64_t>
ActionTermGetChildren::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
  Term t = d_smgr.get_untraced_term(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_TERM(t, tokens[0]);
  _run(t);
  return {};
}

void
ActionTermGetChildren::_run(Term term)
{
  MURXLA_TRACE << get_kind() << " " << term;

  /* Call Term::get_kind(). */
  Op::Kind kind = term->get_kind();
  /* Call Term::get_children(). */
  std::vector<Term> children = term->get_children();
  /* Perform some checks based on term kind */
  if (!children.empty())
  {
    if (kind == Op::ARRAY_SELECT)
    {
      assert(children.size() == 2);
      Sort array_sort            = d_solver.get_sort(children[0], SORT_ANY);
      Sort index_sort_expected   = array_sort->get_array_index_sort();
      Sort element_sort_expected = array_sort->get_array_element_sort();
      Sort index_sort            = d_solver.get_sort(children[1], SORT_ANY);
      MURXLA_TEST(index_sort_expected->equals(index_sort));
      MURXLA_TEST(element_sort_expected->equals(term->get_sort()));
    }
    else if (kind == Op::ARRAY_STORE)
    {
      assert(children.size() == 3);
      Sort array_sort            = d_solver.get_sort(children[0], SORT_ANY);
      Sort index_sort_expected   = array_sort->get_array_index_sort();
      Sort element_sort_expected = array_sort->get_array_element_sort();
      Sort index_sort            = d_solver.get_sort(children[1], SORT_ANY);
      Sort element_sort          = d_solver.get_sort(children[2], SORT_ANY);
      MURXLA_TEST(index_sort_expected->equals(index_sort));
      MURXLA_TEST(element_sort_expected->equals(element_sort));
    }
    else if (kind == Op::UF_APPLY)
    {
      assert(children.size() >= 1);
      Sort fun_sort               = d_solver.get_sort(children[0], SORT_ANY);
      Sort codomain_sort_expected = fun_sort->get_fun_codomain_sort();
      std::vector<Sort> domain_sorts_expected =
          fun_sort->get_fun_domain_sorts();
      MURXLA_TEST(domain_sorts_expected.size() == children.size() - 1);
      MURXLA_TEST(codomain_sort_expected->equals(term->get_sort()));
      if (!domain_sorts_expected.empty())
      {
        MURXLA_TEST(domain_sorts_expected.size() == fun_sort->get_fun_arity());
        for (size_t i = 0, size = domain_sorts_expected.size(); i < size; ++i)
        {
          MURXLA_TEST(domain_sorts_expected[i]->equals(
              d_solver.get_sort(children[i + 1], SORT_ANY)));
        }
      }
    }
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
ActionSetLogic::run()
{
  assert(d_solver.is_initialized());

  TheoryIdSet enabled_theories = d_smgr.get_enabled_theories();
  enabled_theories.erase(THEORY_BOOL);

  auto it = enabled_theories.find(THEORY_QUANT);
  enabled_theories.erase(THEORY_QUANT);
  bool is_quant = it != enabled_theories.end();

  std::string logic = "";

  it = enabled_theories.find(THEORY_ARRAY);
  if (it != enabled_theories.end())
  {
    enabled_theories.erase(THEORY_ARRAY);
    /* Only THEORY_ARRAY left, use AX. */
    logic += enabled_theories.empty() ? "AX" : "A";
  }

  it = enabled_theories.find(THEORY_UF);
  if (it != enabled_theories.end())
  {
    enabled_theories.erase(THEORY_UF);
    logic += "UF";
  }

  it = enabled_theories.find(THEORY_BV);
  if (it != enabled_theories.end())
  {
    enabled_theories.erase(THEORY_BV);
    logic += "BV";
  }

  it = enabled_theories.find(THEORY_FP);
  if (it != enabled_theories.end())
  {
    enabled_theories.erase(THEORY_FP);
    logic += "FP";
  }

  it = enabled_theories.find(THEORY_DT);
  if (it != enabled_theories.end())
  {
    enabled_theories.erase(THEORY_DT);
    logic += "DT";
  }

  it = enabled_theories.find(THEORY_STRING);
  if (it != enabled_theories.end())
  {
    enabled_theories.erase(THEORY_STRING);
    logic += "S";
  }

  auto int_enabled =
      enabled_theories.find(THEORY_INT) != enabled_theories.end();
  auto real_enabled =
      enabled_theories.find(THEORY_REAL) != enabled_theories.end();

  if (int_enabled || real_enabled)
  {
    logic += d_smgr.d_arith_linear ? "L" : "N";
    if (int_enabled)
    {
      enabled_theories.erase(THEORY_INT);
      logic += "I";
    }
    if (real_enabled)
    {
      enabled_theories.erase(THEORY_REAL);
      logic += "R";
    }
    logic += "A";
  }

  /* If we didn't cover all enabled theories, we just use logic ALL. */
  if (!enabled_theories.empty() || logic.empty())
  {
    logic = "ALL";
  }

  if (!is_quant)
  {
    logic = "QF_" + logic;
  }

  _run(logic);
  return true;
}

std::vector<uint64_t>
ActionSetLogic::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
  _run(tokens[0]);
  return {};
}

void
ActionSetLogic::_run(const std::string& logic)
{
  MURXLA_TRACE << get_kind() << " " << logic;
  d_solver.set_logic(logic);
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
    std::tie(opt, value) = d_smgr.pick_option(
        d_solver.get_option_name_incremental(),
        d_solver.option_incremental_enabled() ? "false" : "true");
  }
  if (opt.empty() && d_rng.pick_with_prob(100))
  {
    std::tie(opt, value) = d_smgr.pick_option(
        d_solver.get_option_name_model_gen(),
        d_solver.option_model_gen_enabled() ? "false" : "true");
  }
  if (opt.empty() && d_rng.pick_with_prob(100))
  {
    std::tie(opt, value) = d_smgr.pick_option(
        d_solver.get_option_name_unsat_assumptions(),
        d_solver.option_unsat_assumptions_enabled() ? "false" : "true");
  }
  if (opt.empty() && d_rng.pick_with_prob(100))
  {
    std::tie(opt, value) = d_smgr.pick_option(
        d_solver.get_option_name_unsat_cores(),
        d_solver.option_unsat_cores_enabled() ? "false" : "true");
  }
  /* Pick random options. */
  if (opt.empty())
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
  try
  {
    d_solver.set_opt(opt, value);
    d_smgr.d_incremental       = d_solver.option_incremental_enabled();
    d_smgr.d_model_gen         = d_solver.option_model_gen_enabled();
    d_smgr.d_unsat_assumptions = d_solver.option_unsat_assumptions_enabled();
    d_smgr.d_unsat_cores       = d_solver.option_unsat_cores_enabled();
    d_smgr.mark_option_used(opt);  // only set options once
  }
  catch (const MurxlaSolverOptionException& e)
  {
  }
}

/* -------------------------------------------------------------------------- */

bool
ActionSetOptionReq::run()
{
  for (const auto& [name, value] : d_solver_options)
  {
    d_setoption->_run(name, value);
  }
  return true;
}

std::vector<uint64_t>
ActionSetOptionReq::untrace(const std::vector<std::string>& tokens)
{
  return {};
}

void
ActionSetOptionReq::init(
    const std::vector<std::pair<std::string, std::string>>& solver_options,
    ActionSetOption* setoption)
{
  d_solver_options.insert(
      d_solver_options.end(), solver_options.begin(), solver_options.end());
  d_setoption = setoption;
}

/* -------------------------------------------------------------------------- */

ActionMkSort::ActionMkSort(SolverManager& smgr) : Action(smgr, MK_SORT, ID_LIST)
{
  d_n_args_weights.push_back(0);
  for (uint32_t i = 0; i < MURXLA_MK_TERM_N_ARGS_MAX; ++i)
  {
    uint32_t n = MURXLA_MK_TERM_N_ARGS_MAX - i;
    d_n_args_weights.push_back(n * n);
  }
}

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

      if (!d_smgr.has_sort_excluding(exclude_index_sorts, false))
      {
        return false;
      }
      Sort index_sort = d_smgr.pick_sort_excluding(exclude_index_sorts, false);
      if (!d_smgr.has_sort_excluding(exclude_element_sorts, false))
      {
        return false;
      }
      Sort element_sort =
          d_smgr.pick_sort_excluding(exclude_element_sorts, false);
      _run(kind, {index_sort, element_sort});
      break;
    }

    case SORT_BAG:
    {
      SortKindSet exclude_sorts =
          d_solver.get_unsupported_bag_element_sort_kinds();
      if (!d_smgr.has_sort_excluding(exclude_sorts, false)) return false;
      auto sort = d_smgr.pick_sort_excluding(exclude_sorts, false);
      _run(kind, {sort});
    }
    break;

    case SORT_BV:
      _run(kind, d_rng.pick<uint32_t>(MURXLA_BW_MIN, MURXLA_BW_MAX));
      break;

    case SORT_DT:
    {
      if (!d_smgr.has_sort()) return false;

      SortKindSet exclude_sorts =
          d_solver.get_unsupported_dt_sel_codomain_sort_kinds();
      bool no_sel_sorts = !d_smgr.has_sort_excluding(exclude_sorts, false);

      uint32_t n_dt_sorts = d_rng.pick<uint32_t>(1, MURXLA_DT_MAX_N_DTYPES);
      bool mutual_rec     = n_dt_sorts > 1 && d_rng.flip_coin();

      std::vector<std::string> dt_names;
      std::vector<std::vector<Sort>> param_sorts;
      std::vector<AbsSort::DatatypeConstructorMap> constructors;
      std::unordered_map<std::string, uint32_t> dt_n_params;

      for (uint32_t i = 0; i < n_dt_sorts; ++i)
      {
        dt_names.push_back(d_smgr.pick_symbol());
        bool parametric = (no_sel_sorts && !mutual_rec) || d_rng.flip_coin();
        std::vector<Sort> psorts;
        uint32_t n_psorts = 0;
        if (parametric)
        {
          n_psorts = d_rng.pick<uint32_t>(MURXLA_DT_PARAM_SORT_MIN,
                                          MURXLA_DT_PARAM_SORT_MAX);
          for (uint32_t j = 0; j < n_psorts; ++j)
          {
            psorts.push_back(std::shared_ptr<ParamSort>(
                new ParamSort(d_smgr.pick_symbol())));
          }
        }
        param_sorts.push_back(psorts);
        dt_n_params[dt_names.back()] = n_psorts;
      }

      for (uint32_t i = 0; i < n_dt_sorts; ++i)
      {
        const std::string& dt_name = dt_names[i];
        const auto& psorts         = param_sorts[i];
        bool parametric            = psorts.size() > 0;

        uint32_t n_ctors =
            d_rng.pick<uint32_t>(MURXLA_DT_CON_MIN, MURXLA_DT_CON_MAX);
        AbsSort::DatatypeConstructorMap ctors;

        for (uint32_t j = 0; j < n_ctors; ++j)
        {
          uint32_t n_sels =
              no_sel_sorts && !parametric
                  ? 0
                  : d_rng.pick<uint32_t>(MURXLA_DT_SEL_MIN, MURXLA_DT_SEL_MAX);
          std::vector<std::pair<std::string, Sort>> sels;
          std::unordered_set<std::string> sel_names;
          for (uint32_t k = 0; k < n_sels; ++k)
          {
            std::string sname;
            do
            {
              sname = d_smgr.pick_symbol();
            } while (sel_names.find(sname) != sel_names.end());
            sel_names.insert(sname);
            /* Pick datatype sort itself with 10% probability. We indicate this
             * by passing a nullptr Sort. */
            Sort s = nullptr;
            if (d_rng.pick_with_prob(900))
            {
              if (parametric
                  && ((no_sel_sorts && !mutual_rec) || d_rng.flip_coin()))
              {
                s = d_rng.pick_from_set<decltype(psorts), Sort>(psorts);
              }
              else if (mutual_rec && d_rng.flip_coin())
              {
                std::string uname;
                do
                {
                  uname = d_rng.pick_from_set<decltype(dt_names), std::string>(
                      dt_names);
                } while (uname == dt_name);
                s = std::shared_ptr<UnresolvedSort>(new UnresolvedSort(uname));
                if (dt_n_params.at(uname) > 0)
                {
                  /* pick sorts to instantiate parametric (unresolved) sort */
                  std::vector<Sort> inst_sorts;
                  for (size_t l = 0, n = dt_n_params.at(uname); l < n; ++l)
                  {
                    if (psorts.size() && d_rng.flip_coin())
                    {
                      inst_sorts.push_back(
                          d_rng.pick_from_set<decltype(psorts), Sort>(psorts));
                    }
                    else
                    {
                      SortKindSet excl =
                          d_solver.get_unsupported_sort_param_sort_kinds();
                      inst_sorts.push_back(
                          d_smgr.pick_sort_excluding(excl, false));
                    }
                  }
                  s->set_sorts(inst_sorts);
                }
              }
              else
              {
                s = d_smgr.pick_sort_excluding(exclude_sorts, false);
              }
            }
            sels.emplace_back(sname, s);
          }

          std::string cname;
          do
          {
            cname = d_smgr.pick_symbol();
          } while (ctors.find(cname) != ctors.end());
          ctors[cname] = sels;
        }
        constructors.push_back(ctors);
      }
      _run(kind, dt_names, param_sorts, constructors);
    }
    break;

    case SORT_FP:
    {
      // TODO: support arbitrary formats (for now we only support Float16,
      //       Float32, Float64, Float128
      pick = d_rng.pick_one_of_four();
      uint32_t ew, sw;
      switch (pick)
      {
        case RNGenerator::Choice::FIRST:
          ew = 5;
          sw = 11;
          break;
        case RNGenerator::Choice::SECOND:
          ew = 8;
          sw = 24;
          break;
        case RNGenerator::Choice::THIRD:
          ew = 11;
          sw = 53;
          break;
        default:
          assert(pick == RNGenerator::Choice::FOURTH);
          ew = 15;
          sw = 113;
      }
      _run(kind, ew, sw);
      /* Operator fp expects three bit-vector terms of size 1, ew and sw - 1 as
       * arguments. Operator to_fp from IEEE BV expects a bit-vector of size
       * ew + sw. To increase the probability that terms of these sizes are
       * available, we also generate the corresponding bit-vector sorts. */
      _run(SORT_BV, 1);
      _run(SORT_BV, ew);
      _run(SORT_BV, sw - 1);
      _run(SORT_BV, ew + sw);
    }
    break;

    case SORT_FUN:
    {
      std::vector<Sort> sorts;
      SortKindSet exclude_domain_sorts =
          d_solver.get_unsupported_fun_domain_sort_kinds();
      SortKindSet exclude_codomain_sorts =
          d_solver.get_unsupported_fun_codomain_sort_kinds();
      if (!d_smgr.has_sort_excluding(exclude_domain_sorts, false)
          || !d_smgr.has_sort_excluding(exclude_codomain_sorts, false))
      {
        return false;
      }
      uint32_t nsorts = d_rng.pick_weighted<uint32_t>(d_n_args_weights.begin(),
                                                      d_n_args_weights.end());
      for (uint32_t i = 0; i < nsorts; ++i)
      {
        sorts.push_back(
            d_smgr.pick_sort_excluding(exclude_domain_sorts, false));
      }
      sorts.push_back(
          d_smgr.pick_sort_excluding(exclude_codomain_sorts, false));
      _run(kind, sorts);
    }
    break;

    case SORT_SEQ:
    {
      SortKindSet exclude_sorts =
          d_solver.get_unsupported_seq_element_sort_kinds();
      if (!d_smgr.has_sort_excluding(exclude_sorts, false)) return false;
      auto sort = d_smgr.pick_sort_excluding(exclude_sorts, false);
      _run(kind, {sort});
    }
    break;

    case SORT_SET:
    {
      SortKindSet exclude_sorts =
          d_solver.get_unsupported_set_element_sort_kinds();
      if (!d_smgr.has_sort_excluding(exclude_sorts, false)) return false;
      auto sort = d_smgr.pick_sort_excluding(exclude_sorts, false);
      _run(kind, {sort});
    }
    break;

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

  std::vector<uint64_t> res;
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
      sorts.push_back(d_smgr.get_untraced_sort(untrace_str_to_id(tokens[1])));
      MURXLA_CHECK_TRACE(sorts[0] != nullptr)
          << "unknown sort id '" << tokens[1] << "' as argument to "
          << get_kind();
      sorts.push_back(d_smgr.get_untraced_sort(untrace_str_to_id(tokens[2])));
      MURXLA_CHECK_TRACE(sorts[1] != nullptr)
          << "unknown sort id '" << tokens[2] << "' as argument to "
          << get_kind();
      res = _run(kind, sorts);
      break;
    }

    case SORT_BAG:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_BAG) != theories.end())
          << "solver does not support theory of bags";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(2, n_tokens, kind);
      res =
          _run(kind, {d_smgr.get_untraced_sort(untrace_str_to_id(tokens[1]))});
      break;

    case SORT_BOOL:
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

    case SORT_DT:
    {
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_DT) != theories.end())
          << "solver does not support theory of datatypes";
      MURXLA_CHECK_TRACE_NTOKENS_MIN(5, "", n_tokens);
      uint32_t n_dt_sorts = str_to_uint32(tokens[1]);
      uint32_t idx        = 2;

      std::vector<std::string> dt_names;
      std::vector<std::vector<Sort>> param_sorts;
      std::vector<AbsSort::DatatypeConstructorMap> constructors;

      for (uint32_t j = 0; j < n_dt_sorts; ++j)
      {
        std::string dt_name = str_to_str(tokens[idx++]);
        uint32_t n_params   = str_to_uint32(tokens[idx++]);
        std::vector<Sort> psorts;
        std::unordered_map<std::string, Sort> symbol_to_psort;
        std::unordered_map<std::string, Sort> symbol_to_usort;
        for (uint32_t i = 0; i < n_params; ++i)
        {
          MURXLA_CHECK_TRACE(tokens[idx].substr(0, 2) == "s\"")
              << "expected parameter sort string of the form 's\"<symbol>\"'";
          std::string pname = str_to_str(tokens[idx++].substr(1));
          psorts.push_back(std::shared_ptr<ParamSort>(new ParamSort(pname)));
          assert(symbol_to_psort.find(pname) == symbol_to_psort.end());
          symbol_to_psort[pname] = psorts.back();
        }

        AbsSort::DatatypeConstructorMap ctors;
        uint32_t n_ctors = str_to_uint32(tokens[idx++]);
        for (uint32_t i = 0; i < n_ctors; ++i)
        {
          std::string cname = str_to_str(tokens[idx++]);
          ctors[cname]      = {};
          uint32_t n_sels   = str_to_uint32(tokens[idx++]);
          for (uint32_t j = 0; j < n_sels; ++j)
          {
            std::string sname = str_to_str(tokens[idx++]);
            Sort ssort;
            if (tokens[idx] == "s(nil)")
            {
              ssort = nullptr;
              idx += 1;
            }
            else if (tokens[idx].substr(0, 2) == "s\"")
            {
              std::string pname = str_to_str(tokens[idx++].substr(1));
              assert(symbol_to_psort.find(pname) != symbol_to_psort.end());
              ssort = symbol_to_psort[pname];
            }
            else if (tokens[idx].substr(0, 2) == "s<")
            {
              const std::string& t = tokens[idx++];
              std::string uname    = str_to_str(t.substr(2, t.size() - 3));
              const auto& it       = symbol_to_usort.find(uname);
              if (it == symbol_to_usort.end())
              {
                ssort =
                    std::shared_ptr<UnresolvedSort>(new UnresolvedSort(uname));
                symbol_to_usort[uname] = ssort;
              }
              else
              {
                ssort = it->second;
              }
            }
            else
            {
              ssort =
                  d_smgr.get_untraced_sort(untrace_str_to_id(tokens[idx++]));
            }
            ctors[cname].emplace_back(sname, ssort);
          }
        }
        dt_names.push_back(dt_name);
        param_sorts.push_back(psorts);
        constructors.push_back(ctors);
      }

      res = _run(kind, dt_names, param_sorts, constructors);
    }
    break;

    case SORT_FP:
      MURXLA_CHECK_TRACE(theories.find(THEORY_FP) != theories.end()
                         || theories.find(THEORY_FP) != theories.end())
          << "solver does not support theory of floating-point arithmetic";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(3, n_tokens, kind);
      res = _run(kind, str_to_uint32(tokens[1]), str_to_uint32(tokens[2]));
      break;

    case SORT_FUN:
    {
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_UF) != theories.end())
          << "solver does not support theory of UF";
      std::vector<Sort> sorts;
      for (auto it = tokens.begin() + 1; it < tokens.end(); ++it)
      {
        Sort s = d_smgr.get_untraced_sort(untrace_str_to_id(*it));
        MURXLA_CHECK_TRACE(s != nullptr)
            << "unknown sort id '" << *it << "' as argument to " << get_kind();
        sorts.push_back(s);
      }
      res = _run(kind, sorts);
      break;
    }

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

    case SORT_SEQ:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_SEQ) != theories.end())
          << "solver does not support theory of sequences";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(2, n_tokens, kind);
      res =
          _run(kind, {d_smgr.get_untraced_sort(untrace_str_to_id(tokens[1]))});
      break;

    case SORT_SET:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_SET) != theories.end())
          << "solver does not support theory of sets";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(2, n_tokens, kind);
      res =
          _run(kind, {d_smgr.get_untraced_sort(untrace_str_to_id(tokens[1]))});
      break;

    case SORT_STRING:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_STRING) != theories.end())
          << "solver does not support theory of strings";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
      res = _run(kind);
      break;

    default: MURXLA_CHECK_TRACE(false) << "unknown sort kind " << tokens[0];
  }
  return res;
}

std::vector<uint64_t>
ActionMkSort::_run(SortKind kind)
{
  MURXLA_TRACE << get_kind() << " " << kind;
  Sort res = d_solver.mk_sort(kind);
  d_smgr.add_sort(res, kind);
  check_sort(res);
  MURXLA_TRACE_RETURN << res;
  return {res->get_id()};
}

std::vector<uint64_t>
ActionMkSort::_run(SortKind kind, uint32_t bw)
{
  MURXLA_TRACE << get_kind() << " " << kind << " " << bw;
  assert(kind == SORT_BV);
  Sort res = d_solver.mk_sort(kind, bw);
  MURXLA_TEST(res->get_bv_size() == bw);
  d_smgr.add_sort(res, kind);
  check_sort(res);
  MURXLA_TRACE_RETURN << res;
  return {res->get_id()};
}

std::vector<uint64_t>
ActionMkSort::_run(SortKind kind, uint32_t ew, uint32_t sw)
{
  MURXLA_TRACE << get_kind() << " " << kind << " " << ew << " " << sw;
  assert(kind == SORT_FP);
  Sort res = d_solver.mk_sort(kind, ew, sw);
  MURXLA_TEST(res->get_fp_exp_size() == ew);
  MURXLA_TEST(res->get_fp_sig_size() == sw);
  d_smgr.add_sort(res, kind);
  check_sort(res);
  MURXLA_TRACE_RETURN << res;
  return {res->get_id()};
}

std::vector<uint64_t>
ActionMkSort::_run(SortKind kind, const std::vector<Sort>& sorts)
{
  MURXLA_TRACE << get_kind() << " " << kind << sorts;
  assert(sorts.size() > 1);
  Sort res = d_solver.mk_sort(kind, sorts);
  res->set_sorts(sorts);
  d_smgr.add_sort(res, kind);
  check_sort(res);
  MURXLA_TEST(res->get_sorts().size() == sorts.size());
  MURXLA_TRACE_RETURN << res;
  return {res->get_id()};
}

std::vector<uint64_t>
ActionMkSort::_run(SortKind kind,
                   const std::vector<std::string>& dt_names,
                   const std::vector<std::vector<Sort>>& param_sorts,
                   std::vector<AbsSort::DatatypeConstructorMap>& constructors)
{
  size_t n_dt_sorts = dt_names.size();

  assert(n_dt_sorts == param_sorts.size());
  assert(n_dt_sorts == constructors.size());

  std::stringstream ss;
  ss << " " << n_dt_sorts;

  for (size_t i = 0; i < n_dt_sorts; ++i)
  {
    ss << " \"" << dt_names[i] << "\" " << param_sorts[i].size();
    for (const Sort& s : param_sorts[i])
    {
      ss << " " << s;
    }
    ss << " " << constructors[i].size();
    for (const auto& c : constructors[i])
    {
      const auto& cname = c.first;
      const auto& sels  = c.second;
      ss << " \"" << cname << "\" " << sels.size();
      for (const auto& s : sels)
      {
        const auto& sname = s.first;
        const auto& ssort = s.second;
        ss << " \"" << sname << "\" " << ssort;
      }
    }
  }
  MURXLA_TRACE << get_kind() << " " << kind << ss.str();
  std::vector<Sort> res_sorts =
      d_solver.mk_sort(kind, dt_names, param_sorts, constructors);

  std::unordered_map<std::string, Sort> symbol_to_dt_sort;
  for (size_t i = 0; i < n_dt_sorts; ++i)
  {
    /* add to map from DT sort name to sort for updating unresolved sorts */
    symbol_to_dt_sort[dt_names[i]] = res_sorts[i];
    /* add sort */
    res_sorts[i]->set_sorts(param_sorts[i]);
    res_sorts[i]->set_dt_ctors(constructors[i]);
    d_smgr.add_sort(res_sorts[i],
                    kind,
                    param_sorts[i].size() > 0,
                    res_sorts[i]->is_dt_well_founded());
  }
  for (size_t i = 0; i < n_dt_sorts; ++i)
  {
    /* add back reference to DT sort for param sorts */
    for (auto& p : param_sorts[i])
    {
      p->set_sorts({res_sorts[i]});
    }

    /* update unresolved sorts */
    for (auto& c : res_sorts[i]->get_dt_ctors())
    {
      auto& sels = c.second;
      for (auto& s : sels)
      {
        Sort& ssort = s.second;
        if (ssort && ssort->is_unresolved_sort())
        {
          UnresolvedSort* usort = dynamic_cast<UnresolvedSort*>(ssort.get());
          const std::string& symbol = usort->get_symbol();
          auto it = symbol_to_dt_sort.find(symbol);
          assert(it != symbol_to_dt_sort.end());
          ssort = it->second;
          if (ssort->is_dt_parametric() && !ssort->is_dt_instantiated())
          {
            /* we have to instantiate and cache the instantiated parametric
             * unresolved sort */
            const auto& inst_sorts = usort->get_sorts();
            assert(!inst_sorts.empty());
            Sort inst_ssort = d_solver.instantiate_sort(ssort, inst_sorts);
            inst_ssort->set_dt_is_instantiated(true);
            inst_ssort->set_dt_ctors(
                ssort->instantiate_dt_param_sort(inst_sorts));
            inst_ssort->set_sorts(inst_sorts);
            d_smgr.add_sort(inst_ssort,
                            ssort->get_kind(),
                            false,
                            inst_ssort->is_dt_well_founded());
            ssort = inst_ssort;
          }
        }
      }
    }
    /* check sort */
    check_sort(res_sorts[i], dt_names[i]);
  }
  MURXLA_TRACE_RETURN << res_sorts;
  std::vector<uint64_t> res(res_sorts.size());
  std::transform(
      res_sorts.begin(), res_sorts.end(), res.begin(), [](const auto& sort) {
        return sort->get_id();
      });
  return res;
}

void
ActionMkSort::check_sort(Sort sort, const std::string& name) const
{
  if (d_rng.pick_with_prob(990)) return;

  d_solver.check_sort(sort);

  MURXLA_TEST(sort->is_dt());
  MURXLA_TEST(sort->get_sorts().size() == 0 || sort->is_dt_parametric());
  MURXLA_TEST(sort->get_dt_name() == name);

  uint32_t n_cons = sort->get_dt_num_cons();
  auto cons_names = sort->get_dt_cons_names();
  auto ctors      = sort->get_dt_ctors();
  MURXLA_TEST(n_cons == cons_names.size());
  for (const auto& n : cons_names)
  {
    MURXLA_TEST(ctors.find(n) != ctors.end());
    uint32_t n_sels = sort->get_dt_cons_num_sels(n);
    auto sel_names  = sort->get_dt_cons_sel_names(n);
    MURXLA_TEST(n_sels == sel_names.size());
    for (const auto& p : ctors.at(n))
    {
      MURXLA_TEST(std::find(sel_names.begin(), sel_names.end(), p.first)
                  != sel_names.end());
    }
  }
}

void
ActionMkSort::check_sort(Sort sort) const
{
  if (d_rng.pick_with_prob(990)) return;
  d_solver.check_sort(sort);
}

/* -------------------------------------------------------------------------- */

bool
ActionMkTerm::run(Op::Kind kind)
{
  assert(kind != Op::UNDEFINED);

  Op& op = d_smgr.get_op(kind);
  assert(op.d_kind != Op::UNDEFINED);
  int32_t arity      = op.d_arity;
  uint32_t n_indices = op.d_nidxs;

  SortKind sort_kind     = SORT_ANY;
  SortKindSet sort_kinds = op.d_sort_kinds;
  if (sort_kinds.size() == 1)
  {
    sort_kind = *sort_kinds.begin();
  }

  ++d_smgr.d_mbt_stats->d_ops[op.d_id];

  if (kind == Op::DT_APPLY_CONS)
  {
    assert(!n_indices);
    if (!d_smgr.has_term(SORT_DT)) return false;
    Sort dt_sort           = d_smgr.pick_sort(SORT_DT);
    const auto& cons_names = dt_sort->get_dt_ctor_names();
    const std::string& ctor =
        d_rng.pick_from_set<std::vector<std::string>, std::string>(cons_names);
    const auto& sel_names = dt_sort->get_dt_sel_names(ctor);
    std::vector<Term> args;
    for (const auto& sel : sel_names)
    {
      Sort codomain_sort = dt_sort->get_dt_sel_sort(dt_sort, ctor, sel);
      if (!d_smgr.has_term(codomain_sort)) return false;
      args.push_back(d_smgr.pick_term(codomain_sort));
    }
    assert(sort_kind != SORT_ANY);
    _run(kind, sort_kind, dt_sort, {ctor}, args);
  }
  else if (kind == Op::DT_APPLY_SEL)
  {
    assert(!n_indices);
    if (!d_smgr.has_term(SORT_DT)) return false;
    Term arg               = d_smgr.pick_term(SORT_DT);
    Sort dt_sort           = arg->get_sort();
    const auto& cons_names = dt_sort->get_dt_ctor_names();
    const std::string& ctor =
        d_rng.pick_from_set<std::vector<std::string>, std::string>(cons_names);
    const auto& sel_names = dt_sort->get_dt_sel_names(ctor);
    if (sel_names.empty()) return false;
    const std::string& sel =
        d_rng.pick_from_set<std::vector<std::string>, std::string>(sel_names);
    Sort codomain_sort = dt_sort->get_dt_sel_sort(dt_sort, ctor, sel);
    sort_kind          = codomain_sort->get_kind();
    assert(sort_kind != SORT_ANY);
    _run(kind, sort_kind, {ctor, sel}, {arg});
  }
  else if (kind == Op::DT_APPLY_TESTER)
  {
    assert(!n_indices);
    if (!d_smgr.has_term(SORT_DT)) return false;
    Term arg               = d_smgr.pick_term(SORT_DT);
    Sort dt_sort           = arg->get_sort();
    const auto& cons_names = dt_sort->get_dt_ctor_names();
    const std::string& ctor =
        d_rng.pick_from_set<std::vector<std::string>, std::string>(cons_names);
    assert(sort_kind != SORT_ANY);
    _run(kind, sort_kind, {ctor}, {arg});
  }
  else if (kind == Op::DT_APPLY_UPDATER)
  {
    assert(!n_indices);
    if (!d_smgr.has_term(SORT_DT)) return false;
    std::vector<Term> args;
    args.push_back(d_smgr.pick_term(SORT_DT));
    Sort dt_sort           = args[0]->get_sort();
    const auto& cons_names = dt_sort->get_dt_ctor_names();
    const std::string& ctor =
        d_rng.pick_from_set<std::vector<std::string>, std::string>(cons_names);
    const auto& sel_names = dt_sort->get_dt_sel_names(ctor);
    if (sel_names.empty()) return false;
    const std::string& sel =
        d_rng.pick_from_set<std::vector<std::string>, std::string>(sel_names);
    Sort codomain_sort = dt_sort->get_dt_sel_sort(dt_sort, ctor, sel);
    if (!d_smgr.has_term(codomain_sort)) return false;
    args.push_back(d_smgr.pick_term(codomain_sort));
    _run(kind, sort_kind, {ctor, sel}, args);
  }
  else
  {
    std::vector<Term> args;
    std::vector<uint32_t> indices;

    if (arity == MURXLA_MK_TERM_N_ARGS || arity == MURXLA_MK_TERM_N_ARGS_BIN)
    {
      uint32_t min_arity = MURXLA_MK_TERM_N_ARGS_MIN(arity);
      arity              = d_rng.pick_weighted<uint32_t>(
          d_n_args_weights.begin(), d_n_args_weights.end() - (min_arity - 1));
      arity += min_arity;
    }

    /* Pick term arguments. */
    if (kind == Op::BV_CONCAT)
    {
      assert(!n_indices);
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
      assert(!n_indices);
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
      assert(!n_indices);
      Sort array_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
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
      assert(!n_indices);
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

      args.push_back(mk_store(array_sort, index_sort, element_sort));
      args.push_back(d_smgr.pick_term(index_sort));
      args.push_back(d_smgr.pick_term(element_sort));
    }
    else if (kind == Op::FP_FP)
    {
      assert(!n_indices);
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
      assert(n_indices == 2);
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
      indices.push_back(ew);
      indices.push_back(sw);
    }
    else if (kind == Op::FORALL || kind == Op::EXISTS)
    {
      assert(!n_indices);
      assert(d_smgr.has_var());
      assert(d_smgr.has_quant_body());
      Term body = d_smgr.pick_quant_body();
      uint32_t n_vars = d_rng.pick<uint32_t>(1, d_smgr.get_num_vars());
      if (n_vars > 1)
      {
        std::vector<Term> vars = d_smgr.pick_vars(n_vars);
        args.insert(args.begin(), vars.begin(), vars.end());
      }
      else
      {
        args.push_back(d_smgr.pick_var());
      }
      args.push_back(body);
    }
    else if (d_smgr.d_arith_linear
             && (kind == Op::INT_MUL || kind == Op::REAL_MUL))
    {
      assert(!n_indices);
      assert(d_smgr.has_sort(sort_kind));
      Sort sort = d_smgr.pick_sort(sort_kind);
      if (!d_smgr.has_value(sort)) return false;
      bool picked_non_const = false;
      /* pick arguments */
      for (int32_t i = 0; i < arity; ++i)
      {
        assert(d_smgr.has_term(sort));
        if (picked_non_const)
        {
          args.push_back(d_smgr.pick_value(sort));
          assert(args.back()->get_leaf_kind() == AbsTerm::LeafKind::VALUE);
        }
        else
        {
          args.push_back(d_smgr.pick_term(sort));
          if (args.back()->get_leaf_kind() != AbsTerm::LeafKind::VALUE)
            picked_non_const = true;
        }
      }
    }
    else if (kind == Op::RE_RANGE)
    {
      assert(!n_indices);
      if (!d_smgr.has_string_char_value()) return false;
      args.push_back(d_smgr.pick_string_char_value());
      args.push_back(d_smgr.pick_string_char_value());
    }
    else if (kind == Op::UF_APPLY)
    {
      assert(!n_indices);
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
    else if (kind == Op::SEQ_NTH)
    {
      assert(!n_indices);
      Sort seq_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      const std::vector<Sort>& sorts = seq_sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      assert(d_smgr.has_term(seq_sort));
      assert(d_smgr.has_term(SORT_INT));
      args.push_back(d_smgr.pick_term(seq_sort));
      args.push_back(d_smgr.pick_term(SORT_INT));
      sort_kind = element_sort->get_kind();
    }
    else if (kind == Op::SEQ_UNIT)
    {
      assert(!n_indices);
      SortKindSet exclude_sorts =
          d_solver.get_unsupported_seq_element_sort_kinds();
      if (!d_smgr.has_sort_excluding(exclude_sorts)) return false;
      Sort element_sort = d_smgr.pick_sort_excluding(exclude_sorts);
      assert(exclude_sorts.find(element_sort->get_kind())
             == exclude_sorts.end());
      args.push_back(d_smgr.pick_term(element_sort));
    }
    else if (kind == Op::BAG_CHOOSE || kind == Op::SET_CHOOSE)
    {
      assert(!n_indices);
      Sort sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      const std::vector<Sort>& sorts = sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      args.push_back(d_smgr.pick_term(sort));
      sort_kind = element_sort->get_kind();
    }
    else if (kind == Op::SET_SINGLETON)
    {
      assert(!n_indices);
      SortKindSet exclude_sorts =
          d_solver.get_unsupported_set_element_sort_kinds();
      if (!d_smgr.has_sort_excluding(exclude_sorts)) return false;
      Sort element_sort = d_smgr.pick_sort_excluding(exclude_sorts);
      assert(exclude_sorts.find(element_sort->get_kind())
             == exclude_sorts.end());
      args.push_back(d_smgr.pick_term(element_sort));
    }
    else if (kind == Op::SET_INSERT)
    {
      assert(!n_indices);
      Sort set_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      const std::vector<Sort>& sorts = set_sort->get_sorts();
      assert(sorts.size() == 1);
      assert(d_smgr.has_term(set_sort));
      Sort element_sort = sorts[0];
      if (!d_smgr.has_term(element_sort)) return false;
      args.push_back(d_smgr.pick_term(set_sort));
      assert(sort_kind != SORT_ANY);
      for (int32_t i = 0; i < arity; ++i)
      {
        args.push_back(d_smgr.pick_term(element_sort));
      }
    }
    else if (kind == Op::SET_MEMBER)
    {
      assert(!n_indices);
      Sort set_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      const std::vector<Sort>& sorts = set_sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      if (!d_smgr.has_term(element_sort)) return false;
      args.push_back(d_smgr.pick_term(set_sort));
      args.push_back(d_smgr.pick_term(element_sort));
    }
    else if (kind == Op::SET_COMPREHENSION)
    {
      assert(!n_indices);
      if (!d_smgr.has_var()) return false;
      if (!d_smgr.has_quant_term()) return false;
      if (!d_smgr.has_quant_body()) return false;
      Term body = d_smgr.pick_quant_body();
      Term term = d_smgr.pick_quant_term();
      args.push_back(body);
      args.push_back(term);
      uint32_t n_vars = d_rng.pick<uint32_t>(1, d_smgr.get_num_vars());
      if (n_vars > 1)
      {
        args.push_back(d_smgr.pick_var());
      }
      else
      {
        std::vector<Term> vars = d_smgr.pick_vars(n_vars);
        args.insert(args.end(), vars.begin(), vars.end());
      }
    }
    else if (kind == Op::BAG_COUNT)
    {
      assert(!n_indices);
      Sort bag_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      const std::vector<Sort>& sorts = bag_sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      if (!d_smgr.has_term(element_sort)) return false;
      args.push_back(d_smgr.pick_term(bag_sort));
      args.push_back(d_smgr.pick_term(element_sort));
    }
    else if (kind == Op::BAG_MAP)
    {
      assert(!n_indices);
      Sort bag_sort = d_smgr.pick_sort(op.get_arg_sort_kind(0));
      const std::vector<Sort>& sorts = bag_sort->get_sorts();
      assert(sorts.size() == 1);
      Sort element_sort = sorts[0];
      if (!d_smgr.has_term(element_sort)) return false;
      if (!d_smgr.has_fun({element_sort})) return false;
      args.push_back(d_smgr.pick_term(bag_sort));
      args.push_back(d_smgr.pick_fun({element_sort}));
    }
    else if (kind == Op::BAG_MAKE)
    {
      assert(!n_indices);
      const auto& exclude_sorts =
          d_solver.get_unsupported_bag_element_sort_kinds();
      if (!d_smgr.has_term(SORT_INT)) return false;
      if (!d_smgr.has_sort_excluding(exclude_sorts)) return false;
      Sort element_sort = d_smgr.pick_sort_excluding(exclude_sorts);
      args.push_back(d_smgr.pick_term(element_sort));
      args.push_back(d_smgr.pick_term(SORT_INT));
    }
    else
    {
      /* Always pick the same sort for a given sort kind. */
      std::unordered_map<SortKind, Sort> sorts;
      for (int32_t i = 0; i < arity; ++i)
      {
        SortKindSet skinds = op.get_arg_sort_kind(i);
        assert(d_smgr.has_term(skinds));
        std::unordered_map<SortKind, Sort>::iterator it;
        Sort sort;
        /* We have to ensure that we pick the same sort for all arguments
         * if more than one sort kind is allowed (can only be the case for
         * operators that allow SORT_ANY). */
        SortKind skind = SORT_ANY, skind_map = SORT_ANY;
        if (skinds.size() == 1)
        {
          skind     = *skinds.begin();
          skind_map = skind;
        }
        it = sorts.find(skind_map);
        if (it == sorts.end())
        {
          if (skind == SORT_ANY) skind = d_smgr.pick_sort_kind(skinds);
          sort = d_smgr.pick_sort(skind);
          sorts.emplace(skind_map, sort);
        }
        else
        {
          sort = it->second;
        }
        it = sorts.find(skind_map);
        assert(it != sorts.end());
        assert(d_smgr.has_term(sort));
        args.push_back(d_smgr.pick_term(sort));
      }

      /* Numeral arguments for indexed operators. */
      if (n_indices)
      {
        if (kind == Op::BV_EXTRACT)
        {
          assert(n_indices == 2);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_bv());
          assert(sort_kind == SORT_BV);
          uint32_t bw = args[0]->get_sort()->get_bv_size();
          indices.push_back(d_rng.pick<uint32_t>(0, bw - 1));      // high
          indices.push_back(d_rng.pick<uint32_t>(0, indices[0]));  // low
        }
        else if (kind == Op::BV_REPEAT)
        {
          assert(n_indices == 1);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_bv());
          assert(sort_kind == SORT_BV);
          uint32_t bw = args[0]->get_sort()->get_bv_size();
          indices.push_back(d_rng.pick<uint32_t>(
              1, std::max<uint32_t>(1, MURXLA_BW_MAX / bw)));
        }
        else if (kind == Op::BV_ROTATE_LEFT || kind == Op::BV_ROTATE_RIGHT)
        {
          assert(n_indices == 1);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_bv());
          assert(sort_kind == SORT_BV);
          uint32_t bw = args[0]->get_sort()->get_bv_size();
          indices.push_back(d_rng.pick<uint32_t>(0, bw));
        }
        else if (kind == Op::BV_SIGN_EXTEND || kind == Op::BV_ZERO_EXTEND)
        {
          assert(n_indices == 1);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_bv());
          assert(sort_kind == SORT_BV);
          uint32_t bw = args[0]->get_sort()->get_bv_size();
          indices.push_back(d_rng.pick<uint32_t>(0, MURXLA_BW_MAX - bw));
        }
        else if (kind == Op::FP_TO_FP_FROM_SBV || kind == Op::FP_TO_FP_FROM_UBV)
        {
          assert(n_indices == 2);
          assert(args.size() == 2);
          assert(args[0]->get_sort()->is_rm());
          assert(args[1]->get_sort()->is_bv());
          assert(sort_kind == SORT_FP);
          /* term has FP sort, pick sort */
          if (!d_smgr.has_sort(SORT_FP)) return false;
          Sort sort = d_smgr.pick_sort(SORT_FP, false);
          indices.push_back(sort->get_fp_exp_size());
          indices.push_back(sort->get_fp_sig_size());
        }
        else if (kind == Op::FP_TO_FP_FROM_FP)
        {
          assert(n_indices == 2);
          assert(args.size() == 2);
          assert(args[0]->get_sort()->is_rm());
          assert(args[1]->get_sort()->is_fp());
          assert(sort_kind == SORT_FP);
          /* term has new FP sort, pick sort */
          if (!d_smgr.has_sort(SORT_FP)) return false;
          Sort sort = d_smgr.pick_sort(SORT_FP, false);
          indices.push_back(sort->get_fp_exp_size());
          indices.push_back(sort->get_fp_sig_size());
        }
        else if (kind == Op::FP_TO_SBV || kind == Op::FP_TO_UBV)
        {
          assert(n_indices == 1);
          assert(args.size() == 2);
          assert(args[0]->get_sort()->is_rm());
          assert(args[1]->get_sort()->is_fp());
          assert(sort_kind == SORT_BV);
          /* term has BV sort, pick bit-width */
          indices.push_back(
              d_rng.pick<uint32_t>(1, std::max<uint32_t>(1, MURXLA_BW_MAX)));
        }
        else if (kind == Op::FP_TO_FP_FROM_REAL)
        {
          assert(n_indices == 2);
          assert(args.size() == 2);
          assert(args[0]->get_sort()->is_rm());
          assert(args[1]->get_sort()->is_real());
          assert(sort_kind == SORT_FP);
          /* term has FP sort, pick sort */
          if (!d_smgr.has_sort(SORT_FP)) return false;
          Sort sort = d_smgr.pick_sort(SORT_FP, false);
          indices.push_back(sort->get_fp_exp_size());
          indices.push_back(sort->get_fp_sig_size());
        }
        else if (kind == Op::INT_IS_DIV)
        {
          assert(n_indices == 1);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_int());
          assert(sort_kind == SORT_BOOL);
          indices.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
        }
        else if (kind == Op::RE_LOOP)
        {
          assert(n_indices == 2);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_reglan());
          assert(sort_kind == SORT_REGLAN);
          indices.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
          indices.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
        }
        else if (kind == Op::RE_POW)
        {
          assert(n_indices == 1);
          assert(args.size() == 1);
          assert(args[0]->get_sort()->is_reglan());
          assert(sort_kind == SORT_REGLAN);
          indices.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
        }
        else
        {
          /* solver-specific op */
          for (uint32_t i = 0; i < n_indices; ++i)
          {
            // Note: We select a generic parameter value > 0. If solver expects
            //       a specific value range for param for given solver-specific
            //       operator, modify value accordingly in Solver::mk_term.
            //       See utils::uint32_to_value_in_range().
            indices.push_back(d_rng.pick<uint32_t>(1, UINT32_MAX));
          }
        }
      }
    }

    /* Every OP with return sort SORT_ANY needs to set the kind above. */
    assert(sort_kind != SORT_ANY);
    _run(kind, sort_kind, args, indices);
  }

  ++d_smgr.d_mbt_stats->d_ops_ok[op.d_id];

  return true;
}

ActionMkTerm::ActionMkTerm(SolverManager& smgr) : Action(smgr, MK_TERM, ID)
{
  for (uint32_t i = 0; i < MURXLA_MK_TERM_N_ARGS_MAX; ++i)
  {
    uint32_t n = MURXLA_MK_TERM_N_ARGS_MAX - i;
    d_n_args_weights.push_back(n * n);
  }
}

bool
ActionMkTerm::run()
{
  /* Op is only picked if there exist terms that can be used as operands. */
  Op::Kind kind = d_smgr.pick_op_kind();
  assert(d_solver.is_initialized());
  assert(d_smgr.get_enabled_theories().find(THEORY_BOOL)
         != d_smgr.get_enabled_theories().end());
  assert(d_smgr.has_term());

  assert(!d_smgr.d_arith_linear || kind != Op::INT_MOD);
  assert(!d_smgr.d_arith_linear || kind != Op::INT_DIV);
  assert(!d_smgr.d_arith_linear || kind != Op::REAL_DIV);
  if (kind == Op::UNDEFINED) return false;

  if (kind == Op::DT_MATCH)
  {
    if (!d_smgr.has_term(SORT_DT)) return false;

    /* DT_MATCH is a weird special case. We need variables (of a specific sort)
     * for each selector of a constructor we create patterns for, and a
     * quantified term that possibly uses these variables. We don't rely on
     * Murxla to generate these variables and terms beforehand but generate
     * them here on demand. */

    Op& op = d_smgr.get_op(kind);
    assert(op.d_kind != Op::UNDEFINED);
    assert(!op.d_nidxs);

    Term dt_term = d_smgr.pick_term(SORT_DT);
    Sort dt_sort = dt_term->get_sort();

    std::vector<Term> args;
    args.push_back(dt_term);

    const auto& cons_names = dt_sort->get_dt_ctor_names();
    auto exclude_sorts     = d_solver.get_unsupported_dt_match_sort_kinds();
    /* Pick sort with terms. */
    SortKind sort_kind = d_smgr.pick_sort_kind_excluding(exclude_sorts);
    Sort sort          = d_smgr.pick_sort(sort_kind);

    ActionMkVar mkvar(d_smgr);  // to create variables on demand

    /* True if all constructors are to be matched. */
    bool match_all = d_rng.pick_with_prob(700);
    /* True if at least one match case is a variable pattern. */
    bool match_var = false;

    for (const auto& ctor : cons_names)
    {
      if (!match_all && d_rng.flip_coin()) continue;

      const auto& sel_names = dt_sort->get_dt_sel_names(ctor);
      std::vector<Term> match_case_args;
      std::vector<std::string> match_case_ctor;
      uint32_t match_case_id;
      Op::Kind match_case_kind;

      /* Pick variable pattern with 10% probability. */
      if (d_rng.pick_with_prob(10))
      {
        uint32_t var_id = mkvar._run(dt_sort, d_smgr.pick_symbol())[0];
        match_case_args.push_back(d_smgr.get_term(var_id));
        match_case_kind = Op::DT_MATCH_BIND_CASE;
        match_var       = true;
      }
      /* Else create regular pattern. */
      else
      {
        match_case_ctor.push_back(ctor);

        if (!sel_names.empty())
        {
          for (const auto& sel : sel_names)
          {
            /* Create variable of selector codomain sort for each selector. */
            uint32_t var_id =
                mkvar._run(dt_sort->get_dt_sel_sort(dt_sort, ctor, sel),
                           d_smgr.pick_symbol())[0];
            match_case_args.push_back(d_smgr.get_term(var_id));
          }
          /* Create some terms that (possibly) use these variables. */
          uint32_t n_terms_created = 0;
          while ((!d_smgr.has_quant_term(sort) && !d_smgr.has_term(sort))
                 || n_terms_created < MURXLA_MIN_N_QUANT_TERMS)
          {
            /* We only create op terms here (no consts, values, vars). The
             * former two wouldn't be quantified terms that use the created vars
             * anyways, and we have already picked a sort with terms, so we do
             * have terms of that sort in the term db. We may consider to create
             * vars here in the future. */
            Op::Kind op_kind = d_smgr.pick_op_kind(true, sort_kind);
            if (op_kind == Op::DT_MATCH) continue;
            if (run(op_kind)) n_terms_created += 1;
          }
          match_case_kind = Op::DT_MATCH_BIND_CASE;
        }
        else
        {
          match_case_kind = Op::DT_MATCH_CASE;
        }
      }
      match_case_args.push_back(d_smgr.pick_term(sort));
      match_case_id = _run(match_case_kind,
                           sort_kind,
                           dt_sort,
                           match_case_ctor,
                           match_case_args)[0];
      args.push_back(d_smgr.get_term(match_case_id));
    }

    /* We need at least one variable pattern if not all cases are matched. */
    if (!match_all && !match_var)
    {
      uint32_t var_id = mkvar._run(dt_sort, d_smgr.pick_symbol())[0];
      std::vector<Term> match_case_args{d_smgr.get_term(var_id),
                                        d_smgr.pick_term(sort)};
      uint32_t match_case_id = _run(
          Op::DT_MATCH_BIND_CASE, sort_kind, dt_sort, {}, match_case_args)[0];
      args.push_back(d_smgr.get_term(match_case_id));
    }

    assert(sort_kind != SORT_ANY);
    _run(kind, sort_kind, args, {});

    ++d_smgr.d_mbt_stats->d_ops[op.d_id];
    return true;
  }
  return run(kind);
}

std::vector<uint64_t>
ActionMkTerm::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS_MIN(
      3, " (operator kind, sort id, number of arguments) ", tokens.size());

  std::vector<Term> args;
  std::vector<uint32_t> indices;
  uint32_t n_tokens  = tokens.size();
  Op::Kind op_kind   = tokens[0];
  SortKind sort_kind = get_sort_kind_from_str(tokens[1]);
  Sort sort;

  uint32_t n_args, n_str_args = 0, idx = 3;
  std::vector<std::string> str_args;

  if (op_kind == Op::DT_APPLY_SEL || op_kind == Op::DT_APPLY_TESTER
      || op_kind == Op::DT_APPLY_UPDATER)
  {
    n_str_args = str_to_uint32(tokens[2]);
    for (uint32_t i = 0; i < n_str_args; ++i, ++idx)
    {
      str_args.push_back(str_to_str(tokens[idx]));
    }
    n_args = str_to_uint32(tokens[idx++]);
  }
  else if (op_kind == Op::DT_APPLY_CONS || op_kind == Op::DT_MATCH_CASE
           || op_kind == Op::DT_MATCH_BIND_CASE)
  {
    uint32_t id = untrace_str_to_id(tokens[2]);
    sort        = d_smgr.get_untraced_sort(id);
    n_str_args  = str_to_uint32(tokens[idx++]);
    for (uint32_t i = 0; i < n_str_args; ++i, ++idx)
    {
      str_args.push_back(str_to_str(tokens[idx]));
    }
    n_args = str_to_uint32(tokens[idx++]);
  }
  else
  {
    n_args = str_to_uint32(tokens[2]);
  }

  MURXLA_CHECK_TRACE(idx + n_args <= n_tokens)
      << "expected " << n_args << " term argument(s), got " << n_tokens - 3;

  for (uint32_t i = 0; i < n_args; ++i, ++idx)
  {
    uint32_t id = untrace_str_to_id(tokens[idx]);
    Term t      = d_smgr.get_untraced_term(id);
    MURXLA_CHECK_TRACE_TERM(t, id);
    args.push_back(t);
  }

  if (idx < tokens.size())
  {
    uint32_t n_indices = str_to_uint32(tokens[idx++]);
    MURXLA_CHECK_TRACE(idx + n_indices == n_tokens)
        << "expected " << n_args << " parameter(s) to create indexed term, got "
        << n_tokens - 3 - n_args;
    for (uint32_t i = 0; i < n_indices; ++i, ++idx)
    {
      uint32_t param = str_to_uint32(tokens[idx]);
      indices.push_back(param);
    }
  }

  if (op_kind == Op::DT_APPLY_SEL || op_kind == Op::DT_APPLY_TESTER
      || op_kind == Op::DT_APPLY_UPDATER)
  {
    return _run(op_kind, sort_kind, str_args, args);
  }

  if (op_kind == Op::DT_APPLY_CONS || op_kind == Op::DT_MATCH_CASE
      || op_kind == Op::DT_MATCH_BIND_CASE)
  {
    return _run(op_kind, sort_kind, sort, str_args, args);
  }

  return _run(op_kind, sort_kind, args, indices);
}

std::vector<uint64_t>
ActionMkTerm::_run(Op::Kind kind,
                   SortKind sort_kind,
                   std::vector<Term>& args,
                   const std::vector<uint32_t>& indices)
{
  std::stringstream trace_str;
  trace_str << " " << kind << " " << sort_kind;
  trace_str << " " << args.size() << args;
  if (indices.size())
  {
    trace_str << " " << indices.size() << indices;
  }
  MURXLA_TRACE << get_kind() << trace_str.str();

  std::vector<Term> bargs;
  /* Note: We pop the variable scopes in _run instead of run so that we
   *       correctly handle this case for untracing. */
  if (kind == Op::FORALL || kind == Op::EXISTS)
  {
    for (size_t i = 0, n = args.size() - 1; i < n; ++i)
    {
      d_smgr.remove_var(args[i]);
    }
  }
  else if (kind == Op::SET_COMPREHENSION)
  {
    for (size_t i = 2, n = args.size(); i < n; ++i)
    {
      d_smgr.remove_var(args[i]);
    }
  }

  Term res = d_solver.mk_term(kind, args, indices);

  if ((args.size() > 1 || (args.size() == 1 && !args[0]->equals(res)))
      && res->is_indexed() && indices.size())
  {
    /* We have to guard against the case where an op is rewritten to itself,
     * which can for example happen for a repeat operator with index 1.
     * We further have to perform these checks based on if 'res' is indexed and
     * indices.size() > 0. This is because res might not be indexed even if the
     * latter is true due to rewriting (e.g., a zero extend may be rewritten to
     * a concat) and vice versa (e.g., Bitwuzla rewrites operator fp to
     * to_fp from IEEE bit-vector). */
    MURXLA_TEST(indices.size());
    size_t n_idxs                        = res->get_num_indices();
    std::vector<std::string> res_indices = res->get_indices();
    MURXLA_TEST(n_idxs == res_indices.size());
    /* We can't check if the resulting indices match the given indices, due to
     * rewriting. This is only a problem when a solver does not create a node
     * as it was given, but returns its rewritten form. Which is the case for
     * Bitwuzla and Boolector (but not for cvc5). We therefore have to test
     * this in the solver implementation, if possible. */
  }

  d_smgr.add_term(res, sort_kind, args);
  Sort res_sort = res->get_sort();

  MURXLA_TRACE_RETURN << res << " " << res_sort;
  check_term(res);
  return {res->get_id(), res_sort->get_id()};
}

std::vector<uint64_t>
ActionMkTerm::_run(Op::Kind kind,
                   SortKind sort_kind,
                   const std::vector<std::string> str_args,
                   const std::vector<Term>& args)
{
  std::stringstream trace_str;
  trace_str << " " << kind << " " << sort_kind;
  trace_str << " " << str_args.size();
  for (const auto& s : str_args)
  {
    trace_str << " \"" << s << "\" ";
  }
  trace_str << " " << args.size() << args;
  MURXLA_TRACE << get_kind() << trace_str.str();

  Term res = d_solver.mk_term(kind, str_args, args);
  d_smgr.add_term(res, sort_kind, args);
  Sort res_sort = res->get_sort();

  MURXLA_TRACE_RETURN << res << " " << res_sort;
  check_term(res);
  return {res->get_id(), res_sort->get_id()};
}

std::vector<uint64_t>
ActionMkTerm::_run(Op::Kind kind,
                   SortKind sort_kind,
                   Sort sort,
                   const std::vector<std::string> str_args,
                   std::vector<Term>& args)
{
  std::stringstream trace_str;
  trace_str << " " << kind << " " << sort_kind << " " << sort;
  trace_str << " " << str_args.size();
  for (const auto& s : str_args)
  {
    trace_str << " \"" << s << "\" ";
  }
  trace_str << " " << args.size() << args;
  MURXLA_TRACE << get_kind() << trace_str.str();

  /* Note: We pop the variable scopes in _run instead of run so that we
   *       correctly handle this case for untracing. */
  if (kind == Op::DT_MATCH_BIND_CASE)
  {
    for (size_t i = 0, n = args.size() - 1; i < n; ++i)
    {
      d_smgr.remove_var(args[n - 1 - i]);
    }
  }

  Term res = d_solver.mk_term(kind, sort, str_args, args);
  /* We do not add match case terms since they are specifically created for
   * creating a match term and should not be used in any other terms. */
  d_smgr.add_term(res, sort_kind, args);
  Sort res_sort = res->get_sort();

  MURXLA_TRACE_RETURN << res << " " << res_sort;
  check_term(res);
  return {res->get_id(), res_sort->get_id()};
}

void
ActionMkTerm::check_term(Term term)
{
  if (d_rng.pick_with_prob(990)) return;

  /* check sort */
  Sort sort = term->get_sort();
  if (sort->is_array())
  {
    MURXLA_TEST(term->is_array());
    MURXLA_TEST(sort->get_array_index_sort() == term->get_array_index_sort());
    if (d_rng.pick_with_prob(500))
    {
      MURXLA_TEST(sort->get_array_element_sort()
                  == term->get_array_element_sort());
    }
    else
    {
      MURXLA_TEST(
          !(sort->get_array_element_sort() != term->get_array_element_sort()));
    }
  }
  else if (sort->is_bag())
  {
    MURXLA_TEST(term->is_bag());
    Sort elem_sort = sort->get_bag_element_sort();
    // we can't use operator== here since elem_sort is a sort returned by the
    // solver, thus is has kind SORT_ANY (and operator== checks for equality
    // of sort kind, too)
    MURXLA_TEST(elem_sort == nullptr
                || elem_sort->equals(sort->get_sorts()[0]));
  }
  else if (sort->is_bool())
  {
    MURXLA_TEST(term->is_bool());
  }
  else if (sort->is_bv())
  {
    MURXLA_TEST(term->is_bv());
    MURXLA_TEST(sort->get_bv_size() == term->get_bv_size());
  }
  else if (sort->is_dt())
  {
    MURXLA_TEST(term->is_dt());
  }
  else if (sort->is_fp())
  {
    MURXLA_TEST(term->is_fp());
    MURXLA_TEST(sort->get_fp_exp_size() == term->get_fp_exp_size());
    MURXLA_TEST(sort->get_fp_sig_size() == term->get_fp_sig_size());
  }
  else if (sort->is_fun())
  {
    MURXLA_TEST(term->is_fun());
    MURXLA_TEST(sort->get_fun_arity() == term->get_fun_arity());
    if (d_rng.pick_with_prob(500))
    {
      MURXLA_TEST(sort->get_fun_codomain_sort()
                  == term->get_fun_codomain_sort());
    }
    else
    {
      MURXLA_TEST(
          !(sort->get_fun_codomain_sort() != term->get_fun_codomain_sort()));
    }
    std::vector<Sort> domain_sorts_expected = sort->get_fun_domain_sorts();
    std::vector<Sort> domain_sorts          = term->get_fun_domain_sorts();
    MURXLA_TEST(domain_sorts_expected.size() == domain_sorts.size());
    for (size_t i = 0, n = domain_sorts_expected.size(); i < n; ++i)
    {
      if (d_rng.pick_with_prob(500))
      {
        MURXLA_TEST(domain_sorts_expected[i] == domain_sorts[i]);
      }
      else
      {
        MURXLA_TEST(!(domain_sorts_expected[i] != domain_sorts[i]));
      }
    }
  }
  else if (sort->is_int())
  {
    MURXLA_TEST(term->is_int());
  }
  else if (sort->is_real())
  {
    MURXLA_TEST(term->is_real());
  }
  else if (sort->is_rm())
  {
    MURXLA_TEST(term->is_rm());
  }
  else if (sort->is_string())
  {
    MURXLA_TEST(term->is_string());
  }
  else if (sort->is_reglan())
  {
    MURXLA_TEST(term->is_reglan());
  }
  else if (sort->is_seq())
  {
    MURXLA_TEST(term->is_seq());
    Sort elem_sort = sort->get_seq_element_sort();
    // we can't use operator== here since elem_sort is a sort returned by the
    // solver, thus is has kind SORT_ANY (and operator== checks for equality
    // of sort kind, too)
    MURXLA_TEST(elem_sort == nullptr
                || elem_sort->equals(sort->get_sorts()[0]));
  }
  else if (sort->is_set())
  {
    MURXLA_TEST(term->is_set());
    Sort elem_sort = sort->get_set_element_sort();
    // we can't use operator== here since elem_sort is a sort returned by the
    // solver, thus is has kind SORT_ANY (and operator== checks for equality
    // of sort kind, too)
    MURXLA_TEST(elem_sort == nullptr
                || elem_sort->equals(sort->get_sorts()[0]));
  }
  else
  {
    assert(false);
  }

  /* check term */
  MURXLA_TEST(term == term);
  MURXLA_TEST(!(term != term));
  MURXLA_TEST(!(term == Term()));
  MURXLA_TEST(term != Term());
  d_solver.check_term(term);
}

Term
ActionMkTerm::mk_store(const Sort& array_sort,
                       const Sort& index_sort,
                       const Sort& element_sort)
{
  size_t nstores =
      d_rng.flip_coin() ? 0 : d_rng.pick(1, MURXLA_MAX_STORE_CHAIN_LENGTH);
  Term result = d_smgr.pick_term(array_sort);

  Term index, element;
  for (size_t i = 0; i < nstores; ++i)
  {
    std::vector<Term> args;
    args.push_back(result);
    args.push_back(d_smgr.pick_term(index_sort));
    args.push_back(d_smgr.pick_term(element_sort));
    auto ret = _run(Op::ARRAY_STORE, SortKind::SORT_ARRAY, args, {});
    assert(ret.size() == 2);
    result = d_smgr.get_term(ret[0]);
  }

  return result;
}

/* -------------------------------------------------------------------------- */

bool
ActionMkConst::run(Sort sort)
{
  assert(d_solver.is_initialized());
  if (d_exclude_sort_kinds.find(sort->get_kind()) != d_exclude_sort_kinds.end())
  {
    return false;
  }
  std::string symbol = d_smgr.pick_symbol();
  _run(sort, symbol);
  return true;
}

bool
ActionMkConst::run()
{
  assert(d_solver.is_initialized());
  SortKindSet exclude(d_exclude_sort_kinds);
  /* Deemphasize picking of Boolean sort. */
  if (d_rng.pick_with_prob(800))
  {
    exclude.insert(SORT_BOOL);
  }
  if (!d_smgr.has_sort_excluding(exclude, false)) return false;
  Sort sort = d_smgr.pick_sort_excluding(exclude, false);
  return run(sort);
}

std::vector<uint64_t>
ActionMkConst::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
  Sort sort = d_smgr.get_untraced_sort(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
  std::string symbol = str_to_str(tokens[1]);
  return _run(sort, symbol);
}

std::vector<uint64_t>
ActionMkConst::_run(Sort sort, const std::string& symbol)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << symbol << "\"";
  Term res = d_solver.mk_const(sort, symbol);
  d_smgr.add_const(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  check_const(d_rng, res);
  return {res->get_id()};
}

void
ActionMkConst::check_const(RNGenerator& rng, Term term)
{
  if (rng.pick_with_prob(990)) return;

  ActionMkTerm mkterm(d_smgr);
  mkterm.check_term(term);
  MURXLA_TEST(term->is_const());
  MURXLA_TEST(!term->is_value());
  MURXLA_TEST(!term->is_var());
}

/* -------------------------------------------------------------------------- */

bool
ActionMkVar::run()
{
  assert(d_solver.is_initialized());
  SortKindSet exclude_sorts = d_solver.get_unsupported_var_sort_kinds();
  /* Deemphasize picking of Boolean sort. */
  if (d_rng.pick_with_prob(800))
  {
    exclude_sorts.insert(SORT_BOOL);
  }

  /* Pick sort of const. */
  if (!d_smgr.has_sort_excluding(exclude_sorts, false)) return false;
  Sort sort          = d_smgr.pick_sort_excluding(exclude_sorts, false);
  std::string symbol = d_smgr.pick_symbol();
  /* Create var. */
  _run(sort, symbol);
  return true;
}

std::vector<uint64_t>
ActionMkVar::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
  Sort sort = d_smgr.get_untraced_sort(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
  std::string symbol = str_to_str(tokens[1]);
  return _run(sort, symbol);
}

std::vector<uint64_t>
ActionMkVar::_run(Sort sort, const std::string& symbol)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << symbol << "\"";
  Term res = d_solver.mk_var(sort, symbol);
  d_smgr.add_var(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  check_variable(d_rng, res);
  return {res->get_id()};
}

void
ActionMkVar::check_variable(RNGenerator& rng, Term term)
{
  if (rng.pick_with_prob(999)) return;

  ActionMkTerm mkterm(d_smgr);
  mkterm.check_term(term);

  MURXLA_TEST(term->is_var());
  MURXLA_TEST(!term->is_value());
  MURXLA_TEST(!term->is_const());
}

/* -------------------------------------------------------------------------- */

bool
ActionMkValue::run(Sort sort)
{
  assert(d_solver.is_initialized());

  SortKind sort_kind = sort->get_kind();
  if (d_exclude_sort_kinds.find(sort_kind) != d_exclude_sort_kinds.end())
  {
    return false;
  }

  /* Pick value. */
  switch (sort_kind)
  {
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

    default: assert(false);
  }

  return true;
}

bool
ActionMkValue::run()
{
  SortKindSet exclude(d_exclude_sort_kinds);
  /* Deemphasize picking of Boolean sort. */
  if (d_rng.pick_with_prob(800))
  {
    exclude.insert(SORT_BOOL);
  }
  /* Pick sort of value. */
  if (!d_smgr.has_sort_excluding(exclude)) return false;
  Sort sort = d_smgr.pick_sort_excluding(exclude);
  return run(sort);
}

std::vector<uint64_t>
ActionMkValue::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);

  uint64_t res = 0;
  Sort sort    = d_smgr.get_untraced_sort(untrace_str_to_id(tokens[0]));
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
  check_value(res);
  return res->get_id();
}

uint64_t
ActionMkValue::_run(Sort sort, const std::string& val)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
  Term res;
  res = d_solver.mk_value(sort, val);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  check_value(res);
  return res->get_id();
}

uint64_t
ActionMkValue::_run(Sort sort, const std::string& val, size_t len)
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
  check_value(res);
  return res->get_id();
}

uint64_t
ActionMkValue::_run(Sort sort, const std::string& v0, const std::string& v1)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << v0 << "\""
               << " \"" << v1 << "\"";
  Term res = d_solver.mk_value(sort, v0, v1);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  check_value(res);
  return res->get_id();
}

uint64_t
ActionMkValue::_run(Sort sort, const std::string& val, Solver::Base base)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\""
               << " " << base;
  Term res = d_solver.mk_value(sort, val, base);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  check_value(res);
  return res->get_id();
}

void
ActionMkValue::check_value(Term term)
{
  assert(term->get_leaf_kind() == AbsTerm::LeafKind::VALUE);

  if (d_rng.pick_with_prob(990)) return;

  ActionMkTerm mkterm(d_smgr);
  mkterm.check_term(term);

  MURXLA_TEST(term->is_value());
  MURXLA_TEST(!term->is_const());
  MURXLA_TEST(!term->is_var());

  d_solver.check_value(term);

  if (term->is_bag())
  {
    MURXLA_TEST(term->is_bag_value());
  }
  else if (term->is_bool())
  {
    MURXLA_TEST(term->is_bool_value());
  }
  else if (term->is_bv())
  {
    MURXLA_TEST(term->is_bv_value());
  }
  else if (term->is_fp())
  {
    MURXLA_TEST(term->is_fp_value());
  }
  else if (term->is_int())
  {
    MURXLA_TEST(term->is_int_value());
  }
  else if (term->is_real())
  {
    MURXLA_TEST(term->is_real_value());
  }
  else if (term->is_rm())
  {
    MURXLA_TEST(term->is_rm_value());
  }
  else if (term->is_string())
  {
    MURXLA_TEST(term->is_string_value());
  }
  else if (term->is_reglan())
  {
    MURXLA_TEST(term->is_reglan_value());
  }
  else if (term->is_seq())
  {
    MURXLA_TEST(term->is_seq_value());
  }
  else if (term->is_set())
  {
    MURXLA_TEST(term->is_set_value());
  }
  else
  {
    assert(false);
  }
}

/* -------------------------------------------------------------------------- */

bool
ActionMkSpecialValue::run(Sort sort)
{
  assert(d_solver.is_initialized());
  SortKind sort_kind         = sort->get_kind();
  const auto& special_values = d_solver.get_special_values(sort_kind);
  assert(!special_values.empty());
  _run(sort,
       d_rng.pick_from_set<std::unordered_set<AbsTerm::SpecialValueKind>,
                           AbsTerm::SpecialValueKind>(special_values));
  return true;
}

bool
ActionMkSpecialValue::run()
{
  /* Pick sort of value. */
  if (!d_smgr.has_sort(d_solver.get_special_values_sort_kinds())) return false;
  Sort sort = d_smgr.pick_sort(d_solver.get_special_values_sort_kinds(), false);
  return run(sort);
}

std::vector<uint64_t>
ActionMkSpecialValue::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());

  uint64_t res = 0;
  Sort sort    = d_smgr.get_untraced_sort(untrace_str_to_id(tokens[0]));
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
ActionMkSpecialValue::_run(Sort sort, const AbsTerm::SpecialValueKind& val)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
  Term res;
  res = d_solver.mk_special_value(sort, val);
  d_smgr.add_value(res, sort, sort->get_kind(), val);
  MURXLA_TRACE_RETURN << res;
  check_special_value(d_rng, res, val);
  return res->get_id();
}

void
ActionMkSpecialValue::check_special_value(RNGenerator& rng,
                                          Term term,
                                          const AbsTerm::SpecialValueKind& kind)
{
  assert(term->get_leaf_kind() == AbsTerm::LeafKind::VALUE);

  if (rng.pick_with_prob(990)) return;

  ActionMkValue mkvalue(d_smgr);
  mkvalue.check_value(term);

  MURXLA_TEST(term->is_special_value(kind));

  if (term->is_bv())
  {
    uint32_t size                 = term->get_bv_size();
    const auto& special_bv_values = d_solver.get_special_values(SORT_BV);
    const auto& special_bv_value_kind =
        d_rng.pick_from_set<const std::unordered_set<AbsTerm::SpecialValueKind>,
                            AbsTerm::SpecialValueKind>(special_bv_values);
    if (kind != special_bv_value_kind)
    {
      if (size == 1)
      {
        if (kind == AbsTerm::SPECIAL_VALUE_BV_ONE)
        {
          if (special_bv_value_kind == AbsTerm::SPECIAL_VALUE_BV_ONES
              || special_bv_value_kind == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED)
          {
            MURXLA_TEST(term->is_special_value(special_bv_value_kind));
          }
          else
          {
            MURXLA_TEST(!term->is_special_value(special_bv_value_kind));
          }
        }
        else if (kind == AbsTerm::SPECIAL_VALUE_BV_ONES)
        {
          if (special_bv_value_kind == AbsTerm::SPECIAL_VALUE_BV_ONE
              || special_bv_value_kind == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED)
          {
            MURXLA_TEST(term->is_special_value(special_bv_value_kind));
          }
          else
          {
            MURXLA_TEST(!term->is_special_value(special_bv_value_kind));
          }
        }
        else if (kind == AbsTerm::SPECIAL_VALUE_BV_ZERO)
        {
          if (special_bv_value_kind == AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED)
          {
            MURXLA_TEST(term->is_special_value(special_bv_value_kind));
          }
          else
          {
            MURXLA_TEST(!term->is_special_value(special_bv_value_kind));
          }
        }
        else if (kind == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED)
        {
          if (special_bv_value_kind == AbsTerm::SPECIAL_VALUE_BV_ONE
              || special_bv_value_kind == AbsTerm::SPECIAL_VALUE_BV_ONES)
          {
            MURXLA_TEST(term->is_special_value(special_bv_value_kind));
          }
          else
          {
            MURXLA_TEST(!term->is_special_value(special_bv_value_kind));
          }
        }
        else
        {
          assert(kind == AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED);
          if (special_bv_value_kind == AbsTerm::SPECIAL_VALUE_BV_ZERO)
          {
            MURXLA_TEST(term->is_special_value(special_bv_value_kind));
          }
          else
          {
            MURXLA_TEST(!term->is_special_value(special_bv_value_kind));
          }
        }
      }
      else
      {
        MURXLA_TEST(!term->is_special_value(special_bv_value_kind));
      }
    }
  }
}

/* -------------------------------------------------------------------------- */

bool
ActionInstantiateSort::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.has_sort_dt_parametric()) return false;
  auto exclude_sorts = d_solver.get_unsupported_sort_param_sort_kinds();
  if (!d_smgr.has_sort_excluding(exclude_sorts)) return false;
  Sort param_sort   = d_smgr.pick_sort_dt_param();
  uint32_t n_params = param_sort->get_sorts().size();
  std::vector<Sort> sorts;
  for (uint32_t i = 0; i < n_params; ++i)
  {
    sorts.push_back(d_smgr.pick_sort_excluding(exclude_sorts));
  }
  _run(param_sort, sorts);
  return true;
}

std::vector<uint64_t>
ActionInstantiateSort::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);
  Sort param_sort = d_smgr.get_untraced_sort(untrace_str_to_id(tokens[0]));
  std::vector<Sort> sorts;
  for (size_t i = 1, n_tokens = tokens.size(); i < n_tokens; ++i)
  {
    sorts.push_back(d_smgr.get_untraced_sort(untrace_str_to_id(tokens[i])));
  }
  return {_run(param_sort, sorts)};
}

uint64_t
ActionInstantiateSort::_run(Sort param_sort, const std::vector<Sort>& sorts)
{
  MURXLA_TRACE << get_kind() << " " << param_sort << sorts;
  Sort res = d_solver.instantiate_sort(param_sort, sorts);
  res->set_dt_is_instantiated(true);
  MURXLA_TEST(param_sort->is_dt_parametric());
  /* We need to reconstruct the instantiation of map AbsSort::d_dt_ctors. */
  res->set_dt_ctors(param_sort->instantiate_dt_param_sort(sorts));
  res->set_sorts(sorts);
  d_smgr.add_sort(
      res, param_sort->get_kind(), false, res->is_dt_well_founded());
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
  Term t = d_smgr.get_untraced_term(untrace_str_to_id(tokens[0]));
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
  if (!d_smgr.d_incremental && d_smgr.d_n_sat_calls > 0)
  {
    d_disable = true;
    return false;
  }
  /* Only call action immediately again with low priority. */
  if (d_smgr.d_sat_called && d_rng.pick_with_prob(95)) return false;
  _run();
  return true;
}

std::vector<uint64_t>
ActionCheckSat::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  _run();
  return {};
}

void
ActionCheckSat::_run()
{
  MURXLA_TRACE << get_kind();
  reset_sat();
  d_smgr.report_result(d_solver.check_sat());
}

/* -------------------------------------------------------------------------- */

bool
ActionCheckSatAssuming::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_incremental)
  {
    d_disable = true;
    return false;
  }
  if (!d_smgr.has_term(SORT_BOOL, 0)) return false;
  /* Only call action immediately again with low priority. */
  if (d_smgr.d_sat_called && d_rng.pick_with_prob(95)) return false;
  uint32_t n_assumptions =
      d_rng.pick<uint32_t>(1, MURXLA_MAX_N_ASSUMPTIONS_CHECK_SAT);
  std::vector<Term> assumptions;
  for (uint32_t i = 0; i < n_assumptions; ++i)
  {
    assumptions.push_back(d_smgr.pick_term(SORT_BOOL, 0));
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
    Term t      = d_smgr.get_untraced_term(id);
    MURXLA_CHECK_TRACE_TERM(t, id);
    assumptions.push_back(t);
  }
  _run(assumptions);
  return {};
}

void
ActionCheckSatAssuming::_run(const std::vector<Term>& assumptions)
{
  MURXLA_TRACE << get_kind() << " " << assumptions.size() << assumptions;
  reset_sat();
  for (const Term& t : assumptions)
  {
    d_smgr.add_assumption(t);
  }
  d_smgr.report_result(d_solver.check_sat_assuming(assumptions));
}

/* -------------------------------------------------------------------------- */

bool
ActionGetUnsatAssumptions::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_unsat_assumptions)
  {
    d_disable = true;
    return false;
  }
  if (!d_smgr.d_sat_called) return false;
  if (d_smgr.d_sat_result != Solver::Result::UNSAT) return false;
  if (!d_smgr.d_incremental)
  {
    d_disable = true;
    return false;
  }
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
  /* Note: Unsat assumptions are checked in the checker solver. */
  (void) d_solver.get_unsat_assumptions();
}

/* -------------------------------------------------------------------------- */

bool
ActionGetUnsatCore::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_unsat_cores)
  {
    d_disable = true;
    return false;
  }
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
  if (!d_smgr.d_model_gen)
  {
    d_disable = true;
    return false;
  }
  if (!d_smgr.d_sat_called) return false;
  if (d_smgr.d_sat_result != Solver::Result::SAT) return false;

  uint32_t n_terms = d_rng.pick<uint32_t>(1, MURXLA_MAX_N_TERMS_GET_VALUE);
  std::vector<Term> terms;
  auto exclude_sorts = d_solver.get_unsupported_get_value_sort_kinds();
  if (!d_smgr.has_sort_excluding(exclude_sorts, true)) return false;
  for (uint32_t i = 0; i < n_terms; ++i)
  {
    SortKind sort_kind = d_smgr.pick_sort_kind(0, exclude_sorts);
    terms.push_back(d_smgr.pick_term(sort_kind, 0));
  }
  _run(terms);
  return true;
}

std::vector<uint64_t>
ActionGetValue::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS_MIN(2, "", tokens.size());
  std::vector<Term> terms;
  uint32_t n_args = str_to_uint32(tokens[0]);
  for (uint32_t i = 0, idx = 1; i < n_args; ++i, ++idx)
  {
    uint32_t id = untrace_str_to_id(tokens[idx]);
    Term t      = d_smgr.get_untraced_term(id);
    MURXLA_CHECK_TRACE_TERM(t, id);
    terms.push_back(t);
  }
  _run(terms);
  return {};
}

void
ActionGetValue::_run(const std::vector<Term>& terms)
{
  MURXLA_TRACE << get_kind() << " " << terms.size() << terms;
  /* Note: The Terms in this vector are solver terms wrapped into Term,
   *       without sort information! */
  (void) d_solver.get_value(terms);
}

/* -------------------------------------------------------------------------- */

bool
ActionPush::run()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_incremental)
  {
    d_disable = true;
    return false;
  }
  uint32_t n_levels = d_rng.pick<uint32_t>(1, MURXLA_MAX_N_PUSH_LEVELS);
  _run(n_levels);
  return true;
}

std::vector<uint64_t>
ActionPush::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
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
  if (!d_smgr.d_incremental)
  {
    d_disable = true;
    return false;
  }
  if (d_smgr.d_n_push_levels == 0) return false;
  uint32_t n_levels = d_rng.pick<uint32_t>(1, d_smgr.d_n_push_levels);
  _run(n_levels);
  return true;
}

std::vector<uint64_t>
ActionPop::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
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
  d_smgr.reset();
  d_solver.reset();
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
  if (!d_smgr.d_model_gen)
  {
    d_disable = true;
    return false;
  }
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
