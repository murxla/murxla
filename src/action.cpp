/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
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

Sort
Action::get_untraced_sort(uint64_t id)
{
  Sort res = d_smgr.get_untraced_sort(id);
  MURXLA_CHECK_TRACE(res) << "unknown sort with id " << id;
  return res;
}

Term
Action::get_untraced_term(uint64_t id)
{
  Term res = d_smgr.get_untraced_term(id);
  MURXLA_CHECK_TRACE(res) << "unknown term with id " << id;
  return res;
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
  uint64_t seed = d_sng.next_solver_seed();
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
TransitionCreateInputs::generate()
{
  return d_smgr.d_stats.inputs > 0;
}

/* -------------------------------------------------------------------------- */

bool
TransitionCreateSorts::generate()
{
  return d_smgr.d_stats.sorts > 0;
}

/* -------------------------------------------------------------------------- */

bool
ActionTermGetChildren::generate()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.has_term()) return false;
  Term term = d_smgr.pick_term();
  run(term);
  return true;
}

std::vector<uint64_t>
ActionTermGetChildren::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
  Term t = get_untraced_term(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_TERM(t, tokens[0]);
  run(t);
  return {};
}

void
ActionTermGetChildren::run(Term term)
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
ActionNew::generate()
{
  if (d_solver.is_initialized()) d_solver.delete_solver();
  run();
  return true;
}

std::vector<uint64_t>
ActionNew::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  run();
  return {};
}

void
ActionNew::run()
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
ActionDelete::generate()
{
  assert(d_solver.is_initialized());
  run();
  return true;
}

std::vector<uint64_t>
ActionDelete::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  run();
  return {};
}

void
ActionDelete::run()
{
  MURXLA_TRACE << get_kind();
  d_smgr.clear();
  d_solver.delete_solver();
}

/* -------------------------------------------------------------------------- */

bool
ActionSetLogic::generate()
{
  assert(d_solver.is_initialized());

  TheorySet enabled_theories = d_smgr.get_enabled_theories();
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

  it = enabled_theories.find(THEORY_FF);
  if (it != enabled_theories.end())
  {
    enabled_theories.erase(THEORY_FF);
    logic += "FF";
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

  run(logic);
  return true;
}

std::vector<uint64_t>
ActionSetLogic::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
  run(tokens[0]);
  return {};
}

void
ActionSetLogic::run(const std::string& logic)
{
  MURXLA_TRACE << get_kind() << " " << logic;
  d_solver.set_logic(logic);
}

/* -------------------------------------------------------------------------- */

bool
ActionSetOption::generate()
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

  run(opt, value);
  return true;
}

std::vector<uint64_t>
ActionSetOption::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
  run(tokens[0], tokens[1]);
  return {};
}

void
ActionSetOption::run(const std::string& opt, const std::string& value)
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
ActionSetOptionReq::generate()
{
  for (const auto& [name, value] : d_solver_options)
  {
    d_setoption->run(name, value);
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

ActionMkSort::ActionMkSort(SolverManager& smgr)
    : Action(smgr, s_name, ID_LIST),
      d_exclude_array_element_sort_kinds(
          smgr.get_profile().get_unsupported_array_element_sort_kinds()),
      d_exclude_array_index_sort_kinds(
          smgr.get_profile().get_unsupported_array_index_sort_kinds()),
      d_exclude_bag_element_sort_kinds(
          smgr.get_profile().get_unsupported_bag_element_sort_kinds()),
      d_exclude_dt_sel_codomain_sort_kinds(
          smgr.get_profile().get_unsupported_dt_sel_codomain_sort_kinds()),
      d_exclude_fun_sort_codomain_sort_kinds(
          smgr.get_profile().get_unsupported_fun_sort_codomain_sort_kinds()),
      d_exclude_fun_sort_domain_sort_kinds(
          smgr.get_profile().get_unsupported_fun_sort_domain_sort_kinds()),
      d_exclude_seq_element_sort_kinds(
          smgr.get_profile().get_unsupported_seq_element_sort_kinds()),
      d_exclude_set_element_sort_kinds(
          smgr.get_profile().get_unsupported_set_element_sort_kinds()),
      d_exclude_sort_param_sort_kinds(
          smgr.get_profile().get_unsupported_sort_param_sort_kinds())
{
  d_n_args_weights.push_back(0);
  for (uint32_t i = 0; i < MURXLA_MK_TERM_N_ARGS_MAX; ++i)
  {
    uint32_t n = MURXLA_MK_TERM_N_ARGS_MAX - i;
    d_n_args_weights.push_back(n * n);
  }
}

bool
ActionMkSort::generate()
{
  assert(d_solver.is_initialized());
  SortKind kind = d_smgr.pick_sort_kind_data().d_kind;
  RNGenerator::Choice pick;

  ++d_smgr.d_mbt_stats->d_sorts[kind];

  switch (kind)
  {
    case SORT_ARRAY:
    {
      if (!d_smgr.has_sort_excluding(d_exclude_array_index_sort_kinds, false))
      {
        return false;
      }
      Sort index_sort =
          d_smgr.pick_sort_excluding(d_exclude_array_index_sort_kinds, false);
      if (!d_smgr.has_sort_excluding(d_exclude_array_element_sort_kinds, false))
      {
        return false;
      }
      Sort element_sort =
          d_smgr.pick_sort_excluding(d_exclude_array_element_sort_kinds, false);
      run(kind, {index_sort, element_sort});
      break;
    }

    case SORT_BAG:
    {
      if (!d_smgr.has_sort_excluding(d_exclude_bag_element_sort_kinds, false))
        return false;
      auto sort =
          d_smgr.pick_sort_excluding(d_exclude_bag_element_sort_kinds, false);
      run(kind, {sort});
    }
    break;

    case SORT_BV:
      run(kind, d_rng.pick<uint32_t>(MURXLA_BW_MIN, MURXLA_BW_MAX));
      break;

    case SORT_DT:
    {
      if (!d_smgr.has_sort()) return false;

      bool no_sel_sorts = !d_smgr.has_sort_excluding(
          d_exclude_dt_sel_codomain_sort_kinds, false);

      uint32_t n_dt_sorts = d_rng.pick<uint32_t>(1, MURXLA_DT_MAX_N_DTYPES);
      bool mutual_rec     = n_dt_sorts > 1 && d_rng.flip_coin();

      std::vector<std::string> dt_names;
      std::vector<std::vector<Sort>> param_sorts;
      std::vector<AbsSort::DatatypeConstructorMap> constructors;
      std::unordered_map<std::string, uint32_t> dt_n_params;

      for (uint32_t i = 0; i < n_dt_sorts; ++i)
      {
        dt_names.push_back(d_smgr.pick_symbol("_dt"));
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
                new ParamSort(d_smgr.pick_symbol("_p"))));
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
              sname = d_smgr.pick_symbol("_sel");
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
                    if (psorts.size()
                        && (!d_smgr.has_sort_excluding(
                                d_exclude_sort_param_sort_kinds)
                            || d_rng.flip_coin()))
                    {
                      inst_sorts.push_back(
                          d_rng.pick_from_set<decltype(psorts), Sort>(psorts));
                    }
                    else if (d_smgr.has_sort_excluding(
                                 d_exclude_sort_param_sort_kinds))
                    {
                      inst_sorts.push_back(d_smgr.pick_sort_excluding(
                          d_exclude_sort_param_sort_kinds, false));
                    }
                    else
                    {
                      return false;
                    }
                  }
                  s->set_sorts(inst_sorts);
                }
              }
              else if (!no_sel_sorts)
              {
                s = d_smgr.pick_sort_excluding(
                    d_exclude_dt_sel_codomain_sort_kinds, false);
              }
            }
            sels.emplace_back(sname, s);
          }

          std::string cname;
          do
          {
            cname = d_smgr.pick_symbol("_cons");
          } while (ctors.find(cname) != ctors.end());
          ctors[cname] = sels;
        }
        constructors.push_back(ctors);
      }
      run(kind, dt_names, param_sorts, constructors);
    }
    break;

    case SORT_FF:
    {
      const char* primes[10] = {
          "7", "11", "13", "17", "19", "23", "29", "31", "37", "41"};
      run(SORT_FF, primes[d_rng.pick<uint32_t>(0, 9)]);
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
      run(kind, ew, sw);
      /* Operator fp expects three bit-vector terms of size 1, ew and sw - 1 as
       * arguments. Operator to_fp from IEEE BV expects a bit-vector of size
       * ew + sw. To increase the probability that terms of these sizes are
       * available, we also generate the corresponding bit-vector sorts. */
      run(SORT_BV, 1);
      run(SORT_BV, ew);
      run(SORT_BV, sw - 1);
      run(SORT_BV, ew + sw);
    }
    break;

    case SORT_FUN:
    {
      std::vector<Sort> sorts;
      if (!d_smgr.has_sort_excluding(d_exclude_fun_sort_domain_sort_kinds,
                                     false)
          || !d_smgr.has_sort_excluding(d_exclude_fun_sort_codomain_sort_kinds,
                                        false))
      {
        return false;
      }
      uint32_t nsorts = d_rng.pick_weighted<uint32_t>(d_n_args_weights.begin(),
                                                      d_n_args_weights.end());
      for (uint32_t i = 0; i < nsorts; ++i)
      {
        sorts.push_back(d_smgr.pick_sort_excluding(
            d_exclude_fun_sort_domain_sort_kinds, false));
      }
      sorts.push_back(d_smgr.pick_sort_excluding(
          d_exclude_fun_sort_codomain_sort_kinds, false));
      run(kind, sorts);
    }
    break;

    case SORT_SEQ:
    {
      if (!d_smgr.has_sort_excluding(d_exclude_seq_element_sort_kinds, false))
        return false;
      auto sort =
          d_smgr.pick_sort_excluding(d_exclude_seq_element_sort_kinds, false);
      run(kind, {sort});
    }
    break;

    case SORT_SET:
    {
      if (!d_smgr.has_sort_excluding(d_exclude_set_element_sort_kinds, false))
        return false;
      auto sort =
          d_smgr.pick_sort_excluding(d_exclude_set_element_sort_kinds, false);
      run(kind, {sort});
    }
    break;

    case SORT_BOOL:
    case SORT_INT:
    case SORT_REAL:
    case SORT_REGLAN:
    case SORT_STRING:
    case SORT_RM:
      run(kind);
      break;

      run(kind);
      break;

    case SORT_UNINTERPRETED: run(kind, d_smgr.pick_symbol("_u")); break;

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
      sorts.push_back(get_untraced_sort(untrace_str_to_id(tokens[1])));
      sorts.push_back(get_untraced_sort(untrace_str_to_id(tokens[2])));
      res = run(kind, sorts);
      break;
    }

    case SORT_BAG:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_BAG) != theories.end())
          << "solver does not support theory of bags";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(2, n_tokens, kind);
      res = run(kind, {get_untraced_sort(untrace_str_to_id(tokens[1]))});
      break;

    case SORT_BOOL:
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
      res = run(kind);
      break;

    case SORT_BV:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_BV) != theories.end())
          << "solver does not support theory of bit-vectors";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(2, n_tokens, kind);
      res = run(kind, str_to_uint32(tokens[1]));
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
              ssort = symbol_to_psort.at(pname);
            }
            else if (tokens[idx].substr(0, 2) == "s<")
            {
              const std::string& t = tokens[idx++];
              std::string uname    = str_to_str(t.substr(2, t.size() - 3));
              ssort =
                  std::shared_ptr<UnresolvedSort>(new UnresolvedSort(uname));
              uint32_t n_inst_sorts = str_to_uint32(tokens[idx++]);
              std::vector<Sort> inst_sorts;
              for (uint32_t k = 0; k < n_inst_sorts; ++k)
              {
                if (tokens[idx].substr(0, 2) == "s\"")
                {
                  std::string upname = str_to_str(tokens[idx++].substr(1));
                  assert(symbol_to_psort.find(upname) != symbol_to_psort.end());
                  inst_sorts.push_back(symbol_to_psort.at(upname));
                }
                else
                {
                  inst_sorts.push_back(
                      get_untraced_sort(untrace_str_to_id(tokens[idx++])));
                }
              }
              ssort->set_sorts(inst_sorts);
            }
            else
            {
              ssort = get_untraced_sort(untrace_str_to_id(tokens[idx++]));
            }
            ctors[cname].emplace_back(sname, ssort);
          }
        }
        dt_names.push_back(dt_name);
        param_sorts.push_back(psorts);
        constructors.push_back(ctors);
      }

      res = run(kind, dt_names, param_sorts, constructors);
    }
    break;

    case SORT_FF:
      MURXLA_CHECK_TRACE(theories.find(THEORY_FF) != theories.end()
                         || theories.find(THEORY_FF) != theories.end())
          << "solver does not support theory of finite-field arithmetic";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(2, n_tokens, kind);
      res = run(kind, tokens[1]);
      break;

    case SORT_FP:
      MURXLA_CHECK_TRACE(theories.find(THEORY_FP) != theories.end()
                         || theories.find(THEORY_FP) != theories.end())
          << "solver does not support theory of floating-point arithmetic";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(3, n_tokens, kind);
      res = run(kind, str_to_uint32(tokens[1]), str_to_uint32(tokens[2]));
      break;

    case SORT_FUN:
    {
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_UF) != theories.end())
          << "solver does not support theory of UF";
      std::vector<Sort> sorts;
      for (auto it = tokens.begin() + 1; it < tokens.end(); ++it)
      {
        Sort s = get_untraced_sort(untrace_str_to_id(*it));
        MURXLA_CHECK_TRACE(s != nullptr)
            << "unknown sort id '" << *it << "' as argument to " << get_kind();
        sorts.push_back(s);
      }
      res = run(kind, sorts);
      break;
    }

    case SORT_INT:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_INT) != theories.end())
          << "solver does not support theory of integers";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
      res = run(kind);
      break;

    case SORT_REAL:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_REAL) != theories.end())
          << "solver does not support theory of reals";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
      res = run(kind);
      break;

    case SORT_REGLAN:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_STRING) != theories.end())
          << "solver does not support theory of strings";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
      res = run(kind);
      break;

    case SORT_RM:
      MURXLA_CHECK_TRACE(theories.find(THEORY_FP) != theories.end()
                         || theories.find(THEORY_FP) != theories.end())
          << "solver does not support theory of floating-point arithmetic";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
      res = run(kind);
      break;

    case SORT_SEQ:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_SEQ) != theories.end())
          << "solver does not support theory of sequences";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(2, n_tokens, kind);
      res = run(kind, {get_untraced_sort(untrace_str_to_id(tokens[1]))});
      break;

    case SORT_SET:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_SET) != theories.end())
          << "solver does not support theory of sets";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(2, n_tokens, kind);
      res = run(kind, {get_untraced_sort(untrace_str_to_id(tokens[1]))});
      break;

    case SORT_STRING:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_STRING) != theories.end())
          << "solver does not support theory of strings";
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(1, n_tokens, kind);
      res = run(kind);
      break;

    case SORT_UNINTERPRETED:
      MURXLA_CHECK_TRACE(theories.find(THEORY_ALL) != theories.end()
                         || theories.find(THEORY_BOOL) != theories.end());
      MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(2, n_tokens, kind);
      res = run(kind, tokens[1]);
      break;

    default: MURXLA_CHECK_TRACE(false) << "unknown sort kind " << tokens[0];
  }
  return res;
}

std::vector<uint64_t>
ActionMkSort::run(SortKind kind)
{
  MURXLA_TRACE << get_kind() << " " << kind;
  Sort res = d_solver.mk_sort(kind);
  d_smgr.add_sort(res, kind);
  check_sort(res);
  MURXLA_TRACE_RETURN << res;
  return {res->get_id()};
}

std::vector<uint64_t>
ActionMkSort::run(SortKind kind, const std::string& name)
{
  assert(kind == SORT_UNINTERPRETED || kind == SORT_FF);
  MURXLA_TRACE << get_kind() << " " << kind << " " << name;
  Sort res;
  if (kind == SORT_UNINTERPRETED)
  {
    res = d_solver.mk_sort(name);
  }
  else if (kind == SORT_FF)
  {
    res = d_solver.mk_sort(kind, name);
  }
  else
  {
    assert(false);
  }
  d_smgr.add_sort(res, kind);
  check_sort(res);
  MURXLA_TRACE_RETURN << res;
  return {res->get_id()};
}

//! [docs-action-mksort-run start]
std::vector<uint64_t>
ActionMkSort::run(SortKind kind, uint32_t bw)
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
//! [docs-action-mksort-run end]

std::vector<uint64_t>
ActionMkSort::run(SortKind kind, uint32_t ew, uint32_t sw)
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
ActionMkSort::run(SortKind kind, const std::vector<Sort>& sorts)
{
  MURXLA_TRACE << get_kind() << " " << kind << sorts;
  assert(sorts.size() >= 1);
  Sort res = d_solver.mk_sort(kind, sorts);
  res->set_sorts(sorts);
  d_smgr.add_sort(res, kind);
  check_sort(res);
  MURXLA_TEST(res->get_sorts().size() == sorts.size());
  MURXLA_TRACE_RETURN << res;
  return {res->get_id()};
}

std::vector<uint64_t>
ActionMkSort::run(SortKind kind,
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
        if (ssort && ssort->is_unresolved_sort())
        {
          const auto& ssorts = ssort->get_sorts();
          ss << " " << ssorts.size() << ssorts;
        }
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

  MURXLA_TRACE_RETURN << res_sorts;

  /* Update d_ctors: resolve unresolved sorts in d_ctors and add back reference
   * for parameter sorts. */
  for (size_t i = 0; i < n_dt_sorts; ++i)
  {
    /* Add back reference to DT sort for param sorts. */
    for (auto& p : param_sorts[i])
    {
      p->set_associated_sort({res_sorts[i]});
    }

    /* Add back reference to DT sort for unresolved sorts. */
    for (auto& ctor : res_sorts[i]->get_dt_ctors())
    {
      for (auto& sel : ctor.second)
      {
        if (sel.second && sel.second->is_unresolved_sort())
        {
          UnresolvedSort* usort =
              checked_cast<UnresolvedSort*>(sel.second.get());
          const std::string& symbol = usort->get_symbol();
          auto it = symbol_to_dt_sort.find(symbol);
          assert(it != symbol_to_dt_sort.end());
          Sort associated_sort = it->second;
          assert(associated_sort);
          usort->set_associated_sort(associated_sort);
        }
      }
    }
  }

  for (size_t i = 0; i < n_dt_sorts; ++i)
  {
    /* Resolve unresolved sorts. */
    for (auto& ctor : res_sorts[i]->get_dt_ctors())
    {
      for (auto& sel : ctor.second)
      {
        Sort& ssort = sel.second;
        if (ssort && ssort->is_unresolved_sort())
        {
          UnresolvedSort* usort = checked_cast<UnresolvedSort*>(ssort.get());
          Sort associated_sort  = usort->get_associated_sort();
          assert(associated_sort);
          /* We instantiate and cache the instantiated parametric unresolved
           * sort if the sort parameters do not contain a ParamSort.
           * Else we keep the unresolved sort but add the associated parametric
           * DT sort to the head of the cache. These still unresolved sorts
           * will be resolved when the parametric DT is instantiated. */
          if (associated_sort->is_dt_parametric()
              && !associated_sort->is_dt_instantiated())
          {
            auto inst_sorts = usort->get_sorts();
            assert(!inst_sorts.empty());
            bool has_param_sort = false;
            for (const auto& s : inst_sorts)
            {
              if (s->is_param_sort())
              {
                has_param_sort = true;
                break;
              }
            }
            if (!has_param_sort)
            {
              ActionInstantiateSort instantiate_sort(d_smgr);
              ssort = instantiate_sort.run(associated_sort, inst_sorts);
            }
            else
            {
              usort->set_sorts(inst_sorts);
            }
          }
          else
          {
            ssort = associated_sort;
          }
        }
      }
    }
  }
  for (size_t i = 0; i < n_dt_sorts; ++i)
  {
    /* Check sorts. */
    check_sort(res_sorts[i], dt_names[i]);
  }

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
ActionMkTerm::generate(Op::Kind kind)
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
    run(kind, sort_kind, dt_sort, {ctor}, args);
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
    run(kind, sort_kind, {ctor, sel}, {arg});
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
    run(kind, sort_kind, {ctor}, {arg});
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
    run(kind, sort_kind, {ctor, sel}, args);
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
      size_t n_vars = d_rng.pick<size_t>(1, d_smgr.get_num_vars());
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
      assert(sorts.size() > 1);
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
      if (!d_smgr.has_sort_excluding(d_exclude_seq_element_sort_kinds))
        return false;
      Sort element_sort =
          d_smgr.pick_sort_excluding(d_exclude_seq_element_sort_kinds);
      assert(d_exclude_seq_element_sort_kinds.find(element_sort->get_kind())
             == d_exclude_seq_element_sort_kinds.end());
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
      if (!d_smgr.has_sort_excluding(d_exclude_set_element_sort_kinds))
        return false;
      Sort element_sort =
          d_smgr.pick_sort_excluding(d_exclude_set_element_sort_kinds);
      assert(d_exclude_set_element_sort_kinds.find(element_sort->get_kind())
             == d_exclude_set_element_sort_kinds.end());
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
      size_t n_vars = d_rng.pick<size_t>(1, d_smgr.get_num_vars());
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
    else if (kind == Op::SET_UNION && d_smgr.has_value()
             && d_rng.pick_with_prob(10))
    {
      /* Create union chain with canonical set value. */
      Term value        = d_smgr.pick_value();
      Sort element_sort = value->get_sort();
      Term set_value    = mk_set_value(element_sort);
      args.push_back(set_value);
      args.push_back(d_smgr.pick_term(set_value->get_sort()));
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
      if (!d_smgr.has_term(SORT_INT)) return false;
      if (!d_smgr.has_sort_excluding(d_exclude_bag_element_sort_kinds))
        return false;
      Sort element_sort =
          d_smgr.pick_sort_excluding(d_exclude_bag_element_sort_kinds);
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
          indices.push_back(d_rng.pick<uint32_t>(1, INT32_MAX));
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

    /* FIXME: We need a way to derive the term sort kind in case of
     * sort_kind = SORT_ANY that is local to the solver wrapper for
     * solver-specific operator kinds. Until then, we set it to the sort
     * kind of the first element (which may not work for all cases!).
     */
    //assert(sort_kind != SORT_ANY);
    if (sort_kind == SORT_ANY && arity > 0)
    {
      sort_kind = args[0]->get_sort()->get_kind();
    }
    run(kind, sort_kind, args, indices);
  }

  ++d_smgr.d_mbt_stats->d_ops_ok[op.d_id];

  return true;
}

ActionMkTerm::ActionMkTerm(SolverManager& smgr)
    : Action(smgr, s_name, ID),
      d_exclude_bag_element_sort_kinds(
          smgr.get_profile().get_unsupported_bag_element_sort_kinds()),
      d_exclude_dt_match_sort_kinds(
          smgr.get_profile().get_unsupported_dt_match_sort_kinds()),
      d_exclude_seq_element_sort_kinds(
          smgr.get_profile().get_unsupported_seq_element_sort_kinds()),
      d_exclude_set_element_sort_kinds(
          smgr.get_profile().get_unsupported_set_element_sort_kinds())

{
  for (uint32_t i = 0; i < MURXLA_MK_TERM_N_ARGS_MAX; ++i)
  {
    uint32_t n = MURXLA_MK_TERM_N_ARGS_MAX - i;
    d_n_args_weights.push_back(n * n);
  }
}

bool
ActionMkTerm::generate()
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
    /* Pick sort with terms. */
    SortKind sort_kind =
        d_smgr.pick_sort_kind_excluding(d_exclude_dt_match_sort_kinds);
    Sort sort          = d_smgr.pick_sort(sort_kind);

    //! [docs-action-mkterm-generate-dt_match_pattern-pre start]
    ActionMkVar mkvar(d_smgr);  // to create variables on demand
    //! [docs-action-mkterm-generate-dt_match_pattern-pre end]

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
      uint64_t match_case_id;
      Op::Kind match_case_kind;

      /* Pick variable pattern with 10% probability. */
      if (d_rng.pick_with_prob(10))
      {
        auto var_id = mkvar.run(dt_sort, d_smgr.pick_symbol())[0];
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
          //! [docs-action-mkterm-generate-dt_match_pattern start]
          for (const auto& sel : sel_names)
          {
            /* Create variable of selector codomain sort for each selector. */
            auto var_id =
                mkvar.run(dt_sort->get_dt_sel_sort(dt_sort, ctor, sel),
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
            /* Do not create quantifiers since this would bind the variables
             * created above. */
            if (op_kind == Op::FORALL || op_kind == Op::EXISTS) continue;
            // Skip set comprehension since it would also bind the variables
            // created above.
            if (op_kind == Op::SET_COMPREHENSION) continue;
            if (generate(op_kind)) n_terms_created += 1;
          }
          match_case_kind = Op::DT_MATCH_BIND_CASE;
          //! [docs-action-mkterm-generate-dt_match_pattern end]
        }
        else
        {
          match_case_kind = Op::DT_MATCH_CASE;
        }
      }
      Term match_term = d_smgr.pick_term(sort);
      assert(match_term->get_kind() != Op::DT_MATCH_CASE);
      assert(match_term->get_kind() != Op::DT_MATCH_BIND_CASE);
      match_case_args.push_back(match_term);
      match_case_id = run(match_case_kind,
                          sort_kind,
                          dt_sort,
                          match_case_ctor,
                          match_case_args)[0];
      args.push_back(d_smgr.get_term(match_case_id));
    }

    /* We need at least one variable pattern if not all cases are matched. */
    if (!match_all && !match_var)
    {
      auto var_id = mkvar.run(dt_sort, d_smgr.pick_symbol())[0];
      std::vector<Term> match_case_args{d_smgr.get_term(var_id),
                                        d_smgr.pick_term(sort)};
      auto match_case_id = run(
          Op::DT_MATCH_BIND_CASE, sort_kind, dt_sort, {}, match_case_args)[0];
      args.push_back(d_smgr.get_term(match_case_id));
    }

    assert(sort_kind != SORT_ANY);
    run(kind, sort_kind, args, {});

    ++d_smgr.d_mbt_stats->d_ops[op.d_id];
    return true;
  }
  return generate(kind);
}

std::vector<uint64_t>
ActionMkTerm::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS_MIN(
      3, " (operator kind, sort id, number of arguments) ", tokens.size());

  std::vector<Term> args;
  std::vector<uint32_t> indices;
  size_t n_tokens    = tokens.size();
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
    auto id     = untrace_str_to_id(tokens[2]);
    sort        = get_untraced_sort(id);
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
    auto id     = untrace_str_to_id(tokens[idx]);
    Term t      = get_untraced_term(id);
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
    return run(op_kind, sort_kind, str_args, args);
  }

  if (op_kind == Op::DT_APPLY_CONS || op_kind == Op::DT_MATCH_CASE
      || op_kind == Op::DT_MATCH_BIND_CASE)
  {
    return run(op_kind, sort_kind, sort, str_args, args);
  }

  return run(op_kind, sort_kind, args, indices);
}

std::vector<uint64_t>
ActionMkTerm::run(Op::Kind kind,
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
  reset_sat();

  std::vector<Term> bargs;
  /* Note: We pop the variable scopes in run() instead of generate() so that we
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
  // MURXLA_TEST(res->get_sort() == nullptr
  //             || d_solver.get_sort(res, sort_kind)->equals(res->get_sort()));

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
ActionMkTerm::run(Op::Kind kind,
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
  reset_sat();

  Term res = d_solver.mk_term(kind, str_args, args);
  d_smgr.add_term(res, sort_kind, args);
  Sort res_sort = res->get_sort();

  MURXLA_TRACE_RETURN << res << " " << res_sort;
  check_term(res);
  return {res->get_id(), res_sort->get_id()};
}

std::vector<uint64_t>
ActionMkTerm::run(Op::Kind kind,
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
  reset_sat();

  /* Note: We pop the variable scopes in run instead of generate so that we
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
  else if (sort->is_ff())
  {
    MURXLA_TEST(term->is_ff());
    MURXLA_TEST(sort->get_ff_size() == term->get_ff_size());
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
  else if (sort->is_uninterpreted())
  {
    MURXLA_TEST(term->is_uninterpreted());
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
    auto ret = run(Op::ARRAY_STORE, SortKind::SORT_ARRAY, args, {});
    assert(ret.size() == 2);
    result = d_smgr.get_term(ret[0]);
  }

  return result;
}

Term
ActionMkTerm::mk_set_value(const Sort& element_sort)
{
  assert(d_smgr.has_value(element_sort));

  size_t n_unions =
      d_rng.flip_coin() ? 2 : d_rng.pick(1, MURXLA_MAX_UNION_CHAIN_LENGTH);

  std::unordered_set<Term> values;
  for (uint32_t i = 0; i < n_unions; ++i)
  {
    values.insert(d_smgr.pick_value(element_sort));
  }
  std::vector<Term> values_sorted{values.begin(), values.end()};
  std::sort(values_sorted.begin(), values_sorted.end(), [](Term a, Term b) {
    return a->get_id() > b->get_id();
  });

  Term val1 = values_sorted.back();
  values_sorted.pop_back();
  Term val0 = val1;
  if (!values_sorted.empty())
  {
    val0 = values_sorted.back();
    values_sorted.pop_back();
  }
  std::vector<Term> args1 = {val1};
  std::vector<Term> args0 = {val0};
  Term arg1 =
      d_smgr.get_term(run(Op::SET_SINGLETON, SortKind::SORT_SET, args1, {})[0]);
  Term arg0        = val1 == val0
                         ? arg1
                         : d_smgr.get_term(
                      run(Op::SET_SINGLETON, SortKind::SORT_SET, args0, {})[0]);
  std::vector args = {arg0, arg1};
  Term result =
      d_smgr.get_term(run(Op::SET_UNION, SortKind::SORT_SET, args, {})[0]);
  while (!values_sorted.empty())
  {
    args0 = {values_sorted.back()};
    values_sorted.pop_back();
    args = {d_smgr.get_term(
                run(Op::SET_SINGLETON, SortKind::SORT_SET, args0, {})[0]),
            result};
    result =
        d_smgr.get_term(run(Op::SET_UNION, SortKind::SORT_SET, args, {})[0]);
  }
  return result;
}

/* -------------------------------------------------------------------------- */

bool
ActionMkConst::generate(Sort sort)
{
  assert(d_solver.is_initialized());
  if (d_exclude_sort_kinds.find(sort->get_kind()) != d_exclude_sort_kinds.end())
  {
    return false;
  }
  std::string symbol = d_smgr.pick_symbol();
  run(sort, symbol);
  return true;
}

bool
ActionMkConst::generate()
{
  assert(d_solver.is_initialized());
  SortKindSet exclude(d_exclude_sort_kinds);
  /* Deemphasize picking of Boolean sort. */
  if (d_rng.pick_with_prob(800))
  {
    exclude.insert(SORT_BOOL);
  }
  /* If uninterpreted functions are not enabled we are now allowed to create
   * uninterpreted constants with functions sorts.
   * Function sorts may still be present due to */
  TheorySet enabled_theories = d_smgr.get_enabled_theories();
  if (enabled_theories.find(THEORY_UF) == enabled_theories.end())
  {
    exclude.insert(SORT_FUN);
  }
  if (!d_smgr.has_sort_excluding(exclude, false)) return false;
  Sort sort = d_smgr.pick_sort_excluding(exclude, false);
  return generate(sort);
}

std::vector<uint64_t>
ActionMkConst::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
  Sort sort = get_untraced_sort(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
  std::string symbol = str_to_str(tokens[1]);
  return run(sort, symbol);
}

std::vector<uint64_t>
ActionMkConst::run(Sort sort, const std::string& symbol)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << symbol << "\"";
  reset_sat();
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

ActionMkVar::ActionMkVar(SolverManager& smgr)
    : Action(smgr, s_name, ID),
      d_unsupported_sorts_kinds(
          smgr.get_profile().get_unsupported_var_sort_kinds())
{
}

bool
ActionMkVar::generate()
{
  assert(d_solver.is_initialized());
  SortKindSet exclude_sorts = d_unsupported_sorts_kinds;

  /* Deemphasize picking of Boolean sort. */
  if (d_rng.pick_with_prob(800))
  {
    exclude_sorts.insert(SORT_BOOL);
  }

  /* Pick sort of var. */
  if (!d_smgr.has_sort_excluding(exclude_sorts, false)) return false;
  Sort sort          = d_smgr.pick_sort_excluding(exclude_sorts, false);
  std::string symbol = d_smgr.pick_symbol();
  /* Create var. */
  run(sort, symbol);
  return true;
}

std::vector<uint64_t>
ActionMkVar::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
  Sort sort = get_untraced_sort(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
  std::string symbol = str_to_str(tokens[1]);
  return run(sort, symbol);
}

std::vector<uint64_t>
ActionMkVar::run(Sort sort, const std::string& symbol)
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
ActionMkValue::generate(Sort sort)
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
    case SORT_BOOL: run(sort, d_rng.flip_coin()); break;

    case SORT_BV:
    {
      uint32_t bw = sort->get_bv_size();

      std::vector<Solver::Base> bases;
      for (auto b : {Solver::Base::BIN, Solver::Base::DEC, Solver::Base::HEX})
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
      run(sort, val, base);
    }
    break;

    case SORT_FF:
    {
      size_t digits = sort->get_ff_size().length();
      uint32_t digits_small = (uint32_t) digits;
      assert(digits == digits_small);
      std::string val = d_rng.pick_dec_int_string(digits_small);
      run(sort, val);
    }
    break;

    case SORT_FP:
    {
      uint32_t ew     = sort->get_fp_exp_size();
      uint32_t sw     = sort->get_fp_sig_size();
      std::string val = d_rng.pick_bin_string(ew + sw);
      run(sort, val);
    }
    break;

    case SORT_INT:
      run(sort,
          d_rng.pick_dec_int_string(
              d_rng.pick<uint32_t>(1, MURXLA_INT_LEN_MAX)));
      break;

    case SORT_REAL:
      /* RNGenerator::pick_real_string picks from 2 different options, hence
       * we pick between this and passing two decimal strings as rational
       * arguments with probability 50%. */
      if (d_rng.pick_with_prob(500))
      {
        run(sort, d_rng.pick_real_string());
      }
      else
      {
        if (d_rng.flip_coin())
        {
          run(sort,
              d_rng.pick_dec_rational_string(
                  d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX),
                  d_rng.pick<uint32_t>(1, MURXLA_RATIONAL_LEN_MAX)));
        }
        else
        {
          run(sort,
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
      run(sort, value);
    }
    break;

    default: assert(false);
  }

  return true;
}

bool
ActionMkValue::generate()
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
  return generate(sort);
}

std::vector<uint64_t>
ActionMkValue::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);

  uint64_t res = 0;
  Sort sort    = get_untraced_sort(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
  switch (tokens.size())
  {
    case 3:
      if (sort->is_bv())
      {
        res = run(sort,
                  str_to_str(tokens[1]),
                  static_cast<Solver::Base>(str_to_uint32(tokens[2])));
      }
      else
      {
        assert(sort->is_real());
        res = run(sort, str_to_str(tokens[1]), str_to_str(tokens[2]));
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
        res = run(sort, true);
      }
      else if (tokens[1] == "false")
      {
        res = run(sort, false);
      }
      else
      {
        res = run(sort, str_to_str(tokens[1]));
      }
  }

  return {res};
}

uint64_t
ActionMkValue::run(Sort sort, bool val)
{
  MURXLA_TRACE << get_kind() << " " << sort << " " << (val ? "true" : "false");
  reset_sat();
  Term res = d_solver.mk_value(sort, val);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  check_value(res);
  return res->get_id();
}

uint64_t
ActionMkValue::run(Sort sort, const std::string& val)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
  reset_sat();
  Term res;
  res = d_solver.mk_value(sort, val);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  check_value(res);
  return res->get_id();
}

uint64_t
ActionMkValue::run(Sort sort, const std::string& val, size_t len)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\"";
  reset_sat();
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
ActionMkValue::run(Sort sort, const std::string& v0, const std::string& v1)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << v0 << "\""
               << " \"" << v1 << "\"";
  reset_sat();
  Term res = d_solver.mk_value(sort, v0, v1);
  d_smgr.add_value(res, sort, sort->get_kind());
  MURXLA_TRACE_RETURN << res;
  check_value(res);
  return res->get_id();
}

uint64_t
ActionMkValue::run(Sort sort, const std::string& val, Solver::Base base)
{
  MURXLA_TRACE << get_kind() << " " << sort << " \"" << val << "\""
               << " " << base;
  reset_sat();
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
  else if (term->is_ff())
  {
    MURXLA_TEST(term->is_ff_value());
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
ActionMkSpecialValue::generate(Sort sort)
{
  assert(d_solver.is_initialized());
  SortKind sort_kind         = sort->get_kind();
  const auto& special_values = d_solver.get_special_values(sort_kind);
  assert(!special_values.empty());
  run(sort,
      d_rng.pick_from_set<std::unordered_set<AbsTerm::SpecialValueKind>,
                          AbsTerm::SpecialValueKind>(special_values));
  return true;
}

bool
ActionMkSpecialValue::generate()
{
  /* Pick sort of value. */
  if (!d_smgr.has_sort(d_solver.get_special_values_sort_kinds())) return false;
  Sort sort = d_smgr.pick_sort(d_solver.get_special_values_sort_kinds(), false);
  return generate(sort);
}

std::vector<uint64_t>
ActionMkSpecialValue::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());

  uint64_t res = 0;
  Sort sort    = get_untraced_sort(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_SORT(sort, tokens[0]);
  const auto& special_vals = d_solver.get_special_values(sort->get_kind());

  std::string value = str_to_str(tokens[1]);
  MURXLA_CHECK_TRACE(!special_vals.empty()
                     && special_vals.find(value) != special_vals.end())
      << "unknown special value " << value << " of sort kind "
      << sort->get_kind();

  res = run(sort, value);

  return {res};
}

uint64_t
ActionMkSpecialValue::run(Sort sort, const AbsTerm::SpecialValueKind& val)
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

ActionInstantiateSort::ActionInstantiateSort(SolverManager& smgr)
    : Action(smgr, s_name, ID),
      d_exclude_sort_param_sort_kinds(
          smgr.get_profile().get_unsupported_sort_param_sort_kinds())
{
}

bool
ActionInstantiateSort::generate()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.has_sort_dt_parametric()) return false;
  if (!d_smgr.has_sort_excluding(d_exclude_sort_param_sort_kinds)) return false;
  Sort param_sort   = d_smgr.pick_sort_dt_param();
  size_t n_params   = param_sort->get_sorts().size();
  std::vector<Sort> sorts;
  for (size_t i = 0; i < n_params; ++i)
  {
    sorts.push_back(
        d_smgr.pick_sort_excluding(d_exclude_sort_param_sort_kinds));
  }
  run(param_sort, sorts);
  return true;
}

std::vector<uint64_t>
ActionInstantiateSort::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NOT_EMPTY(tokens);
  Sort param_sort = get_untraced_sort(untrace_str_to_id(tokens[0]));
  std::vector<Sort> sorts;
  for (size_t i = 1, n_tokens = tokens.size(); i < n_tokens; ++i)
  {
    sorts.push_back(get_untraced_sort(untrace_str_to_id(tokens[i])));
  }
  return {run(param_sort, sorts)->get_id()};
}

Sort
ActionInstantiateSort::run(Sort param_sort, const std::vector<Sort>& sorts)
{
  MURXLA_TRACE << get_kind() << " " << param_sort << sorts;
  std::unordered_map<Sort, std::vector<std::pair<std::vector<Sort>, Sort>>>
      cache;
  std::vector<std::pair<std::string, Sort>> to_trace;
  Sort res = run(param_sort, sorts, cache, to_trace);
  MURXLA_TRACE_RETURN << res;
  for (const auto& p : to_trace)
  {
    MURXLA_TRACE << p.first;
    MURXLA_TRACE_RETURN << p.second;
  }
  return res;
}

Sort
ActionInstantiateSort::run(
    Sort param_sort,
    const std::vector<Sort>& sorts,
    std::unordered_map<Sort, std::vector<std::pair<std::vector<Sort>, Sort>>>&
        cache,
    std::vector<std::pair<std::string, Sort>>& to_trace)
{
  Sort res = d_solver.instantiate_sort(param_sort, sorts);
  res->set_dt_is_instantiated(true);
  MURXLA_TEST(param_sort->is_dt_parametric());
  /* We temporarily set the ctors map to the map of param_sort in order to be
   * able to add the sort to the SolverManager. Will be updated after
   * instantiating and resolving unresolved sorts.  */
  res->set_dt_ctors(param_sort->get_dt_ctors());
  res->set_sorts(sorts);
  d_smgr.add_sort(
      res, param_sort->get_kind(), false, res->is_dt_well_founded());
  /* We need to reconstruct the instantiation of map AbsSort::d_dt_ctors. */
  auto ctors = param_sort->instantiate_dt_param_sort(sorts);
  /* Instantiate unresolved sorts. */
  cache[param_sort].emplace_back(sorts, res);
  for (auto& ctor : ctors)
  {
    auto& sels = ctor.second;
    for (auto& sel : sels)
    {
      Sort& ssort = sel.second;
      if (ssort && ssort->is_unresolved_sort())
      {
        Sort associated_sort = ssort->get_associated_sort();
        assert(associated_sort);
        const std::vector<Sort> inst_sorts = ssort->get_sorts();
        if (inst_sorts.size())
        {
          bool cached = false;
          auto it     = cache.find(associated_sort);
          if (it != cache.end())
          {
            for (const auto& v : it->second)
            {
              if (v.first == inst_sorts)
              {
                ssort  = v.second;
                cached = true;
                break;
              }
            }
          }
          if (!cached)
          {
            ssort = run(associated_sort, inst_sorts, cache, to_trace);
            assert(ssort->get_id());
            cache[associated_sort].emplace_back(inst_sorts, ssort);
            std::stringstream ss;
            ss << get_kind() << " " << associated_sort << inst_sorts;
            to_trace.emplace_back(ss.str(), ssort);
          }
        }
        else
        {
          ssort = associated_sort;
        }
      }
    }
  }
  /* Update with the instantiated, resolved ctors map. */
  res->set_dt_ctors(ctors);
  return res;
}

/* -------------------------------------------------------------------------- */

//! [docs-action-assertformula-generate start]
bool
ActionAssertFormula::generate()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.has_term(SORT_BOOL, 0)) return false;
  Term assertion = d_smgr.pick_term(SORT_BOOL, 0);

  run(assertion);
  return true;
}
//! [docs-action-assertformula-generate end]

//! [docs-action-assertformula-untrace start]
std::vector<uint64_t>
ActionAssertFormula::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
  Term t = get_untraced_term(untrace_str_to_id(tokens[0]));
  MURXLA_CHECK_TRACE_TERM(t, tokens[0]);
  run(t);
  return {};
}
//! [docs-action-assertformula-untrace end]

//! [docs-action-assertformula-run start]
void
ActionAssertFormula::run(Term assertion)
{
  MURXLA_TRACE << get_kind() << " " << assertion;
  reset_sat();
  d_solver.assert_formula(assertion);
}
//! [docs-action-assertformula-run end]

/* -------------------------------------------------------------------------- */

bool
ActionCheckSat::generate()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_incremental && d_smgr.d_n_sat_calls > 0)
  {
    d_disable = true;
    return false;
  }
  /* Only call action immediately again with low priority. */
  if (d_smgr.d_sat_called && d_rng.pick_with_prob(95)) return false;
  run();
  return true;
}

std::vector<uint64_t>
ActionCheckSat::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  run();
  return {};
}

void
ActionCheckSat::run()
{
  MURXLA_TRACE << get_kind();
  reset_sat();
  d_smgr.report_result(d_solver.check_sat());
}

/* -------------------------------------------------------------------------- */

bool
ActionCheckSatAssuming::generate()
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
  run(assumptions);
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
    auto id     = untrace_str_to_id(tokens[idx]);
    Term t      = get_untraced_term(id);
    MURXLA_CHECK_TRACE_TERM(t, id);
    assumptions.push_back(t);
  }
  run(assumptions);
  return {};
}

void
ActionCheckSatAssuming::run(const std::vector<Term>& assumptions)
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
ActionGetUnsatAssumptions::generate()
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
  run();
  return true;
}

std::vector<uint64_t>
ActionGetUnsatAssumptions::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  run();
  return {};
}

void
ActionGetUnsatAssumptions::run()
{
  MURXLA_TRACE << get_kind();
  /* Note: Unsat assumptions are checked in the checker solver. */
  (void) d_solver.get_unsat_assumptions();
}

/* -------------------------------------------------------------------------- */

bool
ActionGetUnsatCore::generate()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_unsat_cores)
  {
    d_disable = true;
    return false;
  }
  if (!d_smgr.d_sat_called) return false;
  if (d_smgr.d_sat_result != Solver::Result::UNSAT) return false;
  run();
  return true;
}

std::vector<uint64_t>
ActionGetUnsatCore::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  run();
  return {};
}

void
ActionGetUnsatCore::run()
{
  MURXLA_TRACE << get_kind();
  /* Note: The Terms in this vector are solver terms wrapped into Term,
   *       without sort information! */
  std::vector<Term> res = d_solver.get_unsat_core();
}

/* -------------------------------------------------------------------------- */

ActionGetValue::ActionGetValue(SolverManager& smgr)
    : Action(smgr, s_name, NONE),
      d_exclude_sort_kinds(
          smgr.get_profile().get_unsupported_get_value_sort_kinds())
{
}

bool
ActionGetValue::generate()
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
  if (!d_smgr.has_sort_excluding(0, d_exclude_sort_kinds)) return false;
  for (uint32_t i = 0; i < n_terms; ++i)
  {
    SortKind sort_kind = d_smgr.pick_sort_kind(0, d_exclude_sort_kinds);
    terms.push_back(d_smgr.pick_term(sort_kind, 0));
  }
  run(terms);
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
    auto id     = untrace_str_to_id(tokens[idx]);
    Term t      = get_untraced_term(id);
    MURXLA_CHECK_TRACE_TERM(t, id);
    terms.push_back(t);
  }
  run(terms);
  return {};
}

void
ActionGetValue::run(const std::vector<Term>& terms)
{
  MURXLA_TRACE << get_kind() << " " << terms.size() << terms;
  /* Note: The Terms in this vector are solver terms wrapped into Term,
   *       without sort information! */
  (void) d_solver.get_value(terms);
}

/* -------------------------------------------------------------------------- */

bool
ActionPush::generate()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_incremental)
  {
    d_disable = true;
    return false;
  }
  uint32_t n_levels = d_rng.pick<uint32_t>(1, MURXLA_MAX_N_PUSH_LEVELS);
  run(n_levels);
  return true;
}

std::vector<uint64_t>
ActionPush::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
  uint32_t n_levels = str_to_uint32(tokens[0]);
  run(n_levels);
  return {};
}

void
ActionPush::run(uint32_t n_levels)
{
  MURXLA_TRACE << get_kind() << " " << n_levels;
  reset_sat();
  d_solver.push(n_levels);
  d_smgr.d_n_push_levels += n_levels;
}

/* -------------------------------------------------------------------------- */

bool
ActionPop::generate()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_incremental)
  {
    d_disable = true;
    return false;
  }
  if (d_smgr.d_n_push_levels == 0) return false;
  uint32_t n_levels = d_rng.pick<uint32_t>(1, d_smgr.d_n_push_levels);
  run(n_levels);
  return true;
}

std::vector<uint64_t>
ActionPop::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
  uint32_t n_levels = str_to_uint32(tokens[0]);
  run(n_levels);
  return {};
}

void
ActionPop::run(uint32_t n_levels)
{
  MURXLA_TRACE << get_kind() << " " << n_levels;
  reset_sat();
  d_solver.pop(n_levels);
  d_smgr.d_n_push_levels -= n_levels;
}

/* -------------------------------------------------------------------------- */

bool
ActionReset::generate()
{
  assert(d_solver.is_initialized());
  run();
  return true;
}

std::vector<uint64_t>
ActionReset::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  run();
  return {};
}

void
ActionReset::run()
{
  MURXLA_TRACE << get_kind();
  d_smgr.reset();
  d_solver.reset();
}

/* -------------------------------------------------------------------------- */

bool
ActionResetAssertions::generate()
{
  assert(d_solver.is_initialized());
  run();
  return true;
}

std::vector<uint64_t>
ActionResetAssertions::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  run();
  return {};
}

void
ActionResetAssertions::run()
{
  MURXLA_TRACE << get_kind();
  reset_sat();
  d_solver.reset_assertions();
  d_smgr.d_n_push_levels = 0;
}

/* -------------------------------------------------------------------------- */

bool
ActionPrintModel::generate()
{
  assert(d_solver.is_initialized());
  if (!d_smgr.d_model_gen)
  {
    d_disable = true;
    return false;
  }
  if (!d_smgr.d_sat_called) return false;
  if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
  run();
  return true;
}

std::vector<uint64_t>
ActionPrintModel::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_EMPTY(tokens);
  run();
  return {};
}

void
ActionPrintModel::run()
{
  MURXLA_TRACE << get_kind();
  d_solver.print_model();
}

/* -------------------------------------------------------------------------- */

ActionMkFun::ActionMkFun(SolverManager& smgr)
    : Action(smgr, s_name, ID),
      d_mkterm(smgr),
      d_mkvar(smgr),
      d_exclude_fun_domain_sort_kinds(
          smgr.get_profile().get_unsupported_fun_domain_sort_kinds()),
      d_exclude_fun_codomain_sort_kinds(
          smgr.get_profile().get_unsupported_fun_codomain_sort_kinds())
{
}

bool
ActionMkFun::generate()
{
  /* Avoid creating functions with quantified variables in the body. */
  if (d_smgr.get_num_vars() > 0) return false;
  if (!d_smgr.has_sort_excluding(d_exclude_fun_domain_sort_kinds, false)
      || !d_smgr.has_sort_excluding(d_exclude_fun_codomain_sort_kinds, false))
  {
    return false;
  }

  SortKindSet exclude(d_exclude_fun_domain_sort_kinds.begin(),
                      d_exclude_fun_domain_sort_kinds.end());
  exclude.insert(d_exclude_fun_codomain_sort_kinds.begin(),
                 d_exclude_fun_codomain_sort_kinds.end());

  if (!d_smgr.has_sort_excluding(exclude, false))
  {
    return false;
  }

  std::string name = d_smgr.pick_symbol("_f");

  /* Pick at least one sort that is supported as domain and codomain so that we
   * can always pick a function body (in the worst-case it's just the argument
   * with the supported sort). */
  std::vector<Sort> sorts;
  uint32_t nsorts = d_rng.pick(0, MURXLA_MK_FUN_MAX_ARGS - 1);
  for (uint32_t i = 0; i < nsorts; ++i)
  {
    sorts.push_back(
        d_smgr.pick_sort_excluding(d_exclude_fun_domain_sort_kinds, false));
  }
  Sort codomain_sort = d_smgr.pick_sort_excluding(exclude, false);
  auto it            = sorts.begin();
  if (!sorts.empty())
  {
    std::advance(it, d_rng.pick<size_t>() % sorts.size());
  }
  sorts.insert(it, codomain_sort);

  uint64_t id;
  std::vector<Term> args;
  size_t i = 0;
  for (const auto& s : sorts)
  {
    std::stringstream ss;
    ss << name << "_" << i++;
    id = d_mkvar.run(s, ss.str())[0];
    args.push_back(d_smgr.get_term(id));
  }

  /* Skip operator kinds that would bind variables created above. */
  OpKindSet skip_op_kinds = {
      Op::DT_MATCH, Op::FORALL, Op::EXISTS, Op::SET_COMPREHENSION};

  uint32_t nterms = d_rng.pick<uint32_t>(1, MURXLA_MK_FUN_MAX_TERMS);
  size_t ncreated = 0;
  for (uint32_t i = 0; i < nterms; ++i)
  {
    Op::Kind op_kind = d_smgr.pick_op_kind(true, codomain_sort->get_kind());
    if (op_kind == Op::UNDEFINED)
    {
      break;
    }
    if (skip_op_kinds.find(op_kind) != skip_op_kinds.end())
    {
      continue;
    }
    d_mkterm.generate(op_kind);
    ncreated++;
  }

  // Make sure to pick a term that is in the scope of this function.
  size_t min_level = d_smgr.get_num_vars() - args.size() + 1;
  Term body        = d_smgr.pick_term_min_level(codomain_sort, min_level);
  run(name, args, body);
  return true;
}

std::vector<uint64_t>
ActionMkFun::untrace(const std::vector<std::string>& tokens)
{
  MURXLA_CHECK_TRACE_NTOKENS_MIN(
      4, " (name, number of arguments, body) ", tokens.size());

  const std::string& name = str_to_str(tokens[0]);
  uint32_t n_args         = str_to_uint32(tokens[1]);

  uint64_t id;
  std::vector<Term> args;
  for (uint32_t i = 0; i < n_args; ++i)
  {
    id     = untrace_str_to_id(tokens[2 + i]);
    Term t = get_untraced_term(id);
    MURXLA_CHECK_TRACE_TERM(t, id);
    args.push_back(t);
  }

  id        = untrace_str_to_id(tokens[2 + n_args]);
  Term body = get_untraced_term(id);

  return run(name, args, body);
}

std::vector<uint64_t>
ActionMkFun::run(const std::string& name,
                 const std::vector<Term>& args,
                 Term body)
{
  MURXLA_TRACE << get_kind() << " \"" << name << "\" " << args.size() << args
               << " " << body;

  // Pop variables beginning with top scope.
  for (auto it = args.rbegin(); it != args.rend(); ++it)
  {
    d_smgr.remove_var(*it);
  }

  // Create expected function sort instead of querying the solver in order to
  // get the full sort information of the domain and codomain.
  std::vector<Sort> sorts;
  for (const auto& t : args)
  {
    sorts.push_back(t->get_sort());
  }
  sorts.push_back(body->get_sort());
  Sort s = d_solver.mk_sort(SORT_FUN, sorts);
  s->set_sorts(sorts);

  // Create function and set sort.
  Term res = d_solver.mk_fun(name, args, body);
  // We don't perform this check for now until the SMT2 solver can correctly
  // handle this case.
  // MURXLA_TEST(d_solver.get_sort(res, SORT_FUN)->equals(s));
  res->set_sort(s);

  std::vector<Term> term_args(args.begin(), args.end());
  term_args.push_back(body);
  d_smgr.add_term(res, SORT_FUN, term_args);
  Sort res_sort = res->get_sort();

  MURXLA_TRACE_RETURN << res << " " << res_sort;
  return {res->get_id(), res_sort->get_id()};
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla
