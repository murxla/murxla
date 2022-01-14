#include "solver_manager.hpp"

#include <algorithm>
#include <cstring>
#include <iterator>
#include <sstream>

#include "config.hpp"
#include "except.hpp"
#include "statistics.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

SolverManager::SolverManager(Solver* solver,
                             RNGenerator& rng,
                             SolverSeedGenerator& sng,
                             std::ostream& trace,
                             SolverOptions& options,
                             bool arith_subtyping,
                             bool arith_linear,
                             bool trace_seeds,
                             bool simple_symbols,
                             statistics::Statistics* stats,
                             const TheoryIdVector& enabled_theories,
                             const TheoryIdSet& disabled_theories)
    : d_mbt_stats(stats),
      d_arith_subtyping(arith_subtyping),
      d_arith_linear(arith_linear),
      d_trace_seeds(trace_seeds),
      d_simple_symbols(simple_symbols),
      d_solver(solver),
      d_rng(rng),
      d_sng(sng),
      d_trace(trace),
      d_solver_options(options),
      d_used_solver_options(),
      d_term_db(*this, rng),
      d_untraced_terms(),
      d_untraced_sorts()
{
  add_enabled_theories(enabled_theories, disabled_theories);
}

/* -------------------------------------------------------------------------- */

void
SolverManager::initialize()
{
  assert(!d_initialized);
  add_sort_kinds();  // adds only sort kinds of enabled theories
  d_opmgr.reset(new OpKindManager(d_enabled_theories,
                                  d_sort_kinds,
                                  d_solver->get_unsupported_op_kinds(),
                                  d_solver->get_unsupported_op_sort_kinds(),
                                  d_arith_linear,
                                  d_mbt_stats));
  d_solver->configure_smgr(this);
  d_solver->configure_opmgr(d_opmgr.get());
  reset_op_cache();
  d_initialized = true;
}

/* -------------------------------------------------------------------------- */

void
SolverManager::clear()
{
  d_used_solver_options.clear();
  d_sorts.clear();
  d_sorts_dt_parametric.clear();
  d_sorts_dt_non_well_founded.clear();
  d_sort_kind_to_sorts.clear();
  d_assumptions.clear();
  d_term_db.clear();
  d_string_char_values.clear();
  d_untraced_terms.clear();
  d_untraced_sorts.clear();
  reset_op_cache();
}

void
SolverManager::reset_op_cache()
{
  const auto& kinds = d_opmgr->get_op_kinds();
  d_available_op_kinds.insert(kinds.begin(), kinds.end());
  d_enabled_op_kinds.clear();
}

/* -------------------------------------------------------------------------- */

Solver&
SolverManager::get_solver()
{
  assert(d_initialized);
  return *d_solver.get();
}

/* -------------------------------------------------------------------------- */

RNGenerator&
SolverManager::get_rng() const
{
  return d_rng;
}

SolverSeedGenerator&
SolverManager::get_sng()
{
  return d_sng;
}

/* -------------------------------------------------------------------------- */

std::string
SolverManager::trace_seed() const
{
  std::stringstream ss;
  ss << "set-seed " << d_rng.get_engine() << std::endl;
  return ss.str();
}

std::ostream&
SolverManager::get_trace()
{
  return d_trace;
}

/* -------------------------------------------------------------------------- */

const TheoryIdSet&
SolverManager::get_enabled_theories() const
{
  return d_enabled_theories;
}

void
SolverManager::disable_theory(TheoryId theory)
{
  auto it = d_enabled_theories.find(theory);
  if (it == d_enabled_theories.end()) return;
  d_enabled_theories.erase(it);
}

/* -------------------------------------------------------------------------- */

bool
SolverManager::is_option_used(const std::string& opt)
{
  return d_used_solver_options.find(opt) != d_used_solver_options.end();
}

void
SolverManager::mark_option_used(const std::string& opt)
{
  d_used_solver_options.insert(opt);
}

/* -------------------------------------------------------------------------- */

uint64_t
SolverManager::get_num_terms_max_level() const
{
  return d_term_db.get_num_terms(d_term_db.max_level());
}

uint32_t
SolverManager::get_num_vars() const
{
  return d_term_db.get_num_vars();
}

/* -------------------------------------------------------------------------- */

void
SolverManager::add_value(Term& term,
                         Sort& sort,
                         SortKind sort_kind,
                         const AbsTerm::SpecialValueKind& value_kind)
{
  assert(term.get());

  add_input(term, sort, sort_kind);
  term->set_leaf_kind(AbsTerm::LeafKind::VALUE);
  term->set_special_value_kind(value_kind);
}

void
SolverManager::add_string_char_value(Term& term)
{
  assert(term.get());
  d_string_char_values.insert(term);
}

void
SolverManager::add_input(Term& term, Sort& sort, SortKind sort_kind)
{
  assert(term.get());

  d_stats.inputs += 1;
  d_term_db.add_input(term, sort, sort_kind);
}

void
SolverManager::add_var(Term& term, Sort& sort, SortKind sort_kind)
{
  assert(term.get());

  d_stats.vars += 1;
  d_term_db.add_var(term, sort, sort_kind);
  term->set_leaf_kind(AbsTerm::LeafKind::VARIABLE);
}

void
SolverManager::add_const(Term& term, Sort& sort, SortKind sort_kind)
{
  assert(term.get());

  d_stats.vars += 1;
  d_term_db.add_input(term, sort, sort_kind);
  term->set_leaf_kind(AbsTerm::LeafKind::CONSTANT);
}

void
SolverManager::add_term(Term& term,
                        SortKind sort_kind,
                        const std::vector<Term>& args)
{
  d_stats.terms += 1;
  /* Query solver for sort of newly created term if term does not have a sort.
   * If the returned sort is not in d_sorts, i.e., sort == nullptr, we need to
   * do a lookup on d_sorts if we already have a matching sort. */
  Sort sort = term->get_sort();
  if (sort == nullptr)
  {
    sort = d_solver->get_sort(term, sort_kind);
  }

  /* If sort_kind is SORT_REAL, given sort can only be an Int sort when the
   * solver identifies it as an Int sort (since Int may be a subtype of Real).
   * We don't infer this based on the arguments but delegate this inference
   * to the solver. We always store terms of sort Int under sort kind SORT_INT,
   * even if they were created from a Real operator (and thus, the expected
   * sort kind sort_kind = SORT_REAL).  */
  if (sort_kind == SORT_REAL && sort->is_int())
  {
    sort_kind = SORT_INT;
  }

  sort->set_kind(sort_kind);
  /* If no matching sort is found, we use the sort returned by the solver. */
  Sort lookup = find_sort(sort);
  assert(lookup->equals(sort));
  /* Operators SEQ_UNIT, SET_UNIT and SET_COMPREHENSION may implicitly create a
   * new sequence sort. In that case we have to populate Sort::d_sorts with the
   * element sort. */
  assert(d_enabled_theories.find(THEORY_SEQ) == d_enabled_theories.end()
         || term->get_kind() != Op::UNDEFINED);
  const Op::Kind kind = term->get_kind();
  if ((kind == Op::BAG_TO_SET || kind == Op::BAG_FROM_SET
       || kind == Op::BAG_MAKE || kind == Op::BAG_MAP || kind == Op::SEQ_UNIT
       || kind == Op::SET_SINGLETON || kind == Op::SET_COMPREHENSION)
      && args.size() > 0)
  {
    auto sorts = lookup->get_sorts();
    if (sorts.size() == 0)
    {
      if (kind == Op::SET_COMPREHENSION)
      {
        lookup->set_sorts({args[1]->get_sort()});
      }
      else if (kind == Op::BAG_TO_SET || kind == Op::BAG_FROM_SET)
      {
        const auto& s = args[0]->get_sort()->get_sorts();
        assert(s.size() == 1);
        lookup->set_sorts({s[0]});
      }
      else if (kind == Op::BAG_MAP)
      {
        const auto& s = args[1]->get_sort()->get_sorts();
        assert(s.size() == 2);
        lookup->set_sorts({s[1]});
      }
      else
      {
        lookup->set_sorts({args[0]->get_sort()});
      }
    }
  }
  d_term_db.add_term(term, lookup, sort_kind, args);
  assert(lookup->get_id());
  assert(lookup->get_kind() != SORT_ANY);
  assert(!lookup->is_dt() || !lookup->get_dt_ctor_names().empty());
  assert(sort_kind != SORT_SEQ
         || (lookup->get_sorts().size() == 1
             && lookup->get_sorts()[0]->get_kind() != SORT_ANY));
  assert(sort_kind != SORT_SET
         || (lookup->get_sorts().size() == 1
             && lookup->get_sorts()[0]->get_kind() != SORT_ANY));
}

void
SolverManager::add_sort(Sort& sort,
                        SortKind sort_kind,
                        bool parametric,
                        bool well_founded)
{
  assert(sort.get());
  assert(sort_kind != SORT_ANY);

  if (sort->get_kind() == SORT_ANY)
  {
    assert(sort->get_id() == 0);
    sort->set_kind(sort_kind);
  }
  assert((sort_kind != SORT_INT && sort->get_kind() != SORT_INT)
         || sort->is_int());
  assert((d_arith_subtyping && sort_kind == SORT_REAL
          && sort->get_kind() == SORT_INT)
         || (d_arith_subtyping && sort_kind == SORT_INT
             && sort->get_kind() == SORT_REAL)
         || (sort_kind == SORT_BOOL && sort->get_kind() == SORT_BV
             && sort->get_bv_size() == 1)
         || (sort_kind == SORT_BV && sort->get_kind() == SORT_BOOL)
         || sort->get_kind() == sort_kind);

  SortSet& sorts = well_founded ? (parametric ? d_sorts_dt_parametric : d_sorts)
                                : d_sorts_dt_non_well_founded;

  auto it = sorts.find(sort);
  if (it == sorts.end())
  {
    sort->set_id(++d_n_sorts);
    sorts.insert(sort);
    ++d_stats.sorts;
  }
  else
  {
    sort = *it;
    assert((sort_kind != SORT_INT && sort->get_kind() != SORT_INT)
           || sort->is_int());
    assert((d_arith_subtyping && sort_kind == SORT_REAL
            && sort->get_kind() == SORT_INT)
           || (d_arith_subtyping && sort_kind == SORT_INT
               && sort->get_kind() == SORT_REAL)
           || (sort_kind == SORT_BOOL && sort->get_kind() == SORT_BV
               && sort->get_bv_size() == 1)
           || (sort_kind == SORT_BV && sort->get_kind() == SORT_BOOL)
           || (sort_kind == SORT_ARRAY && sort->get_kind() == SORT_FUN
               && sort->get_sorts().size() == 2)
           || (sort_kind == SORT_FUN && sort->get_kind() == SORT_ARRAY
               && sort->get_sorts().size() == 2)
           || sort->get_kind() == sort_kind);
  }
  assert(sort->get_kind() != SORT_ANY);
  assert(sort_kind != SORT_ARRAY
         || (sort->get_sorts().size() == 2
             && sort->get_sorts()[0]->get_kind() != SORT_ANY
             && sort->get_sorts()[1]->get_kind() != SORT_ANY));
  assert(sort->get_id());
  assert(!sort->is_dt() || !sort->get_dt_ctor_names().empty());

  /* We do not add parametric datatype sorts here. These should never be
   * picked for anything except instantiating the sort (see
   * pick_sort_dt_param()). */
  if (!parametric && well_founded)
  {
    auto& sorts_of_kind = d_sort_kind_to_sorts[sort_kind];
    if (sorts_of_kind.find(sort) == sorts_of_kind.end())
    {
      sorts_of_kind.insert(sort);
    }
  }
}

/* -------------------------------------------------------------------------- */

SortKind
SolverManager::pick_sort_kind(bool with_terms)
{
  assert(!d_sort_kind_to_sorts.empty());
  if (with_terms)
  {
    return d_term_db.pick_sort_kind();
  }
  return d_rng.pick_from_map<std::unordered_map<SortKind, SortSet>, SortKind>(
      d_sort_kind_to_sorts);
}

SortKind
SolverManager::pick_sort_kind(const SortKindSet& sort_kinds, bool with_terms)
{
  assert(has_sort(sort_kinds));
  if (with_terms)
  {
    return d_term_db.pick_sort_kind(sort_kinds);
  }

  if (sort_kinds.size() == 1)
  {
    return *sort_kinds.begin();
  }
  SortKindVector skinds;
  for (SortKind sk : sort_kinds)
  {
    if (has_sort(sk)) skinds.push_back(sk);
  }
  return d_rng.pick_from_set<decltype(skinds), SortKind>(skinds);
}

SortKind
SolverManager::pick_sort_kind_excluding(const SortKindSet& exclude_sort_kinds,
                                        bool with_terms) const
{
  assert(has_sort_excluding(exclude_sort_kinds));
  if (with_terms)
  {
    return d_term_db.pick_sort_kind_excluding(exclude_sort_kinds);
  }
  std::vector<SortKind> skinds;
  for (const auto& s : d_sorts)
  {
    SortKind sk = s->get_kind();
    if (exclude_sort_kinds.find(sk) == exclude_sort_kinds.end())
    {
      skinds.push_back(sk);
    }
  }
  return d_rng.pick_from_set<decltype(skinds), SortKind>(skinds);
}

SortKind
SolverManager::pick_sort_kind(uint32_t level,
                              const SortKindSet& exclude_sort_kinds)
{
  return d_term_db.pick_sort_kind(level, exclude_sort_kinds);
}

SortKindData&
SolverManager::pick_sort_kind_data()
{
  return pick_kind<SortKind, SortKindData, SortKindMap>(d_sort_kinds);
}

Op::Kind
SolverManager::pick_op_kind(bool with_terms, SortKind sort_kind)
{
  if (with_terms)
  {
    std::unordered_map<TheoryId, OpKindSet> kinds(d_enabled_op_kinds);
    std::vector<Op::Kind> remove;
    for (const auto& [kind, op] : d_available_op_kinds)
    {
      /* Quantifiers can only be created if we already have variables and
       * Boolean terms in the current scope. */
      if ((op.d_kind == Op::FORALL || op.d_kind == Op::EXISTS
           || op.d_kind == Op::SET_COMPREHENSION)
          && (!d_term_db.has_var() || !d_term_db.has_quant_body()
              || (d_term_db.get_num_terms(d_term_db.max_level())
                  < MURXLA_MIN_N_QUANT_TERMS)))
      {
        continue;
      }

      bool has_terms = true;

      /* Check if we already have terms that can be used with this operator. */
      if (op.d_arity < 0)
      {
        has_terms = has_term(op.get_arg_sort_kind(0));
      }
      else
      {
        for (int32_t i = 0; i < op.d_arity; ++i)
        {
          if (!has_term(op.get_arg_sort_kind(i)))
          {
            has_terms = false;
            break;
          }
        }
      }
      if (has_terms)
      {
        /* In general if a term was added to the term db it will always be
         * available. However, for quantifiers, terms get "consumed" and
         * therefore we always have to check whether we can create a quantified
         * term and therefore the FORALL and EXISTS kinds can't be cached. */
        if (op.d_kind != Op::FORALL && op.d_kind != Op::EXISTS)
        {
          d_enabled_op_kinds[op.d_theory].insert(op.d_kind);
          remove.push_back(op.d_kind);
        }
        kinds[op.d_theory].insert(op.d_kind);
      }
    }

    /* Remove the enabled kinds from d_available_op_kinds since these kinds now
     * can be constructed with terms in the db. */
    for (const auto& k : remove)
    {
      d_available_op_kinds.erase(k);
    }

    /* Filter operator kinds based on sort kind. */
    if (sort_kind != SORT_ANY)
    {
      const auto& enabled_ops = d_opmgr->get_op_kinds();
      for (const auto& [kind, op] : enabled_ops)
      {
        if (op.d_sort_kinds.find(sort_kind) == op.d_sort_kinds.end())
        {
          const auto it = kinds.find(op.d_theory);
          if (it != kinds.end())
          {
            it->second.erase(kind);
            if (it->second.empty())
            {
              kinds.erase(op.d_theory);
            }
          }
        }
      }
    }

    if (kinds.size() > 0)
    {
      /* First pick theory and then operator kind (avoids bias against theories
       * with many operators). However, we pick THEORY_BOOL and THEORY_ALL with
       * lower probability (10% each) to generate more theory terms. */

      bool have_bool  = kinds.find(THEORY_BOOL) != kinds.end();
      bool have_all   = kinds.find(THEORY_ALL) != kinds.end();
      size_t min_size = have_all ? 1 : 0;
      uint32_t prob   = have_all ? 900 : 1000;
      if (have_bool)
      {
        min_size += 1;
        prob -= 100;
      }

      TheoryId theory = THEORY_ALL;
      if (kinds.size() > min_size && d_rng.pick_with_prob(prob))
      {
        do
        {
          theory = d_rng.pick_from_map<decltype(kinds), TheoryId>(kinds);
        } while (theory == THEORY_ALL || theory == THEORY_BOOL);
      }
      else if (have_bool && d_rng.flip_coin())
      {
        theory = THEORY_BOOL;
      }

      auto& op_kinds  = kinds[theory];
      return d_rng.pick_from_set<decltype(op_kinds), Op::Kind>(op_kinds);
    }

    /* We cannot create any operation with the current set of terms. */
    return Op::UNDEFINED;
  }

  if (sort_kind == SORT_ANY)
  {
    return d_rng.pick_from_map<OpKindMap, Op::Kind>(d_opmgr->get_op_kinds());
  }

  std::vector<Op::Kind> kinds;
  const auto& enabled_ops = d_opmgr->get_op_kinds();
  for (const auto& op : enabled_ops)
  {
    if (op.second.d_sort_kinds.find(sort_kind) != op.second.d_sort_kinds.end())
    {
      kinds.push_back(op.first);
    }
  }
  return d_rng.pick_from_set<decltype(kinds), Op::Kind>(kinds);
}

Op&
SolverManager::get_op(const Op::Kind& kind)
{
  return d_opmgr->get_op(kind);
}

/* -------------------------------------------------------------------------- */

bool
SolverManager::has_theory(bool with_terms)
{
  if (with_terms)
  {
    return has_term() && (!has_term(SORT_RM) || has_term(SORT_FP));
  }
  return d_enabled_theories.size() > 0;
}

TheoryId
SolverManager::pick_theory(bool with_terms)
{
  if (with_terms)
  {
    TheoryIdSet theories;
    for (uint32_t i = 0; i < static_cast<uint32_t>(SORT_ANY); ++i)
    {
      SortKind sort_kind = static_cast<SortKind>(i);

      /* We have to skip SORT_RM since all operators in THEORY_FP require
       * terms of SORT_FP, but not necessarily of SORT_RM. If only terms of
       * SORT_RM have been created, no THEORY_FP operator applies. */
      if (sort_kind == SORT_RM) continue;

      if (has_term(sort_kind))
      {
        TheoryId theory = d_sort_kinds.find(sort_kind)->second.d_theory;
        assert(d_enabled_theories.find(theory) != d_enabled_theories.end());
        theories.insert(theory);
      }
    }
    return d_rng.pick_from_set<decltype(theories), TheoryId>(theories);
  }
  return d_rng.pick_from_set<decltype(d_enabled_theories), TheoryId>(
      d_enabled_theories);
}

/* -------------------------------------------------------------------------- */

Term
SolverManager::pick_value()
{
  return d_term_db.pick_value();
}

Term
SolverManager::pick_value(Sort sort)
{
  return d_term_db.pick_value(sort);
}

Term
SolverManager::pick_string_char_value()
{
  assert(has_string_char_value());
  return d_rng.pick_from_set<decltype(d_string_char_values), Term>(
      d_string_char_values);
}

Term
SolverManager::pick_term(Sort sort)
{
  return d_term_db.pick_term(sort);
}

Term
SolverManager::pick_term(SortKind sort_kind, size_t level)
{
  return d_term_db.pick_term(sort_kind, level);
}

Term
SolverManager::pick_term(SortKind sort_kind)
{
  return d_term_db.pick_term(sort_kind);
}

Term
SolverManager::pick_term()
{
  return d_term_db.pick_term();
}

Term
SolverManager::pick_term(size_t level)
{
  return d_term_db.pick_term(level);
}

Term
SolverManager::pick_fun(const std::vector<Sort>& sorts)
{
  return d_term_db.pick_fun(sorts);
}

Term
SolverManager::pick_var()
{
  return d_term_db.pick_var();
}

std::vector<Term>
SolverManager::pick_vars(uint32_t num_vars) const
{
  return d_term_db.pick_vars(num_vars);
}

void
SolverManager::remove_var(const Term& var)
{
  d_term_db.remove_var(var);
  reset_op_cache();
}

Term
SolverManager::pick_quant_body()
{
  return d_term_db.pick_quant_body();
}

Term
SolverManager::pick_quant_term()
{
  return d_term_db.pick_quant_term();
}

Term
SolverManager::pick_quant_term(Sort sort)
{
  return d_term_db.pick_quant_term(sort);
}

void
SolverManager::add_assumption(Term t)
{
  d_assumptions.insert(t);
}

Term
SolverManager::pick_assumed_assumption()
{
  assert(has_assumed());
  return d_rng.pick_from_set<decltype(d_assumptions), Term>(d_assumptions);
}

void
SolverManager::clear_assumptions()
{
  d_assumptions.clear();
}

void
SolverManager::reset()
{
  clear();
  d_term_db.reset();

  d_incremental       = false;
  d_model_gen         = false;
  d_unsat_assumptions = false;
  d_unsat_cores       = false;
  d_n_push_levels     = 0;
  d_sat_called        = false;
  d_sat_result        = Solver::Result::UNKNOWN;
  d_n_sat_calls       = 0;
  d_n_sorts           = 0;
  d_n_symbols         = 0;
}

void
SolverManager::add_option(SolverOption* opt)
{
  d_solver_options.emplace(opt->get_name(), opt);
}

void
SolverManager::report_result(Solver::Result res)
{
  d_sat_result = res;
  d_sat_called = true;
  ++d_n_sat_calls;
  ++d_mbt_stats->d_results[res];
}

std::unordered_map<std::string, std::string>
SolverManager::get_required_options(TheoryId theory) const
{
  return d_solver->get_required_options(theory);
}

void
SolverManager::filter_solver_options(const std::string& filter)
{
  if (filter.empty())
  {
    return;
  }

  auto filters = split(filter, ',');
  std::vector<std::string> options;

  bool remove;
  for (const auto& p : d_solver_options)
  {
    const std::string& opt = p.first;
    remove                 = true;
    for (const auto& f : filters)
    {
      assert(!f.empty());
      /* Option name must start with f. */
      if (f[0] == '^')
      {
        std::string ff(f.begin() + 1, f.end());
        remove = opt.find(ff) != 0;
      }
      /* Option name contains f. */
      else
      {
        remove = opt.find(f) == std::string::npos;
      }
      if (!remove)
      {
        break;
      }
    }
    if (remove)
    {
      options.push_back(opt);
    }
  }

  for (const auto& opt : options)
  {
    d_solver_options.erase(opt);
  }
}

void
SolverManager::reset_sat()
{
  if (d_sat_called)
  {
    clear_assumptions();
  }
  d_sat_called = false;
}

bool
SolverManager::has_value() const
{
  return d_term_db.has_value();
}

bool
SolverManager::has_value(Sort sort) const
{
  return d_term_db.has_value(sort);
}

bool
SolverManager::has_string_char_value() const
{
  return !d_string_char_values.empty();
}

bool
SolverManager::has_term() const
{
  return d_term_db.has_term();
}

bool
SolverManager::has_term(SortKind sort_kind, size_t level) const
{
  return d_term_db.has_term(sort_kind, level);
}

bool
SolverManager::has_term(SortKind sort_kind) const
{
  return d_term_db.has_term(sort_kind);
}

bool
SolverManager::has_term(const SortKindSet& sort_kinds) const
{
  return d_term_db.has_term(sort_kinds);
}

bool
SolverManager::has_term(Sort sort) const
{
  return d_term_db.has_term(sort);
}

bool
SolverManager::has_assumed() const
{
  return !d_assumptions.empty();
}

bool
SolverManager::has_fun(const std::vector<Sort>& sorts) const
{
  return d_term_db.has_fun(sorts);
}

bool
SolverManager::has_var() const
{
  return d_term_db.has_var();
}

bool
SolverManager::has_quant_body() const
{
  return d_term_db.has_quant_body();
}

bool
SolverManager::has_quant_term() const
{
  return d_term_db.has_quant_term();
}

bool
SolverManager::has_quant_term(Sort sort) const
{
  return d_term_db.has_quant_term(sort);
}

Term
SolverManager::find_term(Term term, Sort sort, SortKind sort_kind)
{
  return d_term_db.find(term, sort, sort_kind);
}

Term
SolverManager::get_term(uint64_t id) const
{
  return d_term_db.get_term(id);
}

Term
SolverManager::get_untraced_term(uint64_t id) const
{
  auto it = d_untraced_terms.find(id);
  if (it != d_untraced_terms.end()) return it->second;
  return nullptr;
}

void
SolverManager::register_term(uint64_t untraced_id, uint64_t term_id)
{
  Term term = d_term_db.get_term(term_id);

  // If we already have a term with given 'id' we don't register the term.
  if (d_untraced_terms.find(untraced_id) != d_untraced_terms.end())
  {
    Term t = get_untraced_term(untraced_id);
    assert(t->get_sort() == term->get_sort());
    return;
  }
  d_untraced_terms.emplace(untraced_id, term);
}

bool
SolverManager::register_sort(uint64_t untraced_id, uint64_t sort_id)
{
  Sort sort;
  for (const auto& s : d_sorts)
  {
    if (s->get_id() == sort_id)
    {
      sort = s;
      break;
    }
  }
  if (!sort)
  {
    for (const auto& s : d_sorts_dt_parametric)
    {
      if (s->get_id() == sort_id)
      {
        sort = s;
        break;
      }
    }
  }
  if (!sort)
  {
    for (const auto& s : d_sorts_dt_non_well_founded)
    {
      if (s->get_id() == sort_id)
      {
        sort = s;
        break;
      }
    }
  }

  if (sort == nullptr) return false;

  // If we already have a sort with given 'id' we don't register the sort.
  if (d_untraced_sorts.find(untraced_id) != d_untraced_sorts.end())
  {
    Sort s = get_untraced_sort(untraced_id);
    assert(s == sort);
    return true;
  }
  d_untraced_sorts.emplace(untraced_id, sort);
  return true;
}

/* -------------------------------------------------------------------------- */

std::string
SolverManager::pick_symbol(const std::string& prefix)
{
  if (d_simple_symbols)
  {
    return prefix + std::to_string(d_n_symbols++);
  }
  uint32_t len = d_rng.pick<uint32_t>(0, MURXLA_SYMBOL_LEN_MAX);
  /* Pick piped vs simple symbol with 50% probability. */
  return len && d_rng.flip_coin() ? d_rng.pick_piped_symbol(len)
                                  : d_rng.pick_simple_symbol(len);
}

Sort
SolverManager::pick_sort()
{
  Sort res = d_rng.pick_from_set<decltype(d_sorts), Sort>(d_sorts);
  assert(res->get_id());
  return res;
}

Sort
SolverManager::pick_sort_with_sort_params()
{
  assert(has_sort_with_sort_params());

  std::vector<Sort> sorts{d_sorts_dt_parametric.begin(),
                          d_sorts_dt_parametric.end()};

  for (const auto& s : d_sorts)
  {
    if (s->is_dt() || !s->get_sorts().empty())
    {
      sorts.push_back(s);
    }
  }
  Sort res = d_rng.pick_from_set<decltype(sorts), Sort>(sorts);
  assert(res->get_id());
  return res;
}

Sort
SolverManager::pick_sort(SortKind sort_kind, bool with_terms)
{
  assert(!with_terms || has_term(sort_kind));
  if (sort_kind == SORT_ANY) sort_kind = pick_sort_kind(with_terms);

  Sort res;
  if (with_terms)
  {
    res = d_term_db.pick_sort(sort_kind);
  }
  else
  {
    assert(has_sort(sort_kind));
    res =
        d_rng.pick_from_set<SortSet, Sort>(d_sort_kind_to_sorts.at(sort_kind));
  }
  assert(res->get_id());
  assert(res->get_kind() != SORT_ANY);
  return res;
}

Sort
SolverManager::pick_sort(const SortKindSet& sort_kinds, bool with_terms)
{
  Sort res;
  if (with_terms)
  {
    res = d_term_db.pick_sort(sort_kinds);
  }
  else
  {
    assert(has_sort(sort_kinds));
    SortKind sk = pick_sort_kind(sort_kinds, with_terms);
    res = d_rng.pick_from_set<SortSet, Sort>(d_sort_kind_to_sorts.at(sk));
  }
  assert(res->get_id());
  return res;
}

Sort
SolverManager::pick_sort_excluding(const SortKindSet& exclude_sort_kinds,
                                   bool with_terms)
{
  assert(has_sort_excluding(exclude_sort_kinds, false));
  SortSet sorts;
  for (const auto& s : d_sorts)
  {
    if (exclude_sort_kinds.find(s->get_kind()) == exclude_sort_kinds.end())
    {
      if (!with_terms || d_term_db.has_term(s))
      {
        sorts.insert(s);
      }
    }
  }
  assert(!sorts.empty());
  Sort res = d_rng.pick_from_set<decltype(sorts), Sort>(sorts);
  assert(res->get_id());
  return res;
}

Sort
SolverManager::pick_sort_bv(uint32_t bw, bool with_terms)
{
  assert(has_sort_bv(bw, with_terms));
  const SortSet sorts = with_terms ? d_term_db.get_sorts() : d_sorts;
  for (const auto& sort : sorts)
  {
    if (sort->is_bv() && sort->get_bv_size() == bw)
    {
      assert(sort->get_id());
      return sort;
    }
  }
  assert(false);
  return nullptr;
}

Sort
SolverManager::pick_sort_bv_max(uint32_t bw_max, bool with_terms)
{
  assert(has_sort_bv_max(bw_max, with_terms));
  std::vector<Sort> bv_sorts;

  const SortSet sorts = with_terms ? d_term_db.get_sorts() : d_sorts;
  for (const auto& sort : sorts)
  {
    if (sort->is_bv() && sort->get_bv_size() <= bw_max)
    {
      bv_sorts.push_back(sort);
    }
  }
  assert(bv_sorts.size() > 0);
  Sort res = d_rng.pick_from_set<decltype(bv_sorts), Sort>(bv_sorts);
  assert(res->get_id());
  return res;
}

Sort
SolverManager::pick_sort_dt_param()
{
  return d_rng.pick_from_set<decltype(d_sorts_dt_parametric), Sort>(
      d_sorts_dt_parametric);
}

bool
SolverManager::has_sort() const
{
  return !d_sorts.empty();
}

bool
SolverManager::has_sort(SortKind sort_kind) const
{
  if (d_sort_kind_to_sorts.empty()) return false;
  if (sort_kind == SORT_ANY) return has_sort();
  if (d_sort_kinds.find(sort_kind) == d_sort_kinds.end()) return false;
  return d_sort_kind_to_sorts.find(sort_kind) != d_sort_kind_to_sorts.end()
         && !d_sort_kind_to_sorts.at(sort_kind).empty();
}

bool
SolverManager::has_sort(const SortKindSet& sort_kinds) const
{
  if (d_sort_kind_to_sorts.empty()) return false;

  for (SortKind sort_kind : sort_kinds)
  {
    if (d_sort_kinds.find(sort_kind) != d_sort_kinds.end()
        && d_sort_kind_to_sorts.find(sort_kind) != d_sort_kind_to_sorts.end()
        && !d_sort_kind_to_sorts.at(sort_kind).empty())
    {
      return true;
    }
  }
  return false;
}

bool
SolverManager::has_sort(Sort sort) const
{
  bool res = d_sorts.find(sort) != d_sorts.end();
  if (!res)
  {
    res = d_sorts_dt_parametric.find(sort) != d_sorts_dt_parametric.end();
  }
  return res;
}

bool
SolverManager::has_sort_excluding(
    const std::unordered_set<SortKind>& exclude_sort_kinds,
    bool with_terms) const
{
  const SortSet& sorts = with_terms ? d_term_db.get_sorts() : d_sorts;
  for (const auto& s : sorts)
  {
    if (exclude_sort_kinds.find(s->get_kind()) == exclude_sort_kinds.end())
    {
      return true;
    }
  }
  return false;
}

bool
SolverManager::has_sort_with_sort_params() const
{
  if (!d_sorts_dt_parametric.empty()) return true;

  for (const auto& s : d_sorts)
  {
    if (s->is_dt()) return true;
    if (!s->get_sorts().empty()) return true;
  }

  return false;
}

Sort
SolverManager::get_untraced_sort(uint64_t id) const
{
  auto it = d_untraced_sorts.find(id);
  if (it != d_untraced_sorts.end()) return it->second;
  return nullptr;
}

void
SolverManager::set_n_sorts(uint64_t id)
{
  d_n_sorts = id;
}

Sort
SolverManager::find_sort(Sort sort) const
{
  if (sort == nullptr) return sort;

  /* We can't use d_sorts::find() here since this uses operator==, which
   * also compares for equality of the kind of 'sort', which may be yet
   * unknown (SORT_ANY). */
  for (const auto& s : d_sorts)
  {
    /* If sort does have a sort kind, we have to compare the sort kinds too due
     * to the bool vs. bv1 handling in Bitwuzla and Boolector. */
    if (s->equals(sort)
        && (sort->get_kind() == SORT_ANY || s->get_kind() == sort->get_kind()))
      return s;
  }
  for (const auto& s : d_sorts_dt_parametric)
  {
    if (s->equals(sort)) return s;
  }
  for (const auto& s : d_sorts_dt_non_well_founded)
  {
    if (s->equals(sort)) return s;
  }
  return sort;
}

bool
SolverManager::has_sort_bv(uint32_t bw, bool with_terms) const
{
  const SortSet& sorts = with_terms ? d_term_db.get_sorts() : d_sorts;
  for (const auto& sort : sorts)
  {
    if (sort->is_bv() && sort->get_bv_size() == bw)
    {
      return true;
    }
  }
  return false;
}
bool
SolverManager::has_sort_bv_max(uint32_t bw_max, bool with_terms) const
{
  const SortSet sorts = with_terms ? d_term_db.get_sorts() : d_sorts;
  for (const auto& sort : sorts)
  {
    if (sort->is_bv() && sort->get_bv_size() <= bw_max)
    {
      return true;
    }
  }
  return false;
}

bool
SolverManager::has_sort_dt_parametric() const
{
  return !d_sorts_dt_parametric.empty();
}

std::pair<std::string, std::string>
SolverManager::pick_option(std::string name, std::string val)
{
  SolverOption* option = nullptr;

  if (name.empty())
  {
    /* No options to configure available. */
    if (d_solver_options.empty()) return std::make_pair("", "");

    std::vector<SolverOption*> available;
    bool skip;

    for (auto const& opt : d_solver_options)
    {
      option = opt.second.get();

      /* Filter out conflicting options */
      skip = false;
      for (auto conflict : option->get_conflicts())
      {
        if (is_option_used(conflict))
        {
          skip = true;
          break;
        }
      }
      if (skip) continue;

      /* Filter out options that depend on each other */
      for (auto depend : option->get_depends())
      {
        if (!is_option_used(depend))
        {
          skip = true;
          break;
        }
      }
      if (skip) continue;

      available.push_back(option);
    }

    option = available[d_rng.pick<uint32_t>() % available.size()];
    name   = option->get_name();
  }
  else
  {
    if (d_solver_options.find(name) != d_solver_options.end())
    {
      option = d_solver_options.at(name).get();
    }
  }

  /* Only configure not yet configured options. */
  if (is_option_used(name)) return std::make_pair("", "");

  mark_option_used(name);

  if (option && val.empty())
  {
    val = option->pick_value(d_rng);
  }
  assert(!val.empty());

  return std::make_pair(name, val);
}

/* -------------------------------------------------------------------------- */

void
SolverManager::add_enabled_theories(const TheoryIdVector& enabled_theories,
                                    const TheoryIdSet& disabled_theories)
{
  /* Get theories supported by enabled solver. */
  TheoryIdVector solver_theories = d_solver->get_supported_theories();

  /* Get all theories supported by MBT. */
  TheoryIdVector all_theories;
  if (enabled_theories.empty())
  {
    for (int32_t t = 0; t < THEORY_ALL; ++t)
    {
      all_theories.push_back(static_cast<TheoryId>(t));
    }
  }
  else
  {
    for (auto theory : enabled_theories)
    {
      all_theories.push_back(theory);
    }
    /* THEORY_BOOL is always enabled. */
    all_theories.push_back(THEORY_BOOL);
  }

  /* We need to sort these for intersection. */
  std::sort(all_theories.begin(), all_theories.end());
  std::sort(solver_theories.begin(), solver_theories.end());

  /* Filter out theories not supported by solver. */
  TheoryIdVector tmp(all_theories.size());
  auto it = std::set_intersection(all_theories.begin(),
                                  all_theories.end(),
                                  solver_theories.begin(),
                                  solver_theories.end(),
                                  tmp.begin());

  /* Resize to intersection size. */
  tmp.resize(it - tmp.begin());
  d_enabled_theories = TheoryIdSet(tmp.begin(), tmp.end());

  /* Remove disabled theories. */
  for (auto t : disabled_theories)
  {
    disable_theory(t);
  }
}

SortKindMap
SolverManager::get_sort_kind_data(const TheoryIdSet& theories)
{
  SortKindMap sort_kinds;
  for (TheoryId theory : theories)
  {
    switch (theory)
    {
      case THEORY_ARRAY:
        sort_kinds.emplace(SORT_ARRAY,
                           SortKindData(SORT_ARRAY, 2, THEORY_ARRAY));
        break;
      case THEORY_BAG:
        sort_kinds.emplace(SORT_BAG, SortKindData(SORT_BAG, 1, THEORY_BAG));
        break;
      case THEORY_BOOL:
        sort_kinds.emplace(SORT_BOOL, SortKindData(SORT_BOOL, 0, THEORY_BOOL));
        break;
      case THEORY_BV:
        sort_kinds.emplace(SORT_BV, SortKindData(SORT_BV, 0, THEORY_BV));
        break;
      case THEORY_DT:
        sort_kinds.emplace(SORT_DT, SortKindData(SORT_DT, 0, THEORY_DT));
        break;
      case THEORY_INT:
        sort_kinds.emplace(SORT_INT, SortKindData(SORT_INT, 0, THEORY_INT));
        break;
      case THEORY_REAL:
        sort_kinds.emplace(SORT_REAL, SortKindData(SORT_REAL, 0, THEORY_REAL));
        break;
      case THEORY_FP:
        sort_kinds.emplace(SORT_RM, SortKindData(SORT_RM, 0, THEORY_FP));
        sort_kinds.emplace(SORT_FP, SortKindData(SORT_FP, 0, THEORY_FP));
        break;

      case THEORY_QUANT: break;

      case THEORY_SEQ:
        sort_kinds.emplace(SORT_SEQ, SortKindData(SORT_SEQ, 1, THEORY_SEQ));
        break;

      case THEORY_SET:
        sort_kinds.emplace(SORT_SET, SortKindData(SORT_SET, 1, THEORY_SET));
        break;

      case THEORY_STRING:
        sort_kinds.emplace(SORT_STRING,
                           SortKindData(SORT_STRING, 0, THEORY_STRING));
        sort_kinds.emplace(SORT_REGLAN,
                           SortKindData(SORT_REGLAN, 0, THEORY_STRING));
        break;

      case THEORY_UF:
        sort_kinds.emplace(
            SORT_FUN, SortKindData(SORT_FUN, MURXLA_MK_TERM_N_ARGS, THEORY_UF));
        sort_kinds.emplace(SORT_UNINTERPRETED,
                           SortKindData(SORT_UNINTERPRETED, 0, THEORY_UF));
        break;

      default: assert(false);
    }
  }

  return sort_kinds;
}

void
SolverManager::add_sort_kinds()
{
  assert(d_enabled_theories.size());
  d_sort_kinds = get_sort_kind_data(d_enabled_theories);

  /* Remove sort kinds not supported by solver. */
  for (const auto& k : d_solver->get_unsupported_sort_kinds())
  {
    d_sort_kinds.erase(k);
  }
}

template <typename TKind, typename TKindData, typename TKindMap>
TKindData&
SolverManager::pick_kind(TKindMap& map)
{
  assert(!map.empty());
  typename TKindMap::iterator it = map.begin();
  std::advance(it, d_rng.pick<uint32_t>() % map.size());
  return it->second;
}

#if 0
template <typename TKind,
          typename TKindData,
          typename TKindMap,
          typename TKindVector>
TKindData&
SolverManager::pick_kind(TKindMap& map,
                         TKindVector* kinds1,
                         TKindVector* kinds2)
{
  assert(kinds1 || kinds2);
  size_t sz1 = kinds1 ? kinds1->size() : 0;
  size_t sz2 = kinds2 ? kinds2->size() : 0;
  uint32_t n = d_rng.pick<uint32_t>() % (sz1 + sz2);
  typename TKindVector::iterator it;

  assert(sz1 || sz2);
  if (sz2 == 0 || n < sz1)
  {
    assert(kinds1);
    it = kinds1->begin();
  }
  else
  {
    assert(kinds2);
    n -= sz1;
    it = kinds2->begin();
  }
  std::advance(it, n);
  TKind kind = *it;
  assert(map.find(kind) != map.end());
  return map.at(kind);
}
#endif

/* -------------------------------------------------------------------------- */

}  // namespace murxla
