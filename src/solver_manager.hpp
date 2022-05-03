/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__SOLVER_MANAGER_H
#define __MURXLA__SOLVER_MANAGER_H

#include <cassert>
#include <iostream>
#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "solver/solver.hpp"
#include "solver/solver_profile.hpp"
#include "solver_option.hpp"
#include "sort.hpp"
#include "term_db.hpp"
#include "theory.hpp"
#include "util.hpp"

namespace murxla {

namespace statistics {
struct Statistics;
}

/* -------------------------------------------------------------------------- */

class SolverManager
{
  friend class FSM;
  friend class DD;

 public:
  using SortSet = std::unordered_set<Sort>;

  /* Statistics. */
  struct Stats
  {
    uint32_t inputs = 0; /* values, constants */
    uint32_t vars   = 0; /* variables */
    uint32_t terms  = 0; /* all terms, including inputs */
    uint32_t sorts  = 0; /* all sorts */
  };


  /* Constructor. */
  SolverManager(Solver* solver,
                SolverProfile& solver_profile,
                RNGenerator& rng,
                SolverSeedGenerator& sng,
                std::ostream& trace,
                SolverOptions& options,
                bool arith_linear,
                bool simple_symbols,
                statistics::Statistics* stats,
                const TheoryVector& enabled_theories,
                const TheorySet& disabled_theories);
  ~SolverManager() = default;

  /**
   * Clear all data.
   */
  void clear();

  /**
   * Get solver.
   * @return A reference to the solver (wrapper) instance.
   */
  Solver& get_solver();

  /**
   * Get the associated global random number generator.
   * @return A reference to the RNG instance.
   */
  RNGenerator& get_rng() const;

  /**
   * Get the associated solver seed generator.
   * @return A reference to the solver seed generator instance.
   */
  SolverSeedGenerator& get_sng();

  /**
   * Get set of enabled theories.
   * @return The set of currently enabled theories.
   */
  const TheorySet& get_enabled_theories() const;

  /**
   * Get a reference to the trace stream.
   * @return A reference to the trace stream.
   */
  std::ostream& get_trace();

  /**
   * Mark given option as already configured.
   * @param opt The option to mark.
   */
  void mark_option_used(const std::string& opt);

  /**
   * Get the number of created terms in the top scope.
   * @return the number of created terms in the current top scope.
   */
  uint64_t get_num_terms_max_level() const;

  /**
   * Get the number of available variables.
   * @return The number of available variables.
   */
  size_t get_num_vars() const;

  /**
   * Add sort to sort database.
   *
   * Parametric sorts are not added to the main database (the database that we
   * pick sorts from), but to a separate database that we only pick from
   * when we explicitly need parametric sorts (see pick_sort_dt_param()).
   *
   * We only add well founded sorts. A sort that is not well founded gets an
   * id to trace the return statement of mk-sort, but is otherwise discarded.
   *
   * @param sort The sort to add to the databse.
   * @param sort_kind The kind of the sort.
   * @param parametric True if given sort has parameter sorts.
   * @param well_founded True if fiven sort is well founded.
   */
  void add_sort(Sort& sort,
                SortKind sort_kind,
                bool parametric   = false,
                bool well_founded = true);

  /**
   * Add value to term database.
   * @param term The term to add to the database.
   * @param sort The sort of the term to add.
   * @param sort_kind The sort of the sort of the term to add.
   * @param value_kind The kind of the special value,
   *                   AbsTerm::SPECIAL_VALUE_NONE if given term is not a
   *                   special value.
   *
   */
  void add_value(Term& term,
                 Sort& sort,
                 SortKind sort_kind,
                 const AbsTerm::SpecialValueKind& value_kind =
                     AbsTerm::SPECIAL_VALUE_NONE);
  /**
   * Add string value of length 1.
   * @param term A term representing a string value of length 1.
   */
  void add_string_char_value(Term& term);
  /**
   * Add input to term database.
   * @param term A term representing an input.
   * @param sort The sort of the term.
   * @param sort_kind The sort of the sort of the term.
   */
  void add_input(Term& term, Sort& sort, SortKind sort_kind);
  /**
   * Add var to term database.
   * @param term A term representing a variable.
   * @param sort The sort of the term.
   */
  void add_var(Term& term, Sort& sort, SortKind sort_kind);
  /**
   * Add const to term database.
   * @param term A term representing a constant.
   * @param sort The sort of the term.
   * @param sort_kind The kind of the sort of the term.
   */
  void add_const(Term& term, Sort& sort, SortKind sort_kind);
  /**
   * Add non-input term to term database.
   * @param term A term representing anything other than an input
   * @param sort_kind The kind of the sort of the term.
   * @param args The argument terms to the given term.
   */
  void add_term(Term& term,
                SortKind sort_kind,
                const std::vector<Term>& args = {});

  /**
   * Pick arbitrary symbol (simple or piped).
   * Simple symbols are generated as `<prefix><id>`.
   * @param prefix The prefix of the symbol.
   * @return An arbitrary symbol.
   */
  std::string pick_symbol(const std::string& prefix = "_x");

  /**
   * Pick sort kind of existing (= created) sort.
   *
   * Optionally restrict selection to sort kinds with terms only if
   * `with_terms` is true.
   *
   * @note This excludes parametric datatype sorts.
   *
   * @param with_terms True to only pick sort kinds of a sort for which we have
   *                   already created terms.
   * @return The sort kind.
   */
  SortKind pick_sort_kind(bool with_terms = true);
  /**
   * Pick sort kind of existing (= created) sort out of given set of sort
   * kinds.  Asserts that a sort of any of the given kinds exists.
   *
   * Optionally restrict selection to sort kinds with terms only if
   * `with_terms` is true.
   *
   * @note This excludes parametric datatype sorts.
   *
   * @param sort_kinds The set of sort kinds to pick from.
   * @param with_terms True to only pick sort kinds of a sort for which we have
   *                   already created terms.
   * @return The sort kind.
   */
  SortKind pick_sort_kind(const SortKindSet& sort_kinds,
                          bool with_terms = true);
  /**
   * Pick a sort kind of existing (= created) sort, excluding the given sort
   * kinds.
   *
   * Optionally restrict selection to sort kinds with terms only if
   * `with_terms` is true.
   *
   * @note This excludes parametric datatype sorts.
   *
   * @param exclude_sort_kinds The sort kinds to exclude.
   * @param with_terms True to only pick sort kinds of a sort for which we have
   *                   already created terms.
   * @return The sort kind.
   */
  SortKind pick_sort_kind_excluding(const SortKindSet& exclude_sort_kinds,
                                    bool with_terms = true) const;

  /**
   * Pick sort kind of existing (= created) sort with terms at given level.
   *
   * Optionally, exclude given sort kinds.
   *
   * @note This excludes parametric datatype sorts.
   *
   * @param level The scope level of existing terms to pick the sort kind from.
   * @param exclude_sort_kinds The sort kinds to exclude.
   * @return The sort kind.
   */
  SortKind pick_sort_kind(uint32_t level,
                          const SortKindSet& exclude_sort_kinds);

  /**
   * Pick enabled sort kind (and get its data).
   *
   * Only sort kinds of enabled theories are picked.
   * This function does not guarantee that a sort of this kind alreay exists.
   *
   * @note This excludes parametric datatype sorts.
   *
   * @return The sort kind.
   */
  SortKindData& pick_sort_kind_data();
  /**
   * Pick enabled operator kind (and get its data).
   *
   * Optionally restricted to operator kinds that create terms of given sort
   * kind.
   *
   * Only operator kinds of enabled theories are picked.
   *
   * @param with_terms True to only pick operator kinds of already created
   *                   terms.
   * @param The sort kind of terms of the operator kind to select.
   * @return The operator kind.
   */
  Op::Kind pick_op_kind(bool with_terms = true, SortKind sort_kind = SORT_ANY);

  /**
   * Get the Op data for given operator kind.
   * @param kind The operator kind.
   * @return The configuration data of the operator.
   */
  Op& get_op(const Op::Kind& kind);

  /**
   * Pick a value of any sort.
   *
   * @note Requires that a value of any sort exists.
   *
   * @return The value.
   */
  Term pick_value();

  /**
   * Pick a value of given sort.
   *
   * @note Requires that a value of given sort exists.
   *
   * @param sort The sort of the value to pick.
   * @return The value.
   */
  Term pick_value(Sort sort);

  /**
   * Pick string value with length 1.
   * @return A term representing a string value of length 1.
   */
  Term pick_string_char_value();

  /**
   * Pick a term of given sort.
   * @note Requires that terms of this sort exist.
   * @param sort The sort of the term to pick.
   * @return The term.
   */
  Term pick_term(Sort sort);
  /**
   * Pick term of given sort kind and scope level.
   * @note Requires that terms of this sort kind exist.
   * @param sort_kind The kind of the sort of the term to pick.
   * @param level The scope level of the term to pick.
   * @return The term.
   */
  Term pick_term(SortKind sort_kind, size_t level);
  /**
   * Pick term of given sort kind.
   * @note Requires that terms of this sort kind exist.
   * @param sort_kind The kind of the sort of the term to pick.
   * @return The term.
   */
  Term pick_term(SortKind sort_kind);
  /**
   * Pick any term.
   * @note Requires that terms of any sort kind exist.
   * @return The term.
   */
  Term pick_term();
  /**
   * Pick any term from given level.
   * @note Requires that terms of any sort kind exist.
   * @param level The scope level of the term to pick.
   * @return The term.
   */
  Term pick_term(size_t level);

  /**
   * Pick any term from any level from the given level to the max level.
   * @note Requires that terms of any sort kind exist.
   * @param level The scope level of the term to pick.
   * @return The term.
   */
  Term pick_term_min_level(Sort sort, size_t level);

  /**
   * Pick function term with given domain sorts.
   * @note Requires that such terms exist.
   * @param domain_sorts The sorts of the domain of the function to pick.
   * @return A term representing a function.
   */
  Term pick_fun(const std::vector<Sort>& domain_sorts);

  /**
   * Pick variable from current scope level.
   * @note Requires that a variable exists.
   * @return A term representing a variable.
   */
  Term pick_var();
  /**
   * Pick `num_vars` variables.
   * @note Requires that at least `num_vars` variables exist.
   * @param num_vars The number of variables to pick.
   * @return A vector with the picked variables.
   */
  std::vector<Term> pick_vars(size_t num_vars) const;

  /**
   * Remove variable from current scope level.
   * @note Must be called before calling add_term.
   * @param var The variable to remove.
   */
  void remove_var(const Term& var);

  /**
   * Pick Boolean term from current scope level.
   * @return The term.
   */
  Term pick_quant_body();

  /**
   * Pick term of any sort from current scope level.
   * @return The term.
   */
  Term pick_quant_term();

  /**
   * Pick term of given sort from current scope level.
   * @return The term.
   */
  Term pick_quant_term(Sort sort);

  /**
   * Add given term to the set of currently assumed assumptions.
   * @param t The assumption to cache.
   */
  void add_assumption(Term t);

  /**
   * Pick assumption out of the set of currently assumed assumptions.
   * @note Requires that d_assumptions is not empty.
   * @return A term representing an assumptions.
   */
  Term pick_assumed_assumption();

  /** Reset solver manager state into start mode. */
  void reset();

  /**
   * Reset solver manager state into assert mode.
   *
   * After this call, calling
   *   - get_unsat_assumptions()
   *   - get_unsat_core() and
   * is not possible until after the next SAT call.
   */
  void reset_sat();

  /**
   * Determine if term database contains any value of any sort.
   * @return True if term database contains any value of any sort.
   */
  bool has_value() const;

  /**
   * Determine if term database contains any value of given sort.
   * @return True if term database contains any value of given sort.
   */
  bool has_value(Sort sort) const;

  /**
   * Determine if we already created string values with length 1.
   * @return True if we already created string values with length 1.
   */
  bool has_string_char_value() const;

  /**
   * Determine if term database contains any term.
   * @return True if term database contains any term.
   */
  bool has_term() const;
  /**
   * Determine if term database contains any term on given level.
   * @param level The scope level to query for terms.
   * @return True if term database contains any term on given level.
   */
  bool has_term(size_t level) const;
  /**
   * Determine if term database contains any term of given sort kind at given
   * level.
   * @param sort_kind The sort kind of the terms to query for.
   * @param level The scope level to query for terms.
   * @return True if term database contains any term of given sort kind at
   *         given level.
   */
  bool has_term(SortKind sort_kind, size_t level) const;
  /**
   * Determine if term database contains any term of given sort kind.
   * @param sort_kind The sort kind of the terms to query for.
   * @return true if term database contains any term of given sort kind.
   */
  bool has_term(SortKind sort_kind) const;
  /**
   * Determine if term database contains any term of one of the given sort
   * kinds.
   * @param sort_kind The sort kind of the terms to query for.
   * @return True if term database contains any term of one of the given sort
   *         kinds.
   */
  bool has_term(const SortKindSet& sort_kinds) const;
  /**
   * Determine if term database contains any term of given sort.
   * @param sort The sort of the terms to query for.
   * @return true if term database contains any term of given sort.
   */
  bool has_term(Sort sort) const;
  /**
   * Determine if d_assumptions is not empty.
   * @return True if d_assumptions is not empty.
   */
  bool has_assumed() const;
  /**
   * Determine if term database contains a function term with given domain
   * sorts.
   * @param domain_sorts The domain sorts of the function to query for.
   * @return True if term database contains a function term with given domain
   *         sorts.
   */
  bool has_fun(const std::vector<Sort>& domain_sorts) const;
  /**
   * Determine if term database contains a variable.
   * @return true if term database contains a variable.
   */
  bool has_var() const;
  /**
   * Determine if term database contains a variable and a Boolean term in the
   * current scope level.
   * @return True if term database contains a variable and a Boolean term in the
   *         current scope level.
   */
  bool has_quant_body() const;
  /**
   * Determine if term database contains a variable and a term of any sort in
   * the current scope level.
   * @return True if term database contains a variable and a term of any sort in
   *         the current scope level.
   */
  bool has_quant_term() const;
  /**
   * Determine if term database contains a variable and a term of given sort
   * in the current scope level.
   * @return True if term database contains a variable and a term of given sort
   *         in the current scope level.
   */
  bool has_quant_term(Sort sort) const;

  /**
   * Find the Term in the Term database that wraps the same solver term
   * with the given sort and sort kind.
   *
   * @note We need this for Terms returned by the solver that are only wrapped
   *       solver terms without sort information.
   *
   * @return A nullptr if given Term is not in the term database.
   *
   */
  Term find_term(Term term, Sort sort, SortKind sort_kind);

  /**
   * Get the term with the given id.
   * @param id The id of the term.
   * @return The term with the given id.
   */
  Term get_term(uint64_t id) const;

  /**
   * Get the untraced term with the given id.
   * @param id The id of the term.
   * @return The untraced term with the given id.
   */
  Term get_untraced_term(uint64_t id) const;

  /**
   * Pick sort.
   *
   * It is not guaranteed that there exist terms of the returned sort.
   *
   * @note This excludes parametric datatype sorts.
   * @return The sort.
   */
  Sort pick_sort();
  /**
   * Pick sort that has sort parameters.
   *
   * It is not guaranteed that there exist terms of the returned sort.
   *
   * @note This includes (parametric) datatype sorts.
   * @return The sort.
   */
  Sort pick_sort_with_sort_params();
  /**
   * Pick sort of given sort kind.
   *
   * Optionally restrict selection to sorts with terms only if `with_terms` is
   * true.
   *
   * @note This excludes parametric datatype sorts.
   * @param sort_kind The sort_kind of the sort to pick.
   * @param with_terms True to restrict to sorts with already created terms.
   * @return The sort.
   */
  Sort pick_sort(SortKind sort_kind, bool with_terms = true);
  /**
   * Pick sort of any of the given sort kinds.
   *
   * Optionally restrict selection to sorts with terms only if `with_terms` is
   * true.
   *
   * @param sort_kinds The set of sort kinds to pick from.
   * @param with_terms True to restrict to sorts with already created terms.
   * @return This excludes parametric datatype sorts.
   */
  Sort pick_sort(const SortKindSet& sort_kinds, bool with_terms = true);
  /**
   * Pick sort, excluding sorts of kinds included in `exclude_sort_kinds`.
   *
   * It is not guaranteed that there exist terms of the returned sort.
   *
   * @param exclude_sort_kinds The sort kinds to exclude.
   * @param with_terms True to restrict to sorts with already created terms.
   * @return This excludes parametric datatype sorts.
   */
  Sort pick_sort_excluding(const SortKindSet& exclude_sort_kinds,
                           bool with_terms = true);
  /**
   * Pick bit-vector sort with given bit-width.
   *
   * Optionally restrict selection to sorts with terms only if `with_terms` is
   * true.
   *
   * @param bw The bit-width of the bit-vector sort to pick.
   * @param with_terms True to restrict to sorts with already created terms.
   * @return The sort.
   */
  Sort pick_sort_bv(uint32_t bw, bool with_terms = true);
  /**
   * Pick bit-vector sort with given maximum bit-width.
   *
   * Optionally restrict selection to sorts with terms only if `with_terms` is
   * true.
   *
   * @param bw_max The maximum bit-width (incl.) of the bit-vector sort to pick.
   * @param with_terms True to restrict to sorts with already created terms.
   * @return The sort.
   */
  Sort pick_sort_bv_max(uint32_t bw_max, bool with_terms = true);

  /**
   * Pick parametric datatypes sort.
   * @return The sort.
   */
  Sort pick_sort_dt_param();

  /**
   * Determine if any sort has been created.
   *
   * This does not guarantee that any terms have been created.
   *
   * @note This excludes parametric datatype sorts.
   * @return True if any sort has been created.
   */
  bool has_sort() const;
  /**
   * Determine if a sort of given kind exists.
   *
   * This does not guarantee that any terms of this sort have been created.
   *
   * @note This excludes parametric datatype sorts.
   * @param sort_kind The sort kind to check for created sorts.
   * @return True if a sort of given kind exists.
   */
  bool has_sort(SortKind sort_kind) const;
  /**
   * Determine if a sort of any of the given kinds exists.
   *
   * This does not guarantee that any terms of these sorts have been created.
   *
   * @note This excludes parametric datatype sorts.
   * @param sort_kinds The sort kinds to check for created sorts.
   * @return True if a sort of any of the given kinds exists.
   */
  bool has_sort(const SortKindSet& sort_kinds) const;
  /**
   * Determine if given sort already exists.
   *
   * This does not guarantee that any terms of this sort have been created.
   *
   * @return sort The sort to query for.
   * @return True if given sort already exists.
   */
  bool has_sort(Sort sort) const;
  /**
   * Determine if sorts of a kind other than the kinds given in
   * exclude_sort_kinds have been created.
   *
   * Optionally restrict selection to sorts with terms only if `with_terms` is
   * true.
   *
   * @note This excludes parametric datatype sorts.
   * @param exclude_sort_kinds The sort kinds to exclude.
   * @param with_terms True to restrict to sorts with already created terms.
   * @return True if sort of a kind other than the given kinds have been
   *         created.
   */
  bool has_sort_excluding(
      const std::unordered_set<SortKind>& exclude_sort_kinds,
      bool with_terms = true) const;

  /**
   * Determine if terms with sorts of a kind other than the kinds given in
   * `exclude_sort_kinds` at the given scope level have been created.
   * @param level The scope level.
   * @param exclude_sort_kinds The sort kinds to exclude.
   * @return True if terms with sorts of a kind other than the kinds given in
   *         `exclude_sort_kinds` have been created.
   */
  bool has_sort_excluding(
      uint32_t level,
      const std::unordered_set<SortKind>& exclude_sort_kinds) const;

  /**
   * Determine if sorts that have sort parameters have been created.
   * @note This includes non-parametric datatypes.
   * @return True if sorts that have sort parameters have been created.
   */
  bool has_sort_with_sort_params() const;

  /**
   * Determine if a bit-vector sort with given bit-width exists.
   *
   * Optionally restrict selection to sorts with terms only if `with_terms` is
   * true.
   *
   * @return True if a bit-vector sort with given bit-width exists.
   */
  bool has_sort_bv(uint32_t bw, bool with_terms = true) const;
  /**
   * Determine if a bit-vector sort up to given maximum bit-width exists.
   *
   * Optionally restrict selection to sorts with terms only if `with_terms` is
   * true.
   *
   * @return True if a bit-vector sort up to given maximum bit-width exists.
   */
  bool has_sort_bv_max(uint32_t bw_max, bool with_terms = true) const;

  /**
   * Determine if a parametric datatypes sort exists.
   * @return True if a parametric datatypes sort exists.
   */
  bool has_sort_dt_parametric() const;

  /**
   * Get the untraced sort with the given id.
   * @return The untraced sort with the given id.
   */
  Sort get_untraced_sort(uint64_t id) const;

  /**
   * Find a matching sort for the given sort in the sort database `d_sorts`.
   * @param sort The sort to find.
   * @return The sort cached in `d_sorts`, if found, else the given sort.
   */
  Sort find_sort(Sort sort) const;

  /**
   * Pick an option and an option value.
   *
   * If either are given, enforce option or value. If no option or the given
   * option / value can be set, return empty pair.
   *
   * @param name The option name.
   * @param value The option value.
   * @return A pair of picked option name and value.
   */
  std::pair<std::string, std::string> pick_option(std::string name  = "",
                                                  std::string value = "");

  /** Clear cached set of assumptions. */
  void clear_assumptions();

  /**
   * Add solver option.
   * @param opt The solver option to add.
   */
  void add_option(SolverOption* opt);

  /**
   * Report solver result to solver manager.
   * @param res The solver result.
   */
  void report_result(Solver::Result res);

  /**
   * Get the currently configured solver profile.
   * @return The solver profile.
   */
  SolverProfile& get_profile();

  /** Statistics. */
  Stats d_stats;

  /* Config -----------------------------------------------------------------
   *
   * Config members are not cleared or reset on reset() / clear().
   */

  /** True to restrict arithmetic operators to linear fragment. */
  bool d_arith_linear = false;

  /**
   * True if all symbols for terms should be of the form '_sX' rather than
   * a random string.
   */
  bool d_simple_symbols = false;

  /* Solver (config) state --------------------------------------------------
   *
   *  All members below are reset / cleared on reset().
   *  All members that are data structures are cleared on clear().
   */

  /**
   * True if incremental solving is enabled.
   * (SMT-LIB: option :incremental).
   */
  bool d_incremental = false;
  /**
   * True if model generation is enabled.
   * (SMT-LIB: option :produce-models).
   */
  bool d_model_gen = false;
  /**
   * True if producing unsat assumptions is enabled.
   * (SMT-LIB: option :produce-unsat-assumptions).
   */
  bool d_unsat_assumptions = false;
  /**
   * True if producing unsat cores is enabled.
   * (SMT-LIB: option :produce-unsat-cores).
   */
  bool d_unsat_cores = false;

  /** The number of scope levels previously pushed. */
  uint32_t d_n_push_levels = 0;

  /**
   * True if a previous check-sat call is still "active", i.e., if no formulas
   * have been asserted or assumed since.
   * While true it is save to check failed assumptions and query model values.
   */
  bool d_sat_called = false;

  /** The result of the previous sat call. */
  Solver::Result d_sat_result = Solver::Result::UNKNOWN;

  /** The number of check-sat calls issued. */
  uint32_t d_n_sat_calls = 0;

  /* Statistics ------------------------------------------------------------- */

  /** A pointer to the murxla-level statistics object. */
  statistics::Statistics* d_mbt_stats;

 private:
  /**
   * Remove theory from set of enabled theories.
   * @param theory The theory to disable.
   */
  void disable_theory(Theory theory);

  /**
   * Finalize initialization of SolverManager. Configures sort kinds,
   * operators, etc. based on currently configured theories.
   * @param smtlib_compliant True to configure for only smt-lib compliant API
   *                         call sequences.
   */
  void initialize(bool smtlib_compliant);

  /**
   * Return true if given option has already been configured.
   * @param opt The option to query.
   * @return True if the given option has already been configure.
   */
  bool is_option_used(const std::string& opt);

  /**
   * Get sort kind data for specified theories.
   * @param theories The set of enabled theories.
   * @return A map from SortKind to SortKindData for all enabled theories.
   */
  static SortKindMap get_sort_kind_data(const TheorySet& theories);

  /**
   * Get options required for a given theory.
   * @param theory The theory.
   * @return A map of options required to be configured for the given theory,
   *         maps option name to option value.
   */
  std::unordered_map<std::string, std::string> get_required_options(
      Theory theory) const;

  /**
   * Remove all solver options that do not match the strings provided in filter.
   * @param filter A comma separated list of (partial) option names that should
   *               be considered for option fuzzing. Names can start
   *               with ^ to indicate that the option name must start with the
   *               given prefix.
   */
  void filter_solver_options(const std::string& filter);

  /**
   * Reset op caches used by pick_op_kind;
   */
  void reset_op_cache();

  /**
   * Pick any of the enabled theories.
   * @param with_terms True to only pick theories with already created terms.
   * @return The theory.
   */
  Theory pick_theory(bool with_terms = true);

  /* Untracing only --------------------------------------------------------- */

  /**
   * Map an id from a trace to an actual term ID.
   * @note Only used for untracing.
   * @param untrace_id The id of the term in the replayed trace.
   * @param term_id The id of the term.
   */
  void register_term(uint64_t untraced_id, uint64_t term_id);

  /**
   * Map an id from a trace to an actual sort ID.
   * @note Only used for untracing.
   * @param untrace_id The id of the term in the replayed trace.
   * @param term_id The id of the term.
   * @return False if a sort with the given id does not exist.
   */
  bool register_sort(uint64_t untraced_id, uint64_t sort_id);

  /**
   * Set the sort id counter to id.
   * @note Only used for untracing.
   * @param id The id.
   */
  void set_n_sorts(uint64_t id);

  /**
   * Determine and populate set of enabled theories.
   *
   * All theories supported by a solvers are by default enabled and can
   * optionally be disabled.
   *
   * @param enabled_theories The set of theories to enable.
   * @param disabled_theories The set of theories to disable.
   */
  void add_enabled_theories(const TheoryVector& enabled_theories,
                            const TheorySet& disabled_theories);

  /**
   * Populate sort kinds database with enabled sort kinds.
   *
   * Sort kinds are enabled based on the set of enabled theories.
   */
  void add_sort_kinds();

#if 0
  template <typename TKind,
            typename TKindData,
            typename TKindMap,
            typename TKindVector>
  TKindData& pick_kind(TKindMap& map,
                       TKindVector* kinds1,
                       TKindVector* kinds2 = nullptr);
#endif

  /** Generalized helper to pick a sort or operator kind. */
  template <typename TKind,
            typename TKindData,
            typename TKindMap>
  TKindData& pick_kind(TKindMap& map);

  /**
   * The activated solver.
   * No calls to the API of the underlying solver are issued from the solver
   * manager, only calls to the API of the murxla::Solver object.
   */
  std::unique_ptr<Solver> d_solver;

  /**
   * The associated global random number generator.
   * Not to be confused with the RNG maintained and used by the solver, which
   * is independent from the global RNG.
   */
  RNGenerator& d_rng;

  /**
   * The associated solver seed generator.
   * Responsible for generating seeds to be used to seed the random generator
   * of the solver.
   */
  SolverSeedGenerator& d_sng;

  /** The stream to capture the API trace. */
  std::ostream& d_trace;

  /** Config ----------------------------------------------------------------
   *
   * Config members are not cleared or reset on reset() / clear().
   */

  /** The set of enabled sort kinds. Maps SortKind to SortKindData. */
  SortKindMap d_sort_kinds;
  /** The Op::Kind manager. */
  std::unique_ptr<OpKindManager> d_opmgr;

  /** The set of enabled theories. */
  TheorySet d_enabled_theories;

  /** Map of available solver options */
  SolverOptions& d_solver_options;

  /** Solver state ----------------------------------------------------------
   *
   *  All members below are reset / cleared on reset().
   *  All data members that are are cleared on clear().
   */

  /** The solver options that have already been configured. */
  std::unordered_set<std::string> d_used_solver_options;

  /** Sort id counter. */
  uint64_t d_n_sorts = 0;

  /** Counter to create simple symbol names when option is enabled. */
  uint32_t d_n_symbols = 0;

  /** Solver state data members -------------------- */

  /**
   * Maintain all created sorts, excluding not yet instantiated parametric
   * datatype sorts.
   */
  SortSet d_sorts;
  /**
   * Maintain parametric, not yet instantizted datatype sorts.
   *
   * We have to maintain these separately, since they can only be picked/used
   * after having been instantiated. Instantiated parametric datatype sorts
   * are maintained in d_sorts.
   */
  SortSet d_sorts_dt_parametric;
  /**
   * Cache non-well-founded sorts.
   * We do not use these sorts but need to cache them for untracing.
   */
  SortSet d_sorts_dt_non_well_founded;

  /** Map sort kind -> sorts. */
  std::unordered_map<SortKind, SortSet> d_sort_kind_to_sorts;

  /** The set of already assumed formulas. */
  std::unordered_set<Term> d_assumptions;

  /** Term database */
  TermDb d_term_db;

  /** Set of currently created string values with length 1. */
  std::unordered_set<Term> d_string_char_values;

  /** Map untraced ids to corresponding Terms. */
  std::unordered_map<uint64_t, Term> d_untraced_terms;

  /** Map untraced ids to corresponding Sorts. */
  std::unordered_map<uint64_t, Sort> d_untraced_sorts;

  /**
   * Cache used by pick_op_kind. Caches operator kinds that are currently
   * safe to pick since the required terms to create an operator already exist.
   */
  std::unordered_map<Theory, OpKindSet> d_enabled_op_kinds;

  /**
   * Cache used by pick_op_kind. Caches available operator kinds reported
   * by opmgr, but cannot be constructed yet due to missing terms.
   */
  OpKindMap d_available_op_kinds;

  /** Is this solver manager already initialized? */
  bool d_initialized = false;

  /** A reference to the currently configured solver profile. */
  SolverProfile& d_profile;
};

/* -------------------------------------------------------------------------- */

}  // namespace murxla
#endif
