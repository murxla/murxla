#ifndef __SMTMBT__SOLVER_MANAGER_H
#define __SMTMBT__SOLVER_MANAGER_H

#include <cassert>
#include <iostream>
#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "solver.hpp"
#include "solver_option.hpp"
#include "sort.hpp"
#include "statistics.hpp"
#include "theory.hpp"
#include "util.hpp"

#define SMTMBT_BW_MIN 1
#define SMTMBT_BW_MAX 128

namespace smtmbt {

/* -------------------------------------------------------------------------- */

class SolverManager
{
 public:
  using TermMap = std::unordered_map<Term, size_t, HashTerm>;
  using SortMap = std::unordered_map<Sort, TermMap, HashSort>;
  using SortSet = std::unordered_set<Sort, HashSort>;

  /* Statistics. */
  struct Stats
  {
    uint32_t inputs = 0; /* constants, variables */
    uint32_t terms  = 0; /* all terms, including inputs */
    uint32_t sorts  = 0; /* all sorts */
  };

  SolverManager(Solver* solver,
                RNGenerator& rng,
                std::ostream& trace,
                SolverOptions& options,
                bool trace_seeds,
                bool cross_check,
                statistics::Statistics* stats);
  ~SolverManager() = default;

  statistics::Statistics* d_mbt_stats;

  /** Clear all data. */
  void clear();

  /** Get solver. */
  Solver& get_solver();

  /** Set random number generator. */
  void set_rng(RNGenerator& rng);
  /** Get random number generator. */
  RNGenerator& get_rng() const;

  /** Get the trace line for the current seed ("set-seed <seed>"). */
  std::string trace_seed() const;

  /** True if current run is a cross check run. */
  bool is_cross_check() const;

  /** Get set of enabled theories. */
  const TheoryIdSet& get_enabled_theories() const;

  std::ostream& get_trace();

  /** Get the number of created terms. */
  uint64_t get_n_terms() const;
  /** Get the number of created terms of given sort kind. */
  uint64_t get_n_terms(SortKind sort_kind);

  /** Add sort to sort databse. */
  void add_sort(Sort sort, SortKind sort_kind);
  /** Add input to term database. */
  void add_input(Term term, Sort sort, SortKind sort_kind);
  /** Add non-input term to term database. */
  void add_term(Term term, Sort sort, SortKind sort_kind);

  /** Pick arbitrary symbol (simple or piped). */
  std::string pick_symbol();

  /**
   * Pick sort kind of existing (= created) sort.
   * Optionally restrict selection to sort kinds with terms only if
   * 'with_terms' is true.
   */
  SortKind pick_sort_kind(bool with_terms = true);

  /**
   * Pick enabled sort kind (and get its data).
   * Only sort kinds of enabled theories are picked.
   * This function does not guarantee that a sort of this kind alreay exists.
   */
  SortKindData& pick_sort_kind_data();
  /**
   * Pick enabled operator kind (and get its data).
   * Only operator kinds of enabled theories are picked.
   */
  Op& pick_op(TheoryId theory, bool with_terms = true);

  /**
   * Return true if
   *  - with_terms = true : Any terms in any enabled theory have been created
   *                        such that an operator of that theory applies.
   *  - with_terms = false: Any theory is enabled.
   */
  bool has_theory(bool with_terms = true);
  /** Pick any of the enabled theories. */
  TheoryId pick_theory(bool with_terms = true);

  /**
   * Pick a term of given sort.
   * Requires that terms of this sort exist.
   */
  Term pick_term(Sort sort);
  /**
   * Pick term of given sort kind.
   * Requires that terms of this sort kind exist.
   */
  Term pick_term(SortKind sort_kind);
  /**
   * Pick any term.
   * Requires that terms of any sort kind exist.
   */
  Term pick_term();
  /**
   * Pick term of Bool SortKind SORT_BOOL and add it to asssumptions list.
   * Requires that terms of SortKind SORT_BOOL exist.
   */
  Term pick_assumption();
  /**
   * Pick assumption out of the assumed assumptions list.
   * Requires that d_assumptions is not empty.
   */
  Term pick_assumed_assumption();

  /**
   * Reset solver manager state into assert mode.
   *
   * After this call, calling
   *   - get_model()
   *   - get_unsat_assumptions()
   *   - get_unsat_core() and
   *   - get_proof()
   * is not possible until after the next SAT call.
   */
  void reset_sat();

  /** Return true if term database contains any term. */
  bool has_term() const;
  /** Return true if term database contains any term of given sort kind. */
  bool has_term(SortKind sort_kind) const;
  /** Return true if term database contains any time of given sort. */
  bool has_term(Sort sort) const;
  /** Return true if term databse contains given term. */
  bool has_term(Term term) const;
  /** Return true if d_assumptions is not empty. */
  bool has_assumed() const;

  /** Return true if given term has been previously assumed. */
  bool is_assumed(Term term) const;

  /**
   * Return the Term in the Term database that wraps the same solver term
   * with the given sort and sort kind.
   * Returns a nullptr if given Term is not in the term database.
   *
   * Note: We need this for Terms returned by the solver that are only wrapped
   *       solver terms without sort information.
   */
  Term find_term(Term term, Sort sort, SortKind sort_kind);

  /**
   * Return the term with the given id.
   * Note: We only use this for untracing.
   */
  Term get_term(uint32_t id) const;

  /**
   * Pick sort.
   * It is not guaranteed that there exist terms of the returned sort.
   */
  Sort pick_sort();
  /**
   * Pick sort of given sort kind. Optionally restrict selection to sorts
   * with terms only if 'with_terms' is true.
   */
  Sort pick_sort(SortKind sort_kind, bool with_terms = true);
  /**
   * Pick sort, but exclude some of them.
   * It is not guaranteed that there exist terms of the returned sort.
   */
  Sort pick_sort(const std::unordered_set<SortKind>& exclude_sorts);
  /**
   * Pick bit-vector sort with given bit-width.  Optionally restrict
   * selection to sorts with terms only if 'with_terms' is true.
   */
  Sort pick_sort_bv(uint32_t bw, bool with_terms = true);
  /**
   * Pick bit-vector sort with given maximum bit-width.  Optionally restrict
   * selection to sorts with terms only if 'with_terms' is true.
   */
  Sort pick_sort_bv_max(uint32_t bw_max, bool with_terms = true);

  /**
   * Return true if any sort has been created.
   * This does not guarantee that any terms have been created.
   */
  bool has_sort() const;
  /**
   * Return true if a sort of given kind exists.
   * This does not guarantee that any terms of this sort have been created.
   */
  bool has_sort(SortKind sort_kind) const;
  /**
   * Return true if given sort already exists.
   * This does not guarantee that any terms of this sort have been created.
   */
  bool has_sort(Sort sort) const;
  /**
   * Return true if sorts other than exclude_sorts have been created.
   * This does not guarantee that any terms have been created.
   */
  bool has_sort(const std::unordered_set<SortKind>& exclude_sorts) const;

  /**
   * Return true if a bit-vector sort with given bit-width exists.
   * Optionally restrict selection to sorts with terms only if 'with_terms' is
   * true.
   */
  bool has_sort_bv(uint32_t bw, bool with_terms = true) const;
  /**
   * Return true if a bit-vector sort up to given maximum bit-width exists.
   * Optionally restrict selection to sorts with terms only if 'with_terms' is
   * true.
   */
  bool has_sort_bv_max(uint32_t bw_max, bool with_terms = true) const;

  /**
   * Return the sort with the given id.
   * Note: We only use this for untracing.
   */
  Sort get_sort(uint32_t id) const;

  /**
   * Set d_n_terms to id.
   * Note: Only used for untracing.
   */
  void set_n_terms(uint64_t id);

  /**
   * Set d_n_sorts to id.
   * Note: Only used for untracing.
   */
  void set_n_sorts(uint64_t id);

  /**
   * Lookup sort in d_sorts. If a no matching sort is found the given sort is
   * returned.
   */
  Sort find_sort(Sort sort) const;

  /**
   * Pick an option and an option value.
   */
  std::pair<std::string, std::string> pick_option();

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

  /** The number of scope levels previously pushed. */
  uint32_t d_n_push_levels = 0;

  /**
   * True if a previous check-sat call is still 'active', i.e., if no formulas
   * have been asserted or assumed since.
   * While true it is save to check failed assumptions and query model values.
   */
  bool d_sat_called = false;

  /** The result of the previous sat call. */
  Solver::Result d_sat_result = Solver::Result::UNKNOWN;

  /** The number of check-sat calls issued. */
  uint32_t d_n_sat_calls = 0;

  /** Statistics. */
  Stats d_stats;

  /**
   * True if every non-return trace call should be preceded by a
   * 'set-seed <seed>' line. We need to provide this option in the solver
   * manager for actions to have access to it.
   */
  bool d_trace_seeds = false;

  /**
   * True if cross checking is enabled. We need to provide this option in the
   * solver manager for the actions to have access to it.
   * */
  bool d_cross_check = false;

 private:
  /**
   * Determine and populate set of enabled theories.
   * All theories supported by a solvers are by default enabled and can
   * optionally be disabled (the latter is still TODO).
   */
  void add_enabled_theories();

  /**
   * Populate sort kinds database with enabled sort kinds.
   * Sort kinds are enabled based on the set of enabled theories.
   */
  void add_sort_kinds();
  /**
   * Populate operator kinds database with enabled operator kinds.
   * Operator kinds are enabled based on the set of enabled theories.
   */
  void add_op_kinds();
  /**
   * Add operator kind to operator kinds database.
   * supported_kinds: the set of operator kinds supported by the solver
   * kind           : the operator kind
   * arity          : the arity of the operator
   * nparams        : the number of parameters of the operator
   * sort_kind      : the sort kind of the operator
   * sort_kind_args : a vector of sorts of the operators' arguments, if all or
   *                  the remaining kinds are the same, it's sufficient to only
   *                  list it once
   */
  void add_op_kind(const OpKindSet& supported_kinds,
                   OpKind kind,
                   int32_t arity,
                   uint32_t nparams,
                   SortKind sort_kind,
                   const std::vector<SortKind>& sort_kind_args,
                   TheoryId theory);

  /** Clear set of assumptions. */
  void clear_assumptions();

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
   * manager, only calls to the API of the smtmbt::Solver object.
   */
  std::unique_ptr<Solver> d_solver;

  /** The random number generator. */
  RNGenerator& d_rng;

  /** The stream to capture the API trace. */
  std::ostream& d_trace;

  /** Term id counter. */
  uint64_t d_n_terms = 0;
  /** Sort id counter. */
  uint64_t d_n_sorts = 0;

  /** Map SortKind to number of created terms of that SortKind. */
  std::unordered_map<SortKind, uint64_t> d_n_sort_terms;

  /** The set of enabled sort kinds. Maps SortKind to SortKindData. */
  SortKindMap d_sort_kinds;
  /** The set of enabled operator kinds. Maps OpKind to Op. */
  OpKindMap d_op_kinds;

  /** The set of enabled theories. */
  TheoryIdSet d_enabled_theories;

  /** Maintain all created sorts. */
  SortSet d_sorts;
  /* Map sort_kind -> (sort -> terms). */
  std::unordered_map<SortKind, SortMap> d_terms;

  /** Map sort kind -> sorts. */
  std::unordered_map<SortKind, SortSet> d_sort_kind_to_sorts;

  /** The set of already assumed formulas. */
  std::unordered_set<Term, HashTerm> d_assumptions;

  /** Vector of available solver options */
  SolverOptions& d_options;

  std::unordered_set<std::string> d_used_options;
};

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt
#endif
