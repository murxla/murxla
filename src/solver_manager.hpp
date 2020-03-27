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
  };

  SolverManager(Solver* solver,
                RNGenerator& rng,
                std::ostream& trace,
                SolverOptions& options);
  ~SolverManager() = default;

  /** Clear all data. */
  void clear();

  /** Get solver. */
  Solver& get_solver();

  /** Set random number generator. */
  void set_rng(RNGenerator& rng);
  /** Get random number generator. */
  RNGenerator& get_rng() const;

  /** Get set of enabled theories. */
  const TheoryIdSet& get_enabled_theories() const;

  std::ostream& get_trace();

  /** Get the number of created terms. */
  uint64_t get_n_terms() const;

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
  OpKindData& pick_op_kind_data();

  /** Pick any of the enabled theories. */
  TheoryId pick_theory();

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
   * Pick bit-vector sort with given maximum bit-width.  Optionally restrict
   * selection to sorts with terms only if 'with_terms' is true.
   */
  Sort pick_sort_bv(uint32_t bw_max, bool with_terms = true);

  /**
   * Return true if any sort has been created.
   * This does not guarantee that any terms have been created.
   */
  bool has_sort() const;
  /**
   * Return true if given sort already exists.
   * This does not guarantee that any terms of this sort have been created.
   */
  bool has_sort(Sort sort) const;
  /**
   * Return true if a bit-vector sort up to given maximum bit-width exists.
   * Optionally restrict selection to sorts with terms only if 'with_terms' is
   * true.
   */
  bool has_sort_bv(uint32_t bw_max, bool with_terms = true) const;

  /**
   * Return the sort with the given id.
   * Note: We only use this for untracing.
   */
  Sort get_sort(uint32_t id) const;

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
   * Populate sort kinds database with enabled operator kinds.
   * Operator kinds are enabled based on the set of enabled theories.
   */
  void add_op_kinds();

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

  /** The set of enabled sort kinds. Maps SortKind to SortKindData. */
  SortKindMap d_sort_kinds;
  /** The set of enabled operator kinds. Maps OpKind to OpKindData. */
  OpKindMap d_op_kinds;

  /** The set of enabled theories. */
  TheoryIdSet d_enabled_theories;

  /* Maintain all created sorts. */
  SortSet d_sorts;
  /* Map sort_kind -> (sort -> terms). */
  std::unordered_map<SortKind, SortMap> d_terms;

  /* Map sort kind -> sorts. */
  std::unordered_map<SortKind, SortSet> d_sort_kind_to_sorts;

  /* The set of already assumed formulas. */
  std::unordered_set<Term, HashTerm> d_assumptions;

  /* Vector of available solver options */
  SolverOptions& d_options;

  std::unordered_set<std::string> d_used_options;
};

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt
#endif
