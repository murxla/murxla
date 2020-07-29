#ifndef __SMTMBT__TERM_DB_H
#define __SMTMBT__TERM_DB_H

#include "solver.hpp"

namespace smtmbt {

class SolverManager;
class RNGenerator;

class TermDb
{
 public:
  using TermMap     = std::unordered_map<Term, size_t, HashTerm>;
  using SortMap     = std::unordered_map<Sort, TermMap, HashSort>;
  using SortSet     = std::unordered_set<Sort, HashSort>;
  using SortKindSet = std::unordered_set<SortKind>;
  using SortTermMap = std::unordered_map<SortKind, SortMap>;

  TermDb(SolverManager& smgr, RNGenerator& rng);

  /** Clear term database. */
  void clear();

  /** Reset term id counter to id (required for untracing) */
  void set_term_id_couter(uint64_t id);

  /** Add term to database. */
  void add_term(Term& term,
                Sort& sort,
                SortKind sort_kind,
                const std::vector<Term>& args = {});
  /** Add input (const, value) to database. */
  void add_input(Term& input, Sort& sort, SortKind sort_kind);

  /** Add variable to database */
  void add_var(Term& input, Sort& sort, SortKind sort_kind);

  /** Lookup term with given sort and sort_kind in database. */
  Term find(Term term, Sort sort, SortKind sort_kind) const;

  /** Lookup term by id. */
  Term get_term(uint64_t id) const;

  /** Register additional id for term. */
  void register_term(uint64_t id, Term term);

  /** Returns all term sorts currently in the database. */
  const SortSet get_sorts() const;

  /**
   * Return true if term database has a term with given sort kind and scope
   * level.
   */
  bool has_term(SortKind kind, size_t level) const;
  /** Return true if term database has a term with given sort kind. */
  bool has_term(SortKind kind) const;
  /** Return true if term database has a term with sort. */
  bool has_term(Sort sort) const;
  /** Return true if term database contains any term. */
  bool has_term() const;
  /** Return true if term database contains a variable. */
  bool has_var() const;
  /**
   * Return true if term database contains a Boolena term in the curren scope
   * level.
   */
  bool has_quant_body() const;

  /**
   * Pick a term of given sort kind at scope level.
   * Requires that terms of this sort kind and level exist.
   */
  Term pick_term(SortKind kind, size_t level);
  /**
   * Pick a term of given sort kind.
   * Requires that terms of this sort kind exist.
   */
  Term pick_term(SortKind kind);
  /**
   * Pick a term of given sort.
   * Requires that terms of this sort exist.
   */
  Term pick_term(Sort sort);
  /**
   * Pick any term.
   * Requires that a term exists.
   */
  Term pick_term();

  /**
   * Pick variable from current scope.
   * Requires that a variable exists.
   */
  Term pick_var();
  /**
   * Pick Boolean term from current scope.
   * Requires that a Boolean term exists at the current scope level.
   */
  Term pick_quant_body();
  /**
   * Remove variable from current scope and close scope.
   */
  void remove_var(Term& var);

  /** Pick a sort kind. */
  SortKind pick_sort_kind();

  /** Pick sort with given sort kind. */
  Sort pick_sort(SortKind sort_kind);

 private:
  /** Open new scope with given variable. */
  void push(Term& var);
  /** Close current scope with given variable. */
  void pop(Term& var);

  /**
   * Pick a scope level.
   * Lower levels are picked less often.
   */
  size_t pick_level() const;
  /**
   * Pick a scope level that has terms with given sort kind.
   * Lower levels are picked less often.
   */
  size_t pick_level(SortKind kind) const;
  /**
   * Pick a scope level that has terms with given sort.
   * Lower levels are picked less often.
   */
  size_t pick_level(Sort sort) const;

  SolverManager& d_smgr;

  RNGenerator& d_rng;

  /** Term database that maps SortKind -> Sort -> Term -> size_t */
  std::vector<SortTermMap> d_term_db;

  /** Maps term ids to terms. */
  std::unordered_map<uint64_t, Term> d_terms;

  /** Maps scope level to variable that opened the scope. */
  std::vector<Term> d_vars;

  /** Sorts currently used in d_term_db. */
  SortSet d_term_sorts;
};

}  // namespace smtmbt

#endif
