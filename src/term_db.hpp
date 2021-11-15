#ifndef __MURXLA__TERM_DB_H
#define __MURXLA__TERM_DB_H

#include <cstddef>
#include <iterator>

#include "solver.hpp"

namespace murxla {

class SolverManager;
class RNGenerator;

/**
 * This class manages term references and random picking of terms based on
 * the number of references where terms with higher reference counts have lower
 * probability to be picked.
 */
class TermRefs
{
 public:
  /** Add term. */
  void add(const Term& t);
  /** Check if term was already added. */
  bool contains(const Term& t) const;
  /** Get stored term. */
  Term get(const Term& t) const;
  /**
   * Pick random term based on reference counts.
   * Terms with higher reference count have lower probability to be picked.
   */
  Term pick(RNGenerator& rng);
  /** Return number of stored terms. */
  size_t size() const;

  /** Iterator that wraps the d_idx iterator to return terms only. */
  struct Iterator
  {
    using iterator_category = std::forward_iterator_tag;

    Iterator(std::unordered_map<Term, size_t>::const_iterator it) : d_it(it) {}

    const Term operator*() { return d_it->first; }
    const Term operator->() { return d_it->first; }

    Iterator& operator++()
    {
      d_it++;
      return *this;
    }
    Iterator operator++(int)
    {
      Iterator tmp = *this;
      ++(*this);
      return tmp;
    }

    friend bool operator==(const Iterator& a, const Iterator& b)
    {
      return a.d_it == b.d_it;
    }
    friend bool operator!=(const Iterator& a, const Iterator& b)
    {
      return a.d_it != b.d_it;
    }

   private:
    std::unordered_map<Term, size_t>::const_iterator d_it;
  };

  Iterator begin() const { return Iterator(d_idx.cbegin()); }
  Iterator end() const { return Iterator(d_idx.cend()); }

 private:
  /** Map term to term index. */
  std::unordered_map<Term, size_t> d_idx;
  /** Maps term index to term. */
  std::vector<Term> d_terms;
  /** Maps term index to references. */
  std::vector<size_t> d_refs;
  /** Maps term index to pick weight (used by pick()). */
  std::vector<size_t> d_weights;
  /** Sum of all references d_refs, used to compute weights in pick(). */
  size_t d_refs_sum = 0;
};

class TermDb
{
 public:
  using SortMap     = std::unordered_map<Sort, TermRefs>;
  using SortSet     = std::unordered_set<Sort>;
  using SortKindSet = std::unordered_set<SortKind>;
  using SortTermMap = std::unordered_map<SortKind, SortMap>;

  TermDb(SolverManager& smgr, RNGenerator& rng);

  /** Clear term database. */
  void clear();
  /**
   * Reset term database.
   * This clears and reinitializes the term database.
   */
  void reset();

  /** Reset term id counter to id (required for untracing) */
  void set_term_id_couter(uint64_t id);

  /**
   * Add term to database.
   *
   * Terms are categorized by sort kind and sort:
   * SortKind -> Sort -> Terms
   *
   * The mapping from SortKind to Sort is a 1:1 mapping for sorts that are not
   * parameterized, and a 1:n mapping for parameterized sorts like BV and FP
   * sorts. A notable special case is sort kind SORT_REAL, since sort Int is
   * a subtype of sort Real. We always store terms of sort Int under SORT_REAL,
   * even created terms that are expected to be of SORT_REAL but are identified
   * by the solver as of sort Int.
   */
  void add_term(Term& term,
                Sort& sort,
                SortKind sort_kind,
                const std::vector<Term>& args = {});

  /**
   * Add input (const, value) to database.
   * This is a specialization for inputs on top of add_term.
   */
  void add_input(Term& input, Sort& sort, SortKind sort_kind);

  /**
   * Add variable to database.
   * This is a specialization for variables on top of add_term.
   */
  void add_var(Term& input, Sort& sort, SortKind sort_kind);

  /** Lookup term with given sort and sort_kind in database. */
  Term find(Term term, Sort sort, SortKind sort_kind) const;

  /** Lookup term by id. */
  Term get_term(uint64_t id) const;

  /** Returns all term sorts currently in the database. */
  const SortSet get_sorts() const;

  /**
   * Return true if term database has a value with given sort.
   *
   * Special case: if sort is of kind SORT_REAL, return true if term database
   *               has value of kind SORT_INT or SORT_REAL.
   */
  bool has_value(Sort sort) const;

  /**
   * Return true if term database has a term with given sort kind and at
   * given or lower scope levels.
   *
   * Special case: if sort kind is SORT_REAL, return true if term database
   *               has term of kind SORT_INT or SORT_REAL at given or lower
   *               scope levels.
   */
  bool has_term(SortKind kind, size_t level) const;
  /**
   * Return true if term database has a term with given sort kind.
   *
   * Special case: if sort kind is SORT_REAL, return true if term database
   *               has term of kind SORT_INT or SORT_REAL.
   */
  bool has_term(SortKind kind) const;
  /**
   * Return true if term database has a term with any of the given sort kinds.
   *
   * Special case: if sort kind is SORT_REAL and the solver treats Int as a
   *               subtype of Real, return true if term database has term of
   *               kind SORT_INT or SORT_REAL.
   */
  bool has_term(const SortKindSet& kinds) const;
  /**
   * Return true if term database has a term with sort.
   *
   * Special case: if sort is of kind SORT_REAL and the solver treats Int as a
   *               subtype of Real, return true if term database has term of
   *               kind SORT_INT or SORT_REAL.
   */
  bool has_term(Sort sort) const;
  /** Return true if term database contains any term. */
  bool has_term() const;
  /** Return true if term database contains a variable. */
  bool has_var() const;
  /**
   * Return true if term database contains a variable and a Boolena term in the
   * current scope level.
   */
  bool has_quant_body() const;
  /**
   * Return true if term database contains a variable and a term (of any sort)
   * in the current scope level.
   */
  bool has_quant_term() const;

  /**
   * Pick a value of given sort.
   * Requires that values of this sort exist.
   *
   * Special case: if sort is of kind SORT_REAL, we pick either from SORT_INT
   *               or SORT_REAL, weighted by number of terms of these sorts
   *               in the database.
   */
  Term pick_value(Sort sort) const;

  /**
   * Pick a term of given sort kind at scope level.
   * Requires that terms of this sort kind at given or lower scope levels exist.
   *
   * Special case: if sort is of kind SORT_REAL, we pick either from SORT_INT
   *               or SORT_REAL at given or lower scope levels, weighted by
   *               number of terms of these sorts in the database.
   */
  Term pick_term(SortKind kind, size_t level);
  /**
   * Pick a term of given sort kind.
   * Requires that terms of this sort kind exist.
   *
   * Special case: if sort is of kind SORT_REAL, we pick either from SORT_INT
   *               or SORT_REAL, weighted by number of terms of these sorts
   *               in the database.
   */
  Term pick_term(SortKind kind);
  /**
   * Pick a term of given sort.
   * Requires that terms of this sort exist.
   *
   * Special case: if sort is of kind SORT_REAL, we pick either from SORT_INT
   *               or SORT_REAL, weighted by number of terms of these sorts
   *               in the database.
   */
  Term pick_term(Sort sort);
  /**
   * Pick any term.
   * Requires that a term exists.
   */
  Term pick_term();
  /**
   * Pick any term from given level.
   * Requires that a term exists.
   */
  Term pick_term(size_t level);

  /**
   * Pick variable from current scope.
   * Requires that a variable exists.
   */
  Term pick_var() const;
  /**
   * Pick Boolean term from current scope.
   * Requires that a Boolean term exists at the current scope level.
   */
  Term pick_quant_body();
  /**
   * Pick term of any sort from current scope.
   * Requires that a term exists at the current scope level.
   */
  Term pick_quant_term();
  /**
   * Remove variable from current scope and close scope.
   */
  void remove_var(Term& var);

  /** Pick a sort kind. */
  SortKind pick_sort_kind() const;

  /** Pick a sort kind from given level. */
  SortKind pick_sort_kind(size_t level) const;

  /** Pick a sort kind (with terms) from any of the given sort kinds. */
  SortKind pick_sort_kind(const SortKindSet& sort_kinds) const;

  /** Pick sort with given sort kind. */
  Sort pick_sort(SortKind sort_kind) const;

  /** Pick sort with any of the given sort kinds. */
  Sort pick_sort(const SortKindSet& sort_kinds) const;

 private:
  /** Open new scope with given variable. */
  void push(Term& var);
  /** Close current scope with given variable. */
  void pop(Term& var);
  /** Get the number of terms of given sort kind stored in the database. */
  size_t get_number_of_terms(SortKind sort_kind) const;
  /**
   * Get the number of terms of given sort kind stored in the database up
   * to and includinv given level.
   */
  size_t get_number_of_terms(SortKind sort_kind, size_t level) const;

  /**
   * Pick a scope level.
   * Lower levels are picked less often.
   */
  size_t pick_level() const;
  /**
   * Pick a scope level that has terms with given sort kind.
   * Lower levels are picked less often.
   *
   * Special case: If sort kind is SORT_REAL, we pick a level either for kind
   *               SORT_INT or SORT_REAL, weighted by number of terms of these
   *               sorts in the database.
   *               Note: If level of kind SORT_INT is picked, 'kind' is reset
   *                     to SORT_INT.
   */
  size_t pick_level(SortKind& kind) const;
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

}  // namespace murxla

#endif
