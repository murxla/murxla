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
  const static size_t MAX_LEVEL = std::numeric_limits<size_t>::max();

  TermRefs(size_t level);

  /** Add term. */
  void add(const Term& t, size_t level);
  /** Check if term was already added. */
  bool contains(const Term& t) const;
  /** Get stored term. */
  Term get(const Term& t) const;
  /**
   * Pick random term based on reference counts.
   * Terms with higher reference count have lower probability to be picked.
   */
  Term pick(RNGenerator& rng, size_t level = MAX_LEVEL);
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

  void push();
  void pop();

  size_t get_num_terms(size_t level) const;

 private:
  size_t get_level_begin(size_t level);
  size_t get_level_end(size_t level);

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

  /* Maps level to number of corresponding terms. */
  std::vector<size_t> d_levels;
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

  /** Return the current top level of stored terms. */
  size_t max_level() const;

  /** Get the number of available variables. */
  uint32_t get_num_vars() const;

  /**
   * Add term to database.
   *
   * Terms are categorized by sort kind and sort:
   * SortKind -> Sort -> Terms
   *
   * The mapping from SortKind to Sort is a 1:1 mapping for sorts that are not
   * parameterized, and a 1:n mapping for parameterized sorts like BV and FP
   * sorts. A notable special case is sort kind SORT_REAL if sort Int is
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

  /** Return true if term database has a value. */
  bool has_value() const;
  /** Return true if term database has a value with given sort. */
  bool has_value(Sort sort) const;

  /**
   * Return true if term database has a term with given sort kind at given or
   * lower scope levels.
   */
  bool has_term(SortKind kind, size_t level) const;
  /**
   * Return true if term database has a term with given sort kind.
   */
  bool has_term(SortKind kind) const;
  /**
   * Return true if term database has a term with any of the given sort kinds.
   */
  bool has_term(const SortKindSet& kinds) const;
  /**
   * Return true if term database has a term with sort.
   */
  bool has_term(Sort sort) const;
  /**
   * Return true if term database has a term with given sort at given or lower
   * scope levels.
   */
  bool has_term(Sort sort, size_t level) const;
  /** Return true if term database contains any term on given level. */
  bool has_term(size_t level) const;
  /** Return true if term database contains any term. */
  bool has_term() const;
  /**
   * Return true if term database contains a function term with given domain
   * sorts.
   */
  bool has_fun(const std::vector<Sort>& domain_sorts) const;
  /** Return true if term database contains a variable. */
  bool has_var() const;
  /**
   * Return true if term database contains a variable and a Boolena term in the
   * current scope level.
   */
  bool has_quant_body() const;
  /**
   * Return true if term database contains a variable and a term (of the given
   * or any sort kind) in the current scope level.
   */
  bool has_quant_term(SortKind sort_kind = SORT_ANY) const;
  /**
   * Return true if term database contains a variable and a term of the given
   * sort in the current scope level.
   */
  bool has_quant_term(Sort sort) const;

  /** Pick value of any sort. */
  Term pick_value() const;
  /**
   * Pick a value of given sort.
   * Requires that values of this sort exist.
   */
  Term pick_value(Sort sort) const;

  /**
   * Pick a term of given sort kind at scope level.
   * Requires that terms of this sort kind at given or lower scope levels exist.
   */
  Term pick_term(SortKind kind, size_t level);
  /**
   * Pick a term of given sort at scope level.
   * Requires that terms of this sort at given or lower scope levels exist.
   */
  Term pick_term(Sort sort, size_t level);
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
   * Pick any term from given level.
   * Requires that a term exists.
   */
  Term pick_term(size_t level);

  /**
   * Pick function term with given domain sorts.
   * Requires that such terms exist.
   */
  Term pick_fun(const std::vector<Sort>& domain_sorts);

  /**
   * Pick variable from current scope.
   * Requires that a variable exists.
   */
  Term pick_var() const;
  /**
   * Pick 'num_vars' variables.
   * Requires that at least 'num_vars' variables exist.
   */
  std::vector<Term> pick_vars(uint32_t num_vars) const;
  /**
   * Pick Boolean term from current scope.
   * Requires that a Boolean term exists at the current scope level.
   */
  Term pick_quant_body();
  /**
   * Pick term of (optionally the given, else any) sort kind from current scope.
   * Requires that a term of that sort kind exists at the current scope level.
   */
  Term pick_quant_term(SortKind sort_kind = SORT_ANY);
  /**
   * Pick term of given sort from current scope.
   * Requires that a term of that sort exists at the current scope level.
   */
  Term pick_quant_term(Sort sort);
  /**
   * Remove variable from current scope and close scope.
   * Must be called before calling add_term.
   */
  void remove_var(const Term& var);

  /** Pick a sort kind from any level. */
  SortKind pick_sort_kind() const;

  /**
   * Pick a sort kind from given level.
   * Optionally, exclude given sort kinds.
   */
  SortKind pick_sort_kind(size_t level,
                          const SortKindSet& exclude_sort_kinds = {}) const;

  /** Pick a sort kind (with terms) from any of the given sort kinds. */
  SortKind pick_sort_kind(const SortKindSet& sort_kinds) const;

  /** Pick a sort kind from any level, excluding the given sort kinds. */
  SortKind pick_sort_kind_excluding(
      const SortKindSet& exclude_sort_kinds) const;

  /** Pick sort with given sort kind. */
  Sort pick_sort(SortKind sort_kind) const;

  /** Pick sort with any of the given sort kinds. */
  Sort pick_sort(const SortKindSet& sort_kinds) const;

  /** Get the number of terms at a given level stored in the database. */
  size_t get_num_terms(size_t level) const;

 private:
  /** Intermediate op kinds. */
  inline static std::unordered_set<Op::Kind> d_intermediate_op_kinds{
      Op::DT_MATCH_BIND_CASE, Op::DT_MATCH_CASE};
  /** Open new scope with given variable. */
  void push(Term& var);
  /** Close current scope with given variable. */
  void pop(const Term& var);
  /** Get the number of terms of given sort kind stored in the database. */
  size_t get_num_terms(SortKind sort_kind) const;
  /**
   * Get the number of terms of given sort kind stored in the database up
   * to and includinv given level.
   */
  size_t get_num_terms(SortKind sort_kind, size_t level) const;

  SolverManager& d_smgr;

  RNGenerator& d_rng;

  /** Term database that maps SortKind -> Sort -> TermRefs */
  SortTermMap d_term_db;

  /**
   * Maps term ids to terms.
   *
   * This only includes terms that may be picked to create arbitrary other
   * terms. Examples for terms that are excluded are terms like DT_MATCH_CASE
   * and DT_MATCH_BIND_CASE, which have to be considered as 'intermediate'
   * terms that may only be used for the one specific DT_MATCH they were
   * created for.
   */
  std::unordered_map<uint64_t, Term> d_terms;
  /**
   * Maps term ids to intermediate terms.
   *
   * This only includes terms that may NOT be picked to create other terms.
   * Intermediate terms are terms that have been created as intermediate steps
   * to create a specific term, for examples terms like DT_MATCH_CASE and
   * DT_MATCH_BIND_CASE, which may only be used for the one specific DT_MATCH
   * they were created for.
   */
  std::unordered_map<uint64_t, Term> d_terms_intermediate;

  /** Maps function term arity to function terms. */
  std::unordered_map<uint32_t, std::unordered_set<Term>> d_funs;

  /** Maps scope level to variable that opened the scope. */
  std::vector<Term> d_vars;

  /** Sorts currently used in d_term_db. */
  SortSet d_term_sorts;
};

}  // namespace murxla

#endif
