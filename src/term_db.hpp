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

  void clear();

  void add_term(Term& term,
                Sort& sort,
                SortKind sort_kind,
                const std::vector<Term>& args = {});
  void add_input(Term& input, Sort& sort, SortKind sort_kind);
  void add_var(Term var);

  Term find(Term term, Sort sort, SortKind sort_kind) const;
  Term get_term(uint32_t id) const;

  const SortKindSet get_sort_kinds() const;
  const SortSet get_sorts() const;

  bool has_term(SortKind kind) const;
  bool has_term(Sort sort) const;
  bool has_term() const;

  Term pick_term(SortKind kind);
  Term pick_term(Sort sort);
  Term pick_term();

  Term pick_free_vars();
  void remove_vars(const std::vector<Term>& vars);

  SortKind pick_sort_kind();

  Sort pick_sort(SortKind sort_kind);

  //  Sort pick_sort_bv(uint32_t bw);
  //  Sort pick_sort_bv_max(uint32_t bw);

  //  bool has_sort_bv(uint32_t bw);
  //  bool has_sort_bv_max(uint32_t bw);

 private:
  void push();
  void pop();

  size_t pick_level() const;
  size_t pick_level(SortKind kind) const;
  size_t pick_level(Sort sort) const;

  SolverManager& d_smgr;
  RNGenerator& d_rng;

  std::vector<SortTermMap> d_term_db;

  std::unordered_map<uint32_t, Term> d_terms;

  SortKindSet d_term_sort_kinds;
  SortSet d_term_sorts;

  uint64_t d_n_terms = 0;
};

}  // namespace smtmbt

#endif
