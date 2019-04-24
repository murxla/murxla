#ifdef SMTMBT_USE_CVC4

#ifndef __SMTMBT__CVC4_SOLVER_MANAGER_H
#define __SMTMBT__CVC4_SOLVER_MANAGER_H

#include "solver_manager.hpp"

#include <unordered_map>

#include "cvc4/api/cvc4cpp.h"

namespace smtmbt {
namespace cvc4 {

/* -------------------------------------------------------------------------- */

struct KindData
{
  KindData(CVC4::api::Kind kind    = CVC4::api::UNDEFINED_KIND,
           CVC4::api::Kind op_kind = CVC4::api::UNDEFINED_KIND,
           int32_t arity           = 0,
           uint32_t nparams        = 0,
           TheoryId theory_term    = THEORY_BOOL,
           TheoryId theory_args    = THEORY_BOOL)
      : d_kind(kind),
        d_op_kind(op_kind),
        d_arity(arity),
        d_nparams(nparams),
        d_theory_term(theory_term),
        d_theory_args(theory_args)
  {
  }

  bool operator==(const KindData& other) const
  {
    return (d_kind == other.d_kind && d_arity == other.d_arity
            && d_theory_term == other.d_theory_term
            && d_theory_args == other.d_theory_args);
  }

  /* The Kind. */
  CVC4::api::Kind d_kind;
  /* For operator kinds, the corresponding parameterized kind. */
  CVC4::api::Kind d_op_kind;
  /* The arity of this kind. */
  int32_t d_arity;
  /* The number of parameters if parameterized. */
  uint32_t d_nparams;
  /* The theory of a term of this kind. */
  TheoryId d_theory_term;
  /* The theory of the term arguments of this kind. */
  TheoryId d_theory_args;
};

/* -------------------------------------------------------------------------- */

using CVC4SolverManagerBase = SolverManager<CVC4::api::Solver*,
                                            CVC4::api::Term,
                                            CVC4::api::Sort,
                                            CVC4::api::TermHashFunction,
                                            CVC4::api::SortHashFunction>;

/* -------------------------------------------------------------------------- */

using CVC4KindVector = std::vector<CVC4::api::Kind>;
using CVC4KindMap =
    std::unordered_map<CVC4::api::Kind, KindData, CVC4::api::KindHashFunction>;

class CVC4SolverManager : public SolverManager<CVC4::api::Solver*,
                                               CVC4::api::Term,
                                               CVC4::api::Sort,
                                               CVC4::api::TermHashFunction,
                                               CVC4::api::SortHashFunction>
{
 public:
  CVC4SolverManager(RNGenerator& rng) : SolverManager(rng) { configure(); }
  CVC4SolverManager() = delete;
  ~CVC4SolverManager();
  void clear();
  CVC4::api::Sort get_sort(CVC4::api::Term term) override;
  KindData& pick_kind(CVC4KindVector& kinds);
  KindData& pick_kind(CVC4KindVector& kinds1, CVC4KindVector& kinds2);
  KindData& pick_op_kind_uint(CVC4KindVector& kinds);
  KindData& pick_op_kind_uint(CVC4KindVector& kinds1, CVC4KindVector& kinds2);
  auto get_all_kinds() { return d_all_kinds; }
  CVC4::api::OpTerm mkOpTerm(CVC4::api::Kind kind, CVC4::api::Term term);

  /**
   * Pick random OpTerm from list of generated OpTerms.
   * This is only used for API calls on OpTerms.
   */
  CVC4::api::OpTerm& pick_op_term();

  /**
   * Return true if the list of generated OpTerms is not empty.
   */
  bool has_op_term() { return !d_op_terms.empty(); }

 protected:
  void configure() override;

 private:
  void configure_kinds();
  KindData& pick_kind(CVC4KindMap& map, CVC4KindVector& kinds);
  KindData& pick_kind(CVC4KindMap& map,
                      CVC4KindVector& kinds1,
                      CVC4KindVector& kinds2);
  /**
   * Mapping for all (non-operator) CVC4 kinds from TheoryId of their term
   * arguments to
   *   - the kind
   *   - its arity
   *   - its number of parameters (must be 0)
   *   - the theory of the term arguments of this kind.
   *   - the theory of a term of this kind.
   */
  CVC4KindMap d_all_kinds;

  /**
   * List of all generated OpTerms.
   * This list is only used for API calls on OpTerms.
   */
  std::vector<CVC4::api::OpTerm> d_op_terms;
};

/* -------------------------------------------------------------------------- */

}  // namespace cvc4
}  // namespace smtmbt

#endif

#endif
