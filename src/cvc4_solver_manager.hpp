#ifdef SMTMBT_USE_CVC4

#ifndef __SMTMBT__CVC4_SOLVER_MANAGER_H
#define __SMTMBT__CVC4_SOLVER_MANAGER_H

#include "solver_manager.hpp"

#include <unordered_map>

#include "api/cvc4cpp.h"

namespace smtmbt {
namespace cvc4 {

/* -------------------------------------------------------------------------- */

struct KindData
{
  KindData(CVC4::api::Kind kind = CVC4::api::UNDEFINED_KIND,
           uint32_t arity       = 0,
           bool parameterized   = false,
           TheoryId theory_term = THEORY_BOOL,
           TheoryId theory_args = THEORY_BOOL)
      : d_kind(kind),
        d_arity(arity),
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

  CVC4::api::Kind d_kind; /* The Kind. */
  int32_t d_arity;        /* The arity of this kind. */
  bool d_parameterized;   /* Is this kind a parameterized kind? */
  TheoryId d_theory_term; /* The theory of a term of this kind. */
  TheoryId d_theory_args; /* The theory of the term arguments of this kind. */
};

/* -------------------------------------------------------------------------- */

using CVC4SolverManagerBase = SolverManager<CVC4::api::Solver*,
                                            CVC4::api::Term,
                                            CVC4::api::Sort,
                                            CVC4::api::TermHashFunction,
                                            CVC4::api::SortHashFunction>;

/* -------------------------------------------------------------------------- */

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
  KindData& pick_kind(std::vector<CVC4::api::Kind>& kinds);
  KindData& pick_kind(std::vector<CVC4::api::Kind>& kinds1,
                      std::vector<CVC4::api::Kind>& kinds2);
  auto get_all_kinds() { return d_all_kinds; }

 protected:
  void configure() override;

 private:
  void configure_kinds();

  /**
   * Mapping for all CVC4 kinds from TheoryId of their term arguments to
   *   - the kind
   *   - its arity
   *   - the theory of the term arguments of this kind.
   *   - the theory of a term of this kind.
   */
  std::unordered_map<CVC4::api::Kind, KindData, CVC4::api::KindHashFunction>
      d_all_kinds;
};

/* -------------------------------------------------------------------------- */

}  // namespace cvc4
}  // namespace smtmbt

#endif

#endif
