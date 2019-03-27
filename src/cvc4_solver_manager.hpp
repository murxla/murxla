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
  KindData(CVC4::api::Kind kind = CVC4::api::UNDEFINED_KIND,
           uint32_t arity       = 0,
           uint32_t nparams     = 0,
           TheoryId theory_term = THEORY_BOOL,
           TheoryId theory_args = THEORY_BOOL)
      : d_kind(kind),
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

  CVC4::api::Kind d_kind; /* The Kind. */
  uint32_t d_arity;       /* The arity of this kind. */
  uint32_t d_nparams;     /* The number of parameters if parameterized. */
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
  using CVC4OpTermMap = std::
      unordered_map<CVC4::api::OpTerm, size_t, CVC4::api::OpTermHashFunction>;
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
  auto get_all_op_kinds_uint() { return d_all_op_kinds_uint; }

  void add_op_term(CVC4::api::OpTerm op_term, TheoryId theory);
  CVC4::api::OpTerm pick_op_term();
  CVC4::api::OpTerm pick_op_term(TheoryId theory);
  bool has_op_term(TheoryId theory);

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
   * Mapping for all CVC4 operator kinds with uint32 parameters from TheoryId of
   * their term arguments to
   *   - the kind
   *   - its arity
   *   - its number of parameters
   *   - the theory of the term arguments of this kind.
   *   - the theory of a term of this kind.
   */
  CVC4KindMap d_all_op_kinds_uint;

  /* Map theory -> opterms. */
  std::unordered_map<TheoryId, CVC4OpTermMap> d_op_terms;
};

/* -------------------------------------------------------------------------- */

}  // namespace cvc4
}  // namespace smtmbt

#endif

#endif
