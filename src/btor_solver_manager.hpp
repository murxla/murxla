#ifdef SMTMBT_USE_BOOLECTOR

#ifndef __SMTMBT__BTOR_SOLVER_MANAGER_H
#define __SMTMBT__BTOR_SOLVER_MANAGER_H

#include "solver_manager.hpp"

#include "boolector.h"

namespace smtmbt {
namespace btor {

#if 0

/* -------------------------------------------------------------------------- */

struct BoolectorNodeHashFunc
{
  size_t operator()(const BoolectorNode *n) const;
};

struct BoolectorSortHashFunc
{
  size_t operator()(const BoolectorSort s) const;
};

/* -------------------------------------------------------------------------- */

using BtorSolverManagerBase = SolverManager<Btor *,
                                            BoolectorNode *,
                                            BoolectorSort,
                                            BoolectorNodeHashFunc,
                                            BoolectorSortHashFunc>;

/* -------------------------------------------------------------------------- */

class BtorSolverManager : public BtorSolverManagerBase
{
 public:
  BtorSolverManager(RNGenerator &rng) : SolverManager(rng) { configure(); };
  BtorSolverManager() = delete;
  ~BtorSolverManager();
  void clear();
  BoolectorSort get_sort(BoolectorNode *term) override;
  BoolectorSort get_bool_sort();
  void set_bool_sort(BoolectorSort sort);

 protected:
  void configure() override;
  BoolectorNode *copy_term(BoolectorNode *term) override;
  BoolectorSort copy_sort(BoolectorSort sort) override;

 private:
  BoolectorSort d_bool_sort;
};

/* -------------------------------------------------------------------------- */

#endif

}  // namespace btor
}  // namespace smtmbt

#endif

#endif
