#ifdef SMTMBT_USE_BOOLECTOR

#ifndef __SMTMBT__BTOR_SOLVER_MANAGER_H
#define __SMTMBT__BTOR_SOLVER_MANAGER_H

#include "solver_manager.hpp"

#include "boolector.h"

namespace smtmbt {
namespace btor {

struct BoolectorNodeHashFunc
{
  size_t operator()(const BoolectorNode *n) const;
};

struct BoolectorSortHashFunc
{
  size_t operator()(const BoolectorSort s) const;
};

class BtorSolverManager : public SolverManager<Btor *,
                                               BoolectorNode *,
                                               BoolectorSort,
                                               BoolectorNodeHashFunc,
                                               BoolectorSortHashFunc>
{
 public:
  BtorSolverManager() = default;
  ~BtorSolverManager();

 protected:
  BoolectorNode *copy_term(BoolectorNode *term) override;
  BoolectorSort copy_sort(BoolectorSort sort) override;
  BoolectorSort get_sort(BoolectorNode *term) override;
};

}  // namespace btor
}  // namespace smtmbt

#endif

#endif
