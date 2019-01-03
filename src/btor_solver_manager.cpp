#include "btor_solver_manager.hpp"

#include <functional>
#include <iostream>

namespace smtmbt {
namespace btor {

size_t BoolectorNodeHashFunc::operator()(const BoolectorNode* n) const
{
  Btor* btor = boolector_get_btor(const_cast<BoolectorNode*>(n));
  int32_t id = boolector_get_id(btor, const_cast<BoolectorNode*>(n));
  return std::hash<int32_t>{}(id);
}

size_t BoolectorSortHashFunc::operator()(const BoolectorSort s) const
{
  return std::hash<BoolectorSort>{}(s);
}

BtorSolverManager::~BtorSolverManager()
{
  BoolectorSort sort;
  BtorSolverManager::TermMap tmap;
  for (auto& p : d_terms)
  {
    std::tie(sort, tmap) = p;
    boolector_release_sort(d_solver, sort);

    for (auto& p : tmap)
    {
      boolector_release(d_solver, p.first);
    }
  }
  if (d_solver != nullptr)
  {
    boolector_delete(d_solver);
  }
}

BoolectorNode* BtorSolverManager::copy_term(BoolectorNode* term)
{
  return boolector_copy(d_solver, term);
}

BoolectorSort BtorSolverManager::copy_sort(BoolectorSort sort)
{
  return boolector_copy_sort(d_solver, sort);
}

BoolectorSort BtorSolverManager::get_sort(BoolectorNode* term)
{
  return boolector_get_sort(d_solver, term);
}

}  // namespace btor
}  // namespace smtmbt
