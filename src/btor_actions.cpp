#ifdef SMTMBT_USE_BOOLECTOR

#include <cassert>

#include "btor_actions.hpp"

namespace smtmbt {
namespace btor {

void
BtorActionNew::run()
{
  Btor* btor = d_smgr->get_solver();
  if (btor != nullptr) boolector_delete(btor);
  d_smgr->set_solver(boolector_new());
}

void
BtorActionDelete::run()
{
  Btor* btor = d_smgr->get_solver();
  assert(btor);
  boolector_delete(btor);
  d_smgr->set_solver(nullptr);
}

}  // namespace btor
}  // namespace smtmbt

#endif
