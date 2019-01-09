#ifdef SMTMBT_USE_BOOLECTOR

#include <cassert>

#include "btor_actions.hpp"
#include "util.hpp"

namespace smtmbt {
namespace btor {

void
BtorActionNew::run()
{
  SMTMBT_TRACE << get_id();
  Btor* btor = d_smgr->get_solver();
  if (btor != nullptr) boolector_delete(btor);
  d_smgr->set_solver(boolector_new());
}

void
BtorActionDelete::run()
{
  SMTMBT_TRACE << get_id();
  Btor* btor = d_smgr->get_solver();
  assert(btor);
  boolector_delete(btor);
  d_smgr->set_solver(nullptr);
}

}  // namespace btor
}  // namespace smtmbt

#endif
