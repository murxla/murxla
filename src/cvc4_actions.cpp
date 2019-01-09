#ifdef SMTMBT_USE_CVC4

#include <cassert>

#include "cvc4_actions.hpp"
#include "util.hpp"

namespace smtmbt {
namespace cvc4 {

void
CVC4ActionNew::run()
{
  SMTMBT_TRACE << get_id();
  CVC4::api::Solver *cvc4 = d_smgr->get_solver();
  if (cvc4 != nullptr) delete (cvc4);
  d_smgr->set_solver(new CVC4::api::Solver());
}

void
CVC4ActionDelete::run()
{
  SMTMBT_TRACE << get_id();
  CVC4::api::Solver *cvc4 = d_smgr->get_solver();
  assert(cvc4);
  delete (cvc4);
  d_smgr->set_solver(nullptr);
}

}  // namespace cvc4
}  // namespace smtmbt

#endif
