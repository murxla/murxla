#ifndef __SMTMBT__OPTIONS_HPP
#define __SMTMBT__OPTIONS_HPP

#include <cstdint>

namespace smtmbt {

struct Options
{
  uint32_t seed      = 0;
  uint32_t verbosity = 0;

  bool use_btor = false;
  bool use_cvc4 = false;
};

}  // namespace smtmbt

#endif
