#include "util.hpp"

#include <unistd.h>
#include <ctime>

namespace smtmbt {

uint32_t SeedGenerator::next()
{
  uint32_t cur_seed;
  cur_seed = d_seed;
  d_seed = getpid();
  d_seed *= 129685499;
  d_seed += time(nullptr);
  d_seed *= 233755607;
  d_seed += cur_seed;
  d_seed *= 38259643;
  return cur_seed;
}

}  // namespace smtmbt
