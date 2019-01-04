#ifndef __SMTMBT__UTIL_H
#define __SMTMBT__UTIL_H

#include <cstdint>

namespace smtmbt {

class SeedGenerator
{
 public:
  SeedGenerator() { next(); }
  explicit SeedGenerator(uint32_t s) : d_seed(s) {}
  uint32_t next();

 private:
  uint32_t d_seed = 0;
};

}  // namespace smtmbt

#endif
