#ifndef __SMTMBT__UTIL_H
#define __SMTMBT__UTIL_H

#include <cstdint>
#include <random>

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

class RNGenerator
{
  public:
    uint32_t next_uint32();
    uint32_t pick_weighted_uint32(std::vector<uint32_t>& weights);

  private:
    uint32_t d_seed;
    std::mt19937 d_rng;
    std::discrete_distribution<uint32_t> d_uint32_dist;
};

}  // namespace smtmbt

#endif
