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
   explicit RNGenerator(uint32_t seed = 0) : d_seed(seed) { d_rng.seed(seed); }
   uint32_t next_uint32();
   uint32_t pick_uint32_weighted(std::vector<uint32_t>& weights);

  private:
    uint32_t d_seed;
    std::mt19937 d_rng;
    std::uniform_int_distribution<uint32_t> d_uint32_dist;
};

class TraceStream
{
 public:
  TraceStream();
  ~TraceStream();
  TraceStream(const TraceStream& astream) = default;

  std::ostream& stream();

 private:
  void flush();
};

class AbortStream
{
 public:
  AbortStream();
  ~AbortStream();
  AbortStream(const AbortStream& astream) = default;

  std::ostream& stream();

 private:
  void flush();
};

class OstreamVoider
{
 public:
  OstreamVoider() = default;
  void operator&(std::ostream& ostream) {}
};

#define SMTMBT_TRACE \
  OstreamVoider() & TraceStream().stream()

#define SMTMBT_ABORT(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & AbortStream().stream()

}  // namespace smtmbt

#endif
