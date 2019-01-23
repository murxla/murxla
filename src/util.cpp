#include "util.hpp"

#include <stdlib.h>
#include <unistd.h>
#include <ctime>
#include <iostream>
#include <limits>

namespace smtmbt {

uint32_t
SeedGenerator::next()
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

uint32_t
RNGenerator::pick_uint32()
{
  return d_uint32_dist(d_rng);
}

uint32_t
RNGenerator::pick_uint32(uint32_t from, uint32_t to)
{
  uint32_t res = pick_uint32();

  from = from == UINT32_MAX ? UINT32_MAX - 1 : from;
  to   = to == UINT32_MAX ? UINT32_MAX - 1 : to;
  res %= to - from + 1;
  res += from;
  return res;
}

uint32_t
RNGenerator::pick_uint32_weighted(std::vector<uint32_t>& weights)
{
  std::discrete_distribution<uint32_t> dist(weights.begin(), weights.end());
  return dist(d_rng);
}

TraceStream::TraceStream() { stream(); }

TraceStream::~TraceStream()
{
  flush();
}

std::ostream&
TraceStream::stream()
{
  return std::cout;
}

void
TraceStream::flush()
{
  stream() << std::endl;
  stream().flush();
}

AbortStream::AbortStream() { stream() << "smtmbt: ERROR: "; }

AbortStream::~AbortStream()
{
  flush();
  std::abort();
}

std::ostream&
AbortStream::stream()
{
  return std::cerr;
}

void
AbortStream::flush()
{
  stream() << std::endl;
  stream().flush();
}

}  // namespace smtmbt
