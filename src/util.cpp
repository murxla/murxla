#include "util.hpp"

#include <stdlib.h>
#include <unistd.h>
#include <bitset>
#include <cassert>
#include <ctime>
#include <iostream>
#include <limits>
#include <sstream>

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

uint64_t
RNGenerator::pick_uint64()
{
  return d_uint64_dist(d_rng);
}

uint64_t
RNGenerator::pick_uint64(uint64_t from, uint64_t to)
{
  uint64_t res = pick_uint64();

  from = from == UINT64_MAX ? UINT64_MAX - 1 : from;
  to   = to == UINT64_MAX ? UINT64_MAX - 1 : to;
  res %= to - from + 1;
  res += from;
  return res;
}

std::string
RNGenerator::pick_bin_str(uint32_t size)
{
  uint32_t n = static_cast<uint32_t>(std::ceil(size/32.0));
  uint32_t val;
  std::stringstream ss;
  for (uint32_t i = 0; i < n; i++)
  {
    val = pick_uint32();
    ss << std::bitset<32>(val).to_string();
  }
  std::string res = ss.str();
  res.resize(size);
  return res;
}

bool
RNGenerator::pick_with_prob(uint32_t prob)
{
  assert (prob <= SMTMBT_PROB_MAX);
  uint32_t r = pick_uint32(0, SMTMBT_PROB_MAX - 1);
  return r < prob;
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
