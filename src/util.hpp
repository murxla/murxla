#ifndef __SMTMBT__UTIL_H
#define __SMTMBT__UTIL_H

#include <cstdint>
#include <random>
#include <vector>

namespace smtmbt {

#define SMTMBT_PROB_MAX 1000  /* Maximum probability 100% = 1000. */

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
   uint32_t pick_uint32();
   uint32_t pick_uint32(uint32_t from, uint32_t to);
   uint32_t pick_uint32_weighted(std::vector<uint32_t>& weights);
   uint64_t pick_uint64();
   uint64_t pick_uint64(uint64_t from, uint64_t to);
   /* Pick binary string of given size. */
   std::string pick_bin_str(uint32_t size);
   /* Pick decimal string of given binar size. */
   std::string pick_dec_str(uint32_t size);
   /* Pick hexadecimal string of given binary size. */
   std::string pick_hex_str(uint32_t size);
   /* Pick with given probability, 100% = 1000. */
   bool pick_with_prob(uint32_t prob);
   /* Pick random string of given length. */
   std::string pick_string(std::string& chars, uint32_t len);
   /* Pick simple symbol string (as defined in SMT-LIB) of given length. */
   std::string pick_simple_symbol(uint32_t len);

  private:
    uint32_t d_seed;
    std::mt19937 d_rng;
    std::uniform_int_distribution<uint32_t> d_uint32_dist;
    std::uniform_int_distribution<uint64_t> d_uint64_dist;

    std::string d_simple_symbol_char_set =
        "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+-/"
        "*=%?!.$_&<>@^~";
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

class WarnStream
{
 public:
  WarnStream();
  ~WarnStream();
  WarnStream(const WarnStream& astream) = default;

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

#define SMTMBT_WARN(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & WarnStream().stream()

#define SMTMBT_ABORT(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & AbortStream().stream()

}  // namespace smtmbt

#endif
