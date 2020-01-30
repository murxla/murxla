#ifndef __SMTMBT__UTIL_H
#define __SMTMBT__UTIL_H

#include <cstdint>
#include <random>
#include <unordered_map>
#include <vector>

namespace smtmbt {

#define SMTMBT_PROB_MAX 1000  /* Maximum probability 100% = 1000. */

/* -------------------------------------------------------------------------- */

class SeedGenerator
{
 public:
  SeedGenerator() { next(); }
  explicit SeedGenerator(uint32_t s) : d_seed(s) {}
  uint32_t next();

 private:
  uint32_t d_seed = 0;
};

/* -------------------------------------------------------------------------- */

class RNGenerator
{
  public:
   enum Choice
   {
     FIRST,
     SECOND,
     THIRD,
   };

   /** Constructor. */
   explicit RNGenerator(uint32_t seed = 0);
   /** Pick uint32_t between 0 and UINT32_MAX. */
   uint32_t pick_uint32();
   /** Pick uint32_t between 'from' and 'to' (inclusive). */
   uint32_t pick_uint32(uint32_t from, uint32_t to);
   /** Pick int32_t between 'from' and 'to' (inclusive). */
   int32_t pick_int32(int32_t from, int32_t to);
   /**
    * Pick uint32_t between 0 and weights.size(), weighted by the given weights.
    * The probability to pick each number is w/S with w its weight and S the
    * sum of all weights.
    */
   uint32_t pick_uint32_weighted(std::vector<uint32_t>& weights);
   /** Pick uint64_t between 0 and UINT64_MAX. */
   uint64_t pick_uint64();
   /** Pick uint64_t between 'from' and 'to' (inclusive). */
   uint64_t pick_uint64(uint64_t from, uint64_t to);
   /** Pick with given probability, 100% = 1000. */
   bool pick_with_prob(uint32_t prob);
   /** Pick with probability of 50%. */
   bool flip_coin();
   /** Pick one out of three choices. */
   Choice pick_one_of_three();
   /** Pick random string of given length from set of 256 printable chars. */
   std::string pick_string(uint32_t len);
   /** Pick random string of given length from given character set. */
   std::string pick_string(std::string& chars, uint32_t len);
   /** Pick binary string of given length. */
   std::string pick_bin_string(uint32_t len);
   /** Pick decimal string of given length in binary representation. */
   std::string pick_dec_bin_string(uint32_t bin_len);
   /** Pick hexadecimal string of given length in binary representation. */
   std::string pick_hex_bin_string(uint32_t bin_len);
   /** Pick simple symbol string (as defined in SMT-LIB) of given length. */
   std::string pick_simple_symbol(uint32_t len);
   /** Pick piped symbol string (as defined in SMT-LIB) of given length. */
   std::string pick_piped_symbol(uint32_t len);

   /* Pick random element from given map. */
   template <typename TMap, typename TPicked>
   TPicked pick_from_map(const TMap& data);
   /* Pick random element from given set/vector. */
   template <typename TSet, typename TPicked>
   TPicked pick_from_set(const TSet& data);

  private:
    uint32_t d_seed;
    std::mt19937 d_rng;
    std::uniform_int_distribution<uint32_t> d_uint32_dist;
    std::uniform_int_distribution<uint64_t> d_uint64_dist;

    std::string d_bin_char_set = "01";
    std::string d_simple_symbol_char_set =
        "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+-/"
        "*=%?!.$_&<>@^~";
};

/* -------------------------------------------------------------------------- */

template <typename TMap, typename TPicked>
TPicked
RNGenerator::pick_from_map(const TMap& map)
{
  assert(!map.empty());
  auto it = map.begin();
  std::advance(it, pick_uint32() % map.size());
  return it->first;
}

template <typename TSet, typename TPicked>
TPicked
RNGenerator::pick_from_set(const TSet& set)
{
  assert(!set.empty());
  auto it = set.begin();
  std::advance(it, pick_uint32() % set.size());
  return *it;
}

/* -------------------------------------------------------------------------- */

std::string str_bin_to_hex(const std::string& str_bin);
std::string str_bin_to_dec(const std::string& str_bin);

uint64_t bv_special_value_ones_uint64(uint32_t bw);
uint64_t bv_special_value_min_signed_uint64(uint32_t bw);
uint64_t bv_special_value_max_signed_uint64(uint32_t bw);

bool is_bv_special_value_ones_uint64(uint32_t bw, uint64_t value);
bool is_bv_special_value_min_signed_uint64(uint32_t bw, uint64_t value);
bool is_bv_special_value_max_signed_uint64(uint32_t bw, uint64_t value);

std::string bv_special_value_zero_str(uint32_t bw);
std::string bv_special_value_one_str(uint32_t bw);
std::string bv_special_value_ones_str(uint32_t bw);
std::string bv_special_value_min_signed_str(uint32_t bw);
std::string bv_special_value_max_signed_str(uint32_t bw);

bool is_bv_special_value_zero_str(std::string& value);
bool is_bv_special_value_one_str(std::string& value);
bool is_bv_special_value_ones_str(std::string& value);
bool is_bv_special_value_min_signed_str(std::string& value);
bool is_bv_special_value_max_signed_str(std::string& value);

/* -------------------------------------------------------------------------- */

/**
 * Convert string to uint32_t.
 * Given string must not be empty or represent a negative number.
 */
uint32_t str_to_uint32(std::string& s);

/**
 * Convert string to uint64_t.
 * Given string must not be empty or represent a negative number.
 */
uint64_t str_to_uint64(std::string& s);

/**
 * Convert string given as a string enclosed with '\"' characters, e.g.,
 * "\"abc\"", to a string with the enclosing '\"' characters, e.g., "abc".
 */
std::string str_to_str(std::string& s);

/* -------------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& out,
                         const std::vector<uint32_t>& vector);

/* -------------------------------------------------------------------------- */

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

#define SMTMBT_WARN(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & WarnStream().stream()

#define SMTMBT_ABORT(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & AbortStream().stream()

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt

#endif
