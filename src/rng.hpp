#ifndef __MURXLA__RNG_H
#define __MURXLA__RNG_H

#include <cassert>
#include <cstdint>
#include <random>
#include <unordered_map>
#include <vector>

namespace murxla {

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
  /**
   * The values for the selected choice when picking from multiple choices,
   * see, e.g., pick_one_of_three().
   */
  enum Choice
  {
    FIRST,
    SECOND,
    THIRD,
    FOURTH,
    FIFTH,
  };

  /** Constructor. */
  explicit RNGenerator(uint32_t seed = 0);

  /** Get the RNG Mersenne Twister engine. */
  std::mt19937& get_engine();

  /** Pick an integral number with type T. */
  template <typename T,
            typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
  T pick()
  {
    std::uniform_int_distribution<T> dist;
    return dist(d_rng);
  }

  /**
   * Pick an integral number with type T between 'from' and 'to' (inclusive).
   */
  template <typename T,
            typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
  T pick(T from, T to)
  {
    std::uniform_int_distribution<T> dist(from, to);
    return dist(d_rng);
  }

  /** Pick a floating point number with type T. */
  template <
      typename T,
      typename std::enable_if<std::is_floating_point<T>::value, int>::type = 0>
  T pick()
  {
    std::uniform_real_distribution<T> dist;
    return dist(d_rng);
  }

  /** Pick a floating point number with type T between 'from' and 'to'
   * (inclusive). */
  template <
      typename T,
      typename std::enable_if<std::is_floating_point<T>::value, int>::type = 0>
  T pick(T from, T to)
  {
    std::uniform_real_distribution<T> dist(from, to);
    return dist(d_rng);
  }

  /**
   * Pick uint32_t between 0 and weights.size(), weighted by the given weights.
   * The probability to pick each number is w/S with w its weight and S the
   * sum of all weights.
   */
  template <typename T>
  T pick_weighted(std::vector<T>& weights);

  template <typename T,
            typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
  T pick_weighted(T from, T to);

  /** Pick with given probability, 100% = 1000. */
  bool pick_with_prob(uint32_t prob);
  /** Pick with probability of 50%. */
  bool flip_coin();
  /** Pick one out of three choices. */
  Choice pick_one_of_three();
  /** Pick one out of four choices. */
  Choice pick_one_of_four();
  /** Pick one out of five choices. */
  Choice pick_one_of_five();

  /** Pick random string of given length from set of printable chars. */
  std::string pick_string(uint32_t len);
  /** Pick random string of given length from given character set. */
  std::string pick_string(std::string& chars, uint32_t len);
  /** Pick binary string of given length. */
  std::string pick_bin_string(uint32_t len);
  /** Pick decimal string of given length in binary representation. */
  std::string pick_dec_bin_string(uint32_t bin_len);
  /** Pick hexadecimal string of given length in binary representation. */
  std::string pick_hex_bin_string(uint32_t bin_len);
  /** Pick decimal integer string of given length. */
  std::string pick_dec_int_string(uint32_t len);
  /** Pick decimal real string of given length (no rationals). */
  std::string pick_dec_real_string(uint32_t len);
  /** Pick rational string with given lengths for numerator and denominator. */
  std::string pick_dec_rational_string(uint32_t nlen, uint32_t dlen);
  /** Pick simple symbol string (as defined in SMT-LIB) of given length. */
  std::string pick_simple_symbol(uint32_t len);
  /** Pick piped symbol string (as defined in SMT-LIB) of given length. */
  std::string pick_piped_symbol(uint32_t len);
  /** Pick escaped unicode character (theory of strings) */
  std::string pick_unicode_character();
  /** Pick string literal (theory of strings) */
  std::string pick_string_literal(uint32_t len);

  /* Pick random element from given map. */
  template <typename TMap, typename TPicked>
  TPicked pick_from_map(const TMap& data);
  /* Pick random element from given set/vector. */
  template <typename TSet, typename TPicked>
  TPicked pick_from_set(const TSet& data);

 private:
  uint32_t d_seed;
  std::mt19937 d_rng;

  /** The character set for binary strings. */
  std::string d_bin_char_set = "01";
  /** The character set for (non-piped) symbol strings. */
  std::string d_simple_symbol_char_set =
      "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+-/"
      "*=%?!.$_&<>@^~";
  /** The set of printable characters: 32-126 and 128-255 (decimal). */
  std::vector<char> d_printable_chars;
  /** The set of hexadecimal characters */
  std::vector<char> d_hex_chars;
};

/* -------------------------------------------------------------------------- */

template <typename TMap, typename TPicked>
TPicked
RNGenerator::pick_from_map(const TMap& map)
{
  assert(!map.empty());
  auto it = map.begin();
  std::advance(it, pick<uint32_t>() % map.size());
  return it->first;
}

template <typename TSet, typename TPicked>
TPicked
RNGenerator::pick_from_set(const TSet& set)
{
  assert(!set.empty());
  auto it = set.begin();
  std::advance(it, pick<uint32_t>() % set.size());
  return *it;
}

template <typename T>
T
RNGenerator::pick_weighted(std::vector<T>& weights)
{
  std::discrete_distribution<T> dist(weights.begin(), weights.end());
  return dist(d_rng);
}

template <typename T,
          typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
T
RNGenerator::pick_weighted(T from, T to)
{
  assert(to >= from);
  std::vector<T> weights;
  T diff = to - from;
  for (T i = 0; i < diff; ++i)
  {
    weights.push_back(diff - i);
  }
  std::discrete_distribution<T> dist(weights.begin(), weights.end());
  return dist(d_rng) + from;
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla

#endif
