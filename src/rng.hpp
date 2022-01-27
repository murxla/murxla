/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
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
  /** Default Constructor. Starts from seed 0. */
  SeedGenerator() { next(); }
  /** Default Constructor. Starts from given seed. */
  explicit SeedGenerator(uint32_t s) : d_seed(s) {}
  /** Generate and return the next seed. */
  uint32_t next();

 private:
  /** The current seed. */
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

  /** Get the seed used for seeding the RNG on construction. */
  uint32_t get_seed() const { return d_seed; }
  /** Seed RNG with new seed. */
  void reseed(uint32_t seed);
  /** Get the RNG Mersenne Twister engine. */
  std::mt19937& get_engine() { return d_rng; }

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

  template <typename T, typename Iterator>
  T pick_weighted(const Iterator& begin, const Iterator& end);

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
  /**
   * Pick decimal string of given length in binary representation.
   * This will produce signed (that is, possibly negative) values if
   * 'sign' is true.
   */
  std::string pick_dec_bin_string(uint32_t bin_len, bool sign);
  /** Pick hexadecimal string of given length in binary representation. */
  std::string pick_hex_bin_string(uint32_t bin_len);
  /** Pick decimal integer string of given length. */
  std::string pick_dec_int_string(uint32_t len);
  /** Pick decimal real string of given length (no rationals). */
  std::string pick_dec_real_string(uint32_t len);
  /** Pick rational string with given lengths for numerator and denominator. */
  std::string pick_dec_rational_string(uint32_t nlen, uint32_t dlen);
  /**
   * Pick real string.
   * This picks either a decimal int or real string, with equal probability.
   */
  std::string pick_real_string();
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

/**
 * The seed generator for seeds for the RNG of the solver.
 * We cannot use SeedGenerator here since it is non-deterministic.
 */
class SolverSeedGenerator : public RNGenerator
{
 public:
  /** Constructor. */
  SolverSeedGenerator(uint32_t seed) : RNGenerator(seed) {}
  /** Generate and return the next seed for the solver RNG. */
  uint32_t next_solver_seed();
  /** Get the current seed. */
  uint32_t seed() const { return d_cur_seed; }
  /** Set the current seed. */
  void set_seed(uint32_t s) { d_cur_seed = s; }
  /** Set to true if we are currently untracing. */
  void set_untrace_mode(bool b) { d_is_untrace_mode = b; }
  /** Return true if we are currently untracing. */
  bool is_untrace_mode() { return d_is_untrace_mode; }

 private:
  /**
   * The current (generated) seed.
   * Not to be confused with the seed used for seeding the generator on
   * construction (which is RnGenerator::d_seed).
   */
  uint32_t d_cur_seed = 0;
  /** True if we are currently untracing. */
  bool d_is_untrace_mode = false;
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

template <typename T, typename Iterator>
T
RNGenerator::pick_weighted(const Iterator& begin, const Iterator& end)
{
  std::discrete_distribution<T> dist(begin, end);
  return dist(d_rng);
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla

#endif
