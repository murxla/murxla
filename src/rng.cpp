/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include "rng.hpp"

#include <unistd.h>

#include <algorithm>
#include <cassert>
#include <sstream>

#include "config.hpp"
#include "except.hpp"
#include "util.hpp"

/* -------------------------------------------------------------------------- */

#define MURXLA_PROB_MAX 1000 /* Maximum probability 100% = 1000. */

/* -------------------------------------------------------------------------- */

namespace murxla {

/* -------------------------------------------------------------------------- */

uint64_t
SeedGenerator::next()
{
  uint64_t cur_seed;
  cur_seed = d_seed;
  d_seed   = getpid();
  d_seed *= 129685499;
  d_seed += time(nullptr);
  d_seed *= 233755607;
  d_seed += cur_seed;
  d_seed *= 38259643;
  return cur_seed;
}

/* -------------------------------------------------------------------------- */

RNGenerator::RNGenerator(uint64_t seed) : d_seed(seed)
{
  d_rng.seed(seed);

  /* generate set of printable characters */
  uint32_t i = 32;
  for (uint32_t i = 32; i < 256; ++i)
  {
    // Skip characters not allowed in SMT2 symbols
    if (i == '|' || i == '\\' || i == 127) continue;
    d_printable_chars.push_back(i);
  }

  /* A-F */
  i = 65;
  std::generate_n(std::back_inserter(d_hex_chars), 6, [&i]() { return i++; });
  /* a-f */
  i = 97;
  std::generate_n(std::back_inserter(d_hex_chars), 6, [&i]() { return i++; });
  /* 0-9 */
  i = 48;
  std::generate_n(std::back_inserter(d_hex_chars), 10, [&i]() { return i++; });
}

void
RNGenerator::reseed(uint64_t seed)
{
  d_rng.seed(seed);
  d_seed = seed;
}

bool
RNGenerator::pick_with_prob(uint32_t prob)
{
  assert(prob <= MURXLA_PROB_MAX);
  uint32_t r = pick<uint32_t>(0, MURXLA_PROB_MAX - 1);
  return r < prob;
}

bool
RNGenerator::flip_coin()
{
  return pick_with_prob(500);
}

RNGenerator::Choice
RNGenerator::pick_one_of_three()
{
  uint32_t r = pick<uint32_t>(0, 8);
  if (r < 3) return Choice::FIRST;
  if (r < 6) return Choice::SECOND;
  assert(r < 9);
  return Choice::THIRD;
}

RNGenerator::Choice
RNGenerator::pick_one_of_four()
{
  uint32_t r = pick<uint32_t>(0, 11);
  if (r < 3) return Choice::FIRST;
  if (r < 6) return Choice::SECOND;
  if (r < 9) return Choice::THIRD;
  assert(r < 12);
  return Choice::FOURTH;
}

RNGenerator::Choice
RNGenerator::pick_one_of_five()
{
  uint32_t r = pick<uint32_t>(0, 14);
  if (r < 3) return Choice::FIRST;
  if (r < 6) return Choice::SECOND;
  if (r < 9) return Choice::THIRD;
  if (r < 12) return Choice::FOURTH;
  assert(r < 15);
  return Choice::FIFTH;
}

std::string
RNGenerator::pick_string(uint32_t len)
{
  if (len == 0) return "";
  std::string str(len, 0);
  std::generate_n(str.begin(), len, [this]() {
    return pick_from_set<std::vector<char>, char>(d_printable_chars);
  });
  return str;
}

std::string
RNGenerator::pick_string(std::string& chars, uint32_t len)
{
  assert(chars.size());
  if (len == 0) return "";
  std::string str(len, 0);
  std::generate_n(str.begin(), len, [this, &chars]() {
    return chars[pick<uint32_t>(0, chars.size() - 1)];
  });
  return str;
}

std::string
RNGenerator::pick_bin_string(uint32_t len)
{
  return pick_string(d_bin_char_set, len);
}

std::string
RNGenerator::pick_dec_bin_string(uint32_t bin_len, bool sign)
{
  std::string s = pick_bin_string(bin_len);
  bool neg      = sign && s[0] == '1';

  if (neg)
  {
    // convert two's complement negative number to positive number
    for (auto& c : s) c = c == '0' ? '1' : '0';  // invert
    bool overflow = true;
    for (size_t i = 0, n = s.size(); i < n; ++i)
    {
      size_t idx = n - i - 1;
      if (overflow)
      {
        if (s[idx] == '1')
        {
          // 1 + 1
          s[idx] = '0';
        }
        else
        {
          // 0 + 1
          s[idx]   = '1';
          overflow = false;
        }
      }
      else if (s[idx] == '1')
      {
        // 1 + 0
        s[idx] = '1';
      }
    }
  }

  std::string res = str_bin_to_dec(s);
  return neg ? "-" + res : res;
}

std::string
RNGenerator::pick_hex_bin_string(uint32_t bin_len)
{
  std::string s = pick_bin_string(bin_len);
  return str_bin_to_hex(s);
}

std::string
RNGenerator::pick_dec_int_string(uint32_t len)
{
  assert(len);
  std::string res;
  if (len > 1)
  {
    // numeral may not start with 0 if len > 1
    std::stringstream ss;
    ss << pick_from_set<std::vector<char>, char>(
        {'1', '2', '3', '4', '5', '6', '7', '8', '9'});
    std::string str(len - 1, 0);
    std::generate_n(str.begin(), len - 1, [this]() {
      return pick_from_set<std::vector<char>, char>(
          {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9'});
    });
    ss << str;
    res = ss.str();
  }
  else
  {
    res = std::string(len, 0);
    std::generate_n(res.begin(), len, [this]() {
      return pick_from_set<std::vector<char>, char>(
          {'1', '2', '3', '4', '5', '6', '7', '8', '9'});
    });
  }
  return res;
}

std::string
RNGenerator::pick_dec_real_string(uint32_t len)
{
  assert(len);
  if (len < 3)
  {
    return pick_dec_int_string(len);
  }
  uint32_t len0 = pick<uint32_t>(1, len);
  if (len0 > len - 2) return pick_dec_int_string(len);
  uint32_t len1 = len - len0 - 1;
  std::stringstream ss;
  ss << pick_dec_int_string(len0) << "." << pick_dec_int_string(len1);
  assert(ss.str().size() == len);
  return ss.str();
}

std::string
RNGenerator::pick_dec_rational_string(uint32_t nlen, uint32_t dlen)
{
  assert(nlen);
  assert(dlen);
  std::string num;
  std::string den;

  if (nlen > 1)
  {
    num = pick_dec_int_string(nlen);
  }
  else
  {
    // numerator may not be 0
    num = pick_from_set<std::vector<char>, char>(
        {'1', '2', '3', '4', '5', '6', '7', '8', '9'});
  }
  if (dlen > 1)
  {
    den = pick_dec_int_string(dlen);
  }
  else
  {
    // denominator must be > 1
    den = pick_from_set<std::vector<char>, char>(
        {'2', '3', '4', '5', '6', '7', '8', '9'});
  }
  std::stringstream ss;
  ss << num << "/" << den;
  return ss.str();
}

std::string
RNGenerator::pick_real_string()
{
  if (flip_coin())
  {
    return pick_dec_int_string(pick<uint32_t>(1, MURXLA_INT_LEN_MAX));
  }
  return pick_dec_real_string(pick<uint32_t>(1, MURXLA_REAL_LEN_MAX));
}

std::string
RNGenerator::pick_simple_symbol(uint32_t len)
{
  std::string s = pick_string(d_simple_symbol_char_set, len);
  return s;
}

std::string
RNGenerator::pick_piped_symbol(uint32_t len)
{
  assert(len);
  std::string s = pick_string(len);
  assert(s.size() == len);
  s[0]       = '|';
  s[len - 1] = '|';
  return s;
}

/**
 * Generate strings of the form
 *
 *  \ud3d2d1d0
 *  \u{d0}
 *  \u{d1d0}
 *  \u{d2d1d0}
 *  \u{d3d2d1d0}
 *  \u{d4d3d2d1d0}
 *
 * where d0 - d3 are hexadecimal digits and d4 is restricted to the range 0-2.
 */
std::string
RNGenerator::pick_unicode_character()
{
  uint32_t len = pick<uint32_t>(1, 5);
  std::vector<char> digits;

  for (uint32_t i = 0; i < std::min<uint32_t>(3, len); ++i)
  {
    digits.push_back(pick_from_set<std::vector<char>, char>(d_hex_chars));
  }

  bool use_braces = true;
  if (len == 5)
  {
    digits.push_back(pick<uint32_t>('0', '2'));
  }
  else if (len == 4)
  {
    use_braces = flip_coin();
  }

  std::stringstream ss;
  ss << "\\u";

  if (use_braces)
  {
    ss << "{";
  }

  for (auto it = digits.rbegin(); it != digits.rend(); ++it)
  {
    ss << *it;
  }

  if (use_braces)
  {
    ss << "}";
  }

  return ss.str();
}

std::string
RNGenerator::pick_string_literal(uint32_t len)
{
  assert(len);

  uint32_t len_ascii   = pick<uint32_t>(0, len);
  uint32_t len_unicode = len - len_ascii;

  std::vector<std::string> chars;

  // pick ASCII chars
  for (uint32_t i = 0; i < len_ascii; ++i)
  {
    chars.push_back(std::string(
        1, pick_from_set<std::vector<char>, char>(d_printable_chars)));
  }

  // pick escaped unicode chars
  for (uint32_t i = 0; i < len_unicode; ++i)
  {
    chars.push_back(pick_unicode_character());
  }

  std::shuffle(std::begin(chars), std::end(chars), d_rng);

  std::stringstream ss;
  for (auto s : chars)
  {
    ss << s;
  }

  return ss.str();
}

/* -------------------------------------------------------------------------- */

uint64_t
SolverSeedGenerator::next_solver_seed()
{
  d_cur_seed = pick<uint32_t>() % 100000;
  return d_cur_seed;
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla
