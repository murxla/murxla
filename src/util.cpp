#include "util.hpp"

#include <stdlib.h>
#include <unistd.h>
#include <algorithm>
#include <bitset>
#include <cassert>
#include <ctime>
#include <iostream>
#include <limits>
#include <sstream>

/* -------------------------------------------------------------------------- */

#define SMTMBT_PROB_MAX 1000 /* Maximum probability 100% = 1000. */

/* -------------------------------------------------------------------------- */

namespace smtmbt {

/* -------------------------------------------------------------------------- */

static std::unordered_map<std::string, std::string> s_hex_lookup = {
    {"0", "0"},    {"00", "0"},   {"000", "0"},  {"0000", "0"},
    {"1", "1"},    {"01", "1"},   {"001", "1"},  {"0001", "1"},
    {"10", "2"},   {"010", "2"},  {"0010", "2"},
    {"11", "3"},   {"011", "3"},  {"0011", "3"},
    {"100", "4"},  {"0100", "4"},
    {"101", "5"},  {"0101", "5"},
    {"110", "6"},  {"0110", "6"},
    {"111", "7"},  {"0111", "7"},
    {"1000", "8"}, {"1001", "9"}, {"1010", "a"}, {"1011", "b"},
    {"1100", "c"}, {"1101", "d"}, {"1110", "e"}, {"1111", "f"}};

/* -------------------------------------------------------------------------- */

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

/* -------------------------------------------------------------------------- */

RNGenerator::RNGenerator(uint32_t seed) : d_seed(seed)
{
  d_rng.seed(seed);

  /* generate set of printable characters */
  uint32_t i = 32;
  std::generate_n(
      std::back_inserter(d_printable_chars), 95, [&i]() { return i++; });
  i = 128;
  std::generate_n(
      std::back_inserter(d_printable_chars), 128, [&i]() { return i++; });
}

std::mt19937&
RNGenerator::get_engine()
{
  return d_rng;
}

bool
RNGenerator::pick_with_prob(uint32_t prob)
{
  assert(prob <= SMTMBT_PROB_MAX);
  uint32_t r = pick<uint32_t>(0, SMTMBT_PROB_MAX - 1);
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
RNGenerator::pick_dec_bin_string(uint32_t bin_len)
{
  std::string s = pick_bin_string(bin_len);
  return str_bin_to_dec(s);
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
  std::cout << "n " << nlen << " '" << num << "' d " << dlen << " '" << den
            << "'" << std::endl;
  return ss.str();
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

/* -------------------------------------------------------------------------- */

std::string
str_bin_to_hex(const std::string& str_bin)
{
  std::stringstream ss;
  std::vector<std::string> stack;
  for (size_t i = 0, n = str_bin.size(); i < n; i += 4)
  {
    uint32_t len = n - i >= 4 ? 4 : n - i;
    std::string chunk(len, 0);
    for (uint32_t j = 0; j <= len; ++j) chunk[len - j] = str_bin[n - i - j];
    stack.push_back(s_hex_lookup.at(chunk));
  }
  for (size_t i = 0, n = stack.size(); i < n; ++i) ss << stack[n - 1 - i];
  return ss.str();
}

std::string
str_bin_to_dec(const std::string& str_bin)
{
  std::string digits(str_bin.size(), 0);

  // from MSB to LSB
  for (const auto& c : str_bin)
  {
    // shift digits, with carry
    uint32_t carry = 0;
    for (auto& digit : digits)
    {
      uint32_t d = digit * 2 + carry;
      carry      = d > 9;
      digit      = d % 10;
    }
    // add new bit
    if (c == '1') digits[0] |= 1;
  }

  // Note: digits are in reverse order, with leading zeros on the right
  size_t pos = 0;
  size_t n   = digits.size();
  for (pos = 0; pos <= n; ++pos)
  {
    if (digits[n - pos] != 0) break;
  }
  std::stringstream ss;
  if (pos > n) return "0";
  for (size_t i = pos; i <= n; ++i)
  {
    ss << ((char) (digits[n - i] + '0'));
  }
  return ss.str();
}

uint64_t
bv_special_value_ones_uint64(uint32_t bw)
{
  assert(bw > 0);
  assert(bw <= 64);
  uint64_t ones = ~((uint64_t) 0u);
  return bw == 64 ? ones : ~(ones << bw);
}

uint64_t
bv_special_value_min_signed_uint64(uint32_t bw)
{
  assert(bw <= 64);
  return ((uint64_t) 1u) << (bw - 1);
}

uint64_t
bv_special_value_max_signed_uint64(uint32_t bw)
{
  return bw == 1 ? 0u : bv_special_value_ones_uint64(bw - 1);
}

bool
is_bv_special_value_ones_uint64(uint32_t bw, uint64_t value)
{
  if (bw > 64) return false;
  return value == bv_special_value_ones_uint64(bw);
}

bool
is_bv_special_value_min_signed_uint64(uint32_t bw, uint64_t value)
{
  if (bw > 64) return false;
  return value == bv_special_value_min_signed_uint64(bw);
}

bool
is_bv_special_value_max_signed_uint64(uint32_t bw, uint64_t value)
{
  if (bw > 64) return false;
  return value == bv_special_value_max_signed_uint64(bw);
}

std::string
bv_special_value_zero_str(uint32_t bw)
{
  return std::string(bw, '0');
}

std::string
bv_special_value_one_str(uint32_t bw)
{
  std::string res(bw, '0');
  res[res.size() - 1] = '1';
  return res;
}

std::string
bv_special_value_ones_str(uint32_t bw)
{
  return std::string(bw, '1');
}

std::string
bv_special_value_min_signed_str(uint32_t bw)
{
  std::string res(bw, '0');
  res[0] = '1';
  return res;
}

std::string
bv_special_value_max_signed_str(uint32_t bw)
{
  std::string res(bw, '1');
  res[0] = '0';
  return res;
}

bool
is_bv_special_value_zero_str(std::string& value)
{
  for (const auto& c : value)
  {
    if (c != '0') return false;
  }
  return true;
}

bool
is_bv_special_value_one_str(uint32_t bw, std::string& value)
{
  size_t n = value.size();
  for (size_t i = 0; i < n; ++i)
  {
    if (value[i] != '0') return false;
  }
  if (value[n] != '1') return false;
  return true;
}

bool
is_bv_special_value_ones_str(uint32_t bw, std::string& value)
{
  for (const auto& c : value)
  {
    if (c != '1') return false;
  }
  return true;
}

bool
is_bv_special_value_min_signed_str(std::string& value)
{
  if (value[0] != '1') return false;
  for (size_t i = 1, n = value.size(); i <= n; ++i)
  {
    if (value[i] != '0') return false;
  }
  return true;
}

bool
is_bv_special_value_max_signed_str(std::string& value)
{
  if (value[0] != '0') return false;
  for (size_t i = 1, n = value.size(); i <= n; ++i)
  {
    if (value[i] != '1') return false;
  }
  return true;
}

/* -------------------------------------------------------------------------- */

uint32_t
str_to_uint32(std::string& s)
{
  assert(!s.empty());
  assert(s[0] != '-');
  return std::stoul(s);  // throws exception if conversion not successful
}

uint64_t
str_to_uint64(std::string& s)
{
  assert(!s.empty());
  assert(s[0] != '-');
  return std::stoull(s);  // throws exception if conversion not successful
}

std::string
str_to_str(std::string& s)
{
  assert(s.size() >= 2);
  assert(s[0] == '"');
  assert(s[s.size() - 1] == '"');
  if (s.size() == 2) return "";
  return s.substr(1, s.size() - 2);
}

/* -------------------------------------------------------------------------- */

std::ostream&
operator<<(std::ostream& out, const std::vector<uint32_t>& vector)
{
  for (const uint32_t v : vector) out << " " << v;
  return out;
}

/* -------------------------------------------------------------------------- */

WarnStream::WarnStream() { stream() << "smtmbt: WARNING: "; }

WarnStream::~WarnStream() { flush(); }

std::ostream&
WarnStream::stream()
{
  return std::cout;
}

void
WarnStream::flush()
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

/* -------------------------------------------------------------------------- */
}  // namespace smtmbt
