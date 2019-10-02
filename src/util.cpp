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

RNGenerator::RNGenerator(uint32_t seed) : d_seed(seed) { d_rng.seed(seed); }

uint32_t
RNGenerator::pick_uint32()
{
  return d_uint32_dist(d_rng);
}

uint32_t
RNGenerator::pick_uint32(uint32_t from, uint32_t to)
{
  assert(from <= to);

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
  assert(from <= to);

  uint64_t res = pick_uint64();

  from = from == UINT64_MAX ? UINT64_MAX - 1 : from;
  to   = to == UINT64_MAX ? UINT64_MAX - 1 : to;
  res %= to - from + 1;
  res += from;
  return res;
}

bool
RNGenerator::pick_with_prob(uint32_t prob)
{
  assert(prob <= SMTMBT_PROB_MAX);
  uint32_t r = pick_uint32(0, SMTMBT_PROB_MAX - 1);
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
  uint32_t r = pick_uint32(0, 8);
  if (r < 3) return Choice::FIRST;
  if (r < 6) return Choice::SECOND;
  assert(r < 9);
  return Choice::THIRD;
}

std::string
RNGenerator::pick_string(uint32_t len)
{
  if (len == 0) return "";
  std::string str(len, 0);
  std::generate_n(str.begin(), len, [this]() { return pick_uint32(32, 255); });
  return str;
}

std::string
RNGenerator::pick_string(std::string& chars, uint32_t len)
{
  assert(chars.size());
  if (len == 0) return "";
  std::string str(len, 0);
  std::generate_n(str.begin(), len, [this, &chars]() {
    return chars[pick_uint32(0, chars.size() - 1)];
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
RNGenerator::pick_simple_symbol(uint32_t len)
{
  std::string s = pick_string(d_simple_symbol_char_set, len);
  std::cout << "picked simple symbol string: '" << s << "'" << std::endl;
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
  std::cout << "picked piped symbol string: '" << s << "'" << std::endl;
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
  return bw == 1 ? 1u : bv_special_value_ones_uint64(bw - 1);
}

bool
is_bv_special_value_ones_uint64(uint32_t bw, uint64_t value)
{
  return value == ((~0u) >> (64 - bw));
}

bool
is_bv_special_value_min_signed_uint64(uint32_t bw, uint64_t value)
{
  return value == (1u << (bw - 1));
}

bool
is_bv_special_value_max_signed_uint64(uint32_t bw, uint64_t value)
{
  return value == bv_special_value_ones_uint64(bw - 1);
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
  res[res.size()] = '1';
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

TraceStream::TraceStream() { stream(); }

TraceStream::~TraceStream() { flush(); }

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
