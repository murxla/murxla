#include "util.hpp"

#include <stdlib.h>
#include <sys/time.h>
#include <unistd.h>

#include <algorithm>
#include <bitset>
#include <cassert>
#include <cstring>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <limits>
#include <sstream>
#include <vector>

#include "except.hpp"

/* -------------------------------------------------------------------------- */

#define MURXLA_PROB_MAX 1000 /* Maximum probability 100% = 1000. */

/* -------------------------------------------------------------------------- */

namespace murxla {

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
  for (uint32_t i = 32; i < 256; ++i)
  {
    // Skip characters not allowed in SMT2 symbols
    if (i == '|' || i == '\\' || i == 127)
      continue;
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

std::mt19937&
RNGenerator::get_engine()
{
  return d_rng;
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

uint32_t
uint32_to_value_in_range(uint32_t val, uint32_t from, uint32_t to)
{
  assert(from <= to);

  from = from == UINT32_MAX ? UINT32_MAX - 1 : from;
  to   = to == UINT32_MAX ? UINT32_MAX - 1 : to;
  val %= to - from + 1;
  val += from;
  return val;
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

namespace {
std::string
strip_zeros(std::string s)
{
  s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](unsigned char ch) {
            return ch != '0';
          }));
  return s;
}

std::string
add_unbounded_bin_str(std::string a, std::string b)
{
  a = strip_zeros(a);
  b = strip_zeros(b);

  if (a.empty()) return b;
  if (b.empty()) return a;

  size_t asize = a.size();
  size_t bsize = b.size();
  size_t rsize = (asize < bsize) ? bsize + 1 : asize + 1;
  std::string res(rsize, '0');

  char c = '0';
  for (uint32_t i = 0; i < rsize; ++i)
  {
    char x             = i < asize ? a[asize - i - 1] : '0';
    char y             = i < bsize ? b[bsize - i - 1] : '0';
    char s             = x ^ y ^ c;
    c                  = (x & y) | (x & c) | (y & c);
    res[rsize - i - 1] = s;
  }
  return strip_zeros(res);
}

std::string
mult_unbounded_bin_str(std::string a, std::string b)
{
  a = strip_zeros(a);

  if (a.empty()) return a;

  if (a[0] == '1' && !a[1]) return b;

  b = strip_zeros(b);

  if (b.empty()) return b;

  if (b[0] == '1' && !b[1]) return a;

  size_t asize = a.size();
  size_t bsize = b.size();
  size_t rsize = asize + bsize;

  std::string res(rsize, '0');
  for (uint32_t i = 0, n = a.size(); i < n; ++i) res[bsize + i] = a[i];

  for (size_t i = 0; i < asize; ++i)
  {
    char m = res[rsize - 1];
    char c = '0';

    if (m == '1')
    {
      for (size_t j = bsize; j > 0; --j)
      {
        char x     = b[j - 1];
        char y     = res[j - 1];
        char s     = x ^ y ^ c;
        c          = (x & y) | (x & c) | (y & c);
        res[j - 1] = s;
      }
    }
    std::string subres = res.substr(0, rsize - 1);
    res.replace(res.begin() + 1, res.end(), subres.begin(), subres.end());
    res[0] = c;
  }

  return res;
}

const char*
digit2bin(char ch)
{
  assert('0' <= ch);
  assert(ch <= '9');

  const char* table[10] = {
      "",
      "1",
      "10",
      "11",
      "100",
      "101",
      "110",
      "111",
      "1000",
      "1001",
  };

  return table[ch - '0'];
}
}  // namespace

std::string
str_dec_to_bin(const std::string& str_dec)
{
  std::string res;

  for (size_t i = 0, n = str_dec.size(); i < n; ++i)
  {
    res = mult_unbounded_bin_str(res, "1010");                // * 10
    res = add_unbounded_bin_str(res, digit2bin(str_dec[i]));  // + digit
  }
  assert(strip_zeros(res) == res);
  assert(str_bin_to_dec(res) == str_dec);
  if (res.size()) return res;
  return "0";
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

std::string
get_tmp_file_path(const std::string& filename, const std::string& directory)
{
  std::filesystem::path p(directory);
  p /= filename;
  return p.string();
}

std::string
prepend_path(const std::string& prefix, const std::string& file_name)
{
  std::filesystem::path p(prefix);
  p /= file_name;
  return p.string();
}

std::string
prepend_prefix_to_file_name(const std::string& prefix,
                            const std::string& file_name)
{
  size_t pos = file_name.find_last_of('/');
  std::stringstream ss;
  if (pos == std::string::npos)
  {
    ss << prefix << file_name;
  }
  else
  {
    std::string path = file_name.substr(0, pos);
    std::string file = file_name.substr(pos + 1);
    ss << path << "/" << prefix << file;
  }
  return ss.str();
}

std::string
get_smt2_file_name(uint32_t seed, std::string& untrace_file_name)
{
  std::stringstream ss;
  if (untrace_file_name.empty())
  {
    ss << "murxla-" << seed << ".smt2";
  }
  else
  {
    auto path = std::filesystem::path(untrace_file_name);
    ss << path.replace_extension(".smt2").c_str();
  }
  return ss.str();
}

std::ifstream
open_input_file(const std::string& file_name, bool is_forked)
{
  std::ifstream res(file_name);
  MURXLA_EXIT_ERROR_FORK(!res.is_open(), is_forked)
      << "unable to open input file '" << file_name << "'";
  return res;
}

std::ofstream
open_output_file(const std::string& file_name, bool is_forked)
{
  std::ofstream res(file_name, std::ofstream::out | std::ofstream::trunc);
  MURXLA_EXIT_ERROR_FORK(!res.is_open(), is_forked)
      << "unable to open output file '" << file_name << "'";
  return res;
}

bool
compare_files(const std::string& file_name1, const std::string& file_name2)
{
  std::ifstream file1(file_name1, std::ifstream::binary | std::ifstream::ate);
  std::ifstream file2(file_name2, std::ifstream::binary | std::ifstream::ate);

  if (file1.fail() || file2.fail())
  {
    return false;
  }

  if (file1.tellg() != file2.tellg())
  {
    return false;
  }

  file1.seekg(0, file1.beg);
  file2.seekg(0, file2.beg);
  return std::equal(std::istreambuf_iterator<char>(file1.rdbuf()),
                    std::istreambuf_iterator<char>(),
                    std::istreambuf_iterator<char>(file2.rdbuf()));
}

void
diff_files(std::ostream& out,
           const std::string& file_name1,
           const std::string& file_name2,
           bool is_forked)
{
  std::ifstream file1 = open_input_file(file_name1, is_forked);
  std::ifstream file2 = open_input_file(file_name2, is_forked);
  std::string line1, line2;

  while (std::getline(file1, line1))
  {
    if (std::getline(file2, line2))
    {
      if (line1 == line2)
      {
        out << COLOR_DEFAULT << "  ";
      }
      else
      {
        out << COLOR_RED << "x ";
      }
      out << std::left << std::setw(9) << line1;
      out << std::left << std::setw(9) << line2;
    }
    else
    {
      out << COLOR_RED << "x ";
      out << std::left << std::setw(9) << line1;
    }
    out << std::endl;
  }
  while (std::getline(file2, line2))
  {
    out << COLOR_RED << "x ";
    out << std::left << std::setw(9) << " ";
    out << std::left << std::setw(9) << line2 << std::endl;
  }
  out << COLOR_DEFAULT << std::flush;
  file1.close();
  file2.close();
}

bool
find_in_file(const std::string& file_name, const std::string& s, bool is_forked)
{
  std::ifstream file = open_input_file(file_name, is_forked);
  std::string line;
  while (std::getline(file, line))
  {
    if (line.find(s) != std::string::npos) return true;
  }
  return false;
}

/* -------------------------------------------------------------------------- */

double
get_cur_wall_time()
{
  struct timeval time;
  MURXLA_EXIT_ERROR(gettimeofday(&time, nullptr)) << "failed to get time";
  return (double) time.tv_sec + (double) time.tv_usec / 1000000;
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla
