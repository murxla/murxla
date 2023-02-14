/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include "util.hpp"

#include <sys/time.h>
#include <unistd.h>

#include <algorithm>
#include <cassert>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <limits>
#include <sstream>
#include <unordered_map>

#include "except.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

static std::unordered_map<std::string, std::string> s_bin_to_hex_lookup = {
    {"0", "0"},    {"00", "0"},   {"000", "0"},  {"0000", "0"}, {"1", "1"},
    {"01", "1"},   {"001", "1"},  {"0001", "1"}, {"10", "2"},   {"010", "2"},
    {"0010", "2"}, {"11", "3"},   {"011", "3"},  {"0011", "3"}, {"100", "4"},
    {"0100", "4"}, {"101", "5"},  {"0101", "5"}, {"110", "6"},  {"0110", "6"},
    {"111", "7"},  {"0111", "7"}, {"1000", "8"}, {"1001", "9"}, {"1010", "a"},
    {"1011", "b"}, {"1100", "c"}, {"1101", "d"}, {"1110", "e"}, {"1111", "f"}};

static std::unordered_map<char, std::string> s_hex_to_bin_lookup = {
    {'0', "0"},    {'1', "1"},    {'2', "10"},   {'3', "11"},   {'4', "100"},
    {'5', "101"},  {'6', "110"},  {'7', "111"},  {'8', "1000"}, {'9', "1001"},
    {'a', "1010"}, {'A', "1010"}, {'b', "1011"}, {'B', "1011"}, {'c', "1100"},
    {'C', "1100"}, {'d', "1101"}, {'D', "1101"}, {'e', "1110"}, {'E', "1110"},
    {'f', "1111"}, {'F', "1111"}};

/* -------------------------------------------------------------------------- */

namespace {
/** Strip leading zeros of given string. */
std::string
strip_zeros(std::string s)
{
  s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](unsigned char ch) {
            return ch != '0';
          }));
  return s;
}

/** Add two binary numbers given as strings. */
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

/** Multiply two binary numbers given as strings. */
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
  for (size_t i = 0, n = a.size(); i < n; ++i) res[bsize + i] = a[i];

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

/** Convert a digit to its binary representation; */
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
    size_t len = n - i >= 4 ? 4 : n - i;
    std::string chunk(len, 0);
    for (uint32_t j = 0; j <= len; ++j) chunk[len - j] = str_bin[n - i - j];
    stack.push_back(s_bin_to_hex_lookup.at(chunk));
  }
  for (size_t i = 0, n = stack.size(); i < n; ++i) ss << stack[n - 1 - i];
  return ss.str();
}

std::string
str_hex_to_bin(const std::string& str_hex)
{
  std::stringstream ss;
  for (size_t i = 0, n = str_hex.size(); i < n; ++i)
  {
    ss << s_hex_to_bin_lookup.at(str_hex[i]);
  }
  return ss.str();
}

std::string
str_bin_to_dec(const std::string& str_bin, bool sign)
{
  std::string _str_bin = str_bin;
  if (sign)
  {
    // negate
    for (auto& c : _str_bin) c = c == '1' ? '0' : '1';           // xor
    _str_bin = add_unbounded_bin_str(_str_bin, digit2bin('1'));  // + 1
  }

  std::string digits(_str_bin.size(), 0);

  // from MSB to LSB
  for (const auto& c : _str_bin)
  {
    // shift digits, with carry
    uint32_t carry = 0;
    for (auto& digit : digits)
    {
      uint32_t d = digit * 2 + carry;
      carry      = d > 9;
      digit      = static_cast<char>(d % 10);
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
  if (sign) return '-' + ss.str();
  return ss.str();
}

std::string
str_dec_to_bin(const std::string& str_dec)
{
  std::string res;
  bool is_neg = str_dec[0] == '-';
  size_t i    = is_neg ? 1 : 0;

  for (size_t n = str_dec.size(); i < n; ++i)
  {
    res = mult_unbounded_bin_str(res, "1010");                // * 10
    res = add_unbounded_bin_str(res, digit2bin(str_dec[i]));  // + digit
  }
  assert(strip_zeros(res) == res);
  assert(str_bin_to_dec(res) == (is_neg ? str_dec.substr(1) : str_dec));
  if (res.empty()) return "0";
  if (!is_neg) return res;
  /* negate */
  for (auto& c : res) c = c == '1' ? '0' : '1';      // xor
  res = add_unbounded_bin_str(res, digit2bin('1'));  // + 1
  return res;
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

/* -------------------------------------------------------------------------- */

uint32_t
str_to_uint32(const std::string& s)
{
  assert(!s.empty());
  assert(s[0] != '-');
  // throws exception if conversion not successful
  return static_cast<uint32_t>(std::stoul(s));
}

uint64_t
str_to_uint64(const std::string& s)
{
  assert(!s.empty());
  assert(s[0] != '-');
  return std::stoull(s);  // throws exception if conversion not successful
}

std::string
str_to_str(const std::string& s)
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

Terminal::Terminal() : d_is_terminal(isatty(fileno(stdout))) {}

bool
Terminal::is_term() const
{
  return d_is_terminal;
}

const std::string
Terminal::cr() const
{
  return code("\r");
}

void
Terminal::erase(std::ostream& out) const
{
  if (d_is_terminal)
  {
    out << "\33[2K" << cr() << std::flush;
  }
}
const std::string
Terminal::blue() const
{
  return code("\33[94m");
}
const std::string
Terminal::defaultcolor() const
{
  return code("\33[39m");
}
const std::string
Terminal::gray() const
{
  return code("\33[37m");
}
const std::string
Terminal::green() const
{
  return code("\33[92m");
}
const std::string
Terminal::red() const
{
  return code("\33[91m");
}

const std::string
Terminal::code(const std::string color) const
{
  return d_is_terminal ? color : "";
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
replace_suffix_file_name(const std::string& file_name,
                         const std::string& suffix)
{
  size_t pos = file_name.find_last_of('.');
  return file_name.substr(0, pos) + suffix;
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

  Terminal term;

  while (std::getline(file1, line1))
  {
    if (std::getline(file2, line2))
    {
      if (line1 == line2)
      {
        out << term.defaultcolor() << "  ";
      }
      else
      {
        out << term.red() << "x ";
      }
      out << std::left << std::setw(9) << line1;
      out << std::left << std::setw(9) << line2;
    }
    else
    {
      out << term.red() << "x ";
      out << std::left << std::setw(9) << line1;
    }
    out << std::endl;
  }
  while (std::getline(file2, line2))
  {
    out << term.red() << "x ";
    out << std::left << std::setw(9) << " ";
    out << std::left << std::setw(9) << line2 << std::endl;
  }
  out << term.defaultcolor() << std::flush;
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

std::tuple<uint32_t, std::string, std::vector<std::string>>
tokenize(const std::string& line)
{
  std::stringstream ss;
  std::string token;
  std::stringstream tokenstream(line);
  std::string seed, action;
  std::vector<std::string> tokens;
  bool open_str = false;

  /* Note: this std::getline() call also splits piped symbols that have
   *       spaces, e.g., "|a b|". We join these together again. */
  while (std::getline(tokenstream, token, ' '))
  {
    if (token.empty()) continue;
    if (seed.empty() && (token[0] < '0' || token[0] > '9'))
    {
      seed = "undefined";
    }
    if (seed.empty())
    {
      seed = token;
    }
    else if (action.empty())
    {
      action = token;
    }
    else if (open_str)
    {
      ss << " " << token;
      if (token[token.size() - 1] == '"')
      {
        open_str = false;
        tokens.push_back(ss.str());
      }
    }
    else if (token[0] == '"' && token[token.size() - 1] != '"')
    {
      open_str = true;
      ss << token;
    }
    else
    {
      tokens.push_back(token);
    }
  }
  return std::make_tuple(
      seed == "undefined" ? 0 : std::stoul(seed), action, tokens);
}

std::vector<std::string>
split(const std::string& s, const char delim)
{
  std::stringstream ss(s);
  std::string token;
  std::vector<std::string> res;
  while (std::getline(ss, token, delim))
  {
    res.push_back(token);
  }
  return res;
}

std::string&
rstrip(std::string& s)
{
  s.erase(std::find_if(s.rbegin(),
                       s.rend(),
                       [](unsigned char c) { return !std::isspace(c); })
              .base(),
          s.end());
  return s;
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla
