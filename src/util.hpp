#ifndef __MURXLA__UTIL_H
#define __MURXLA__UTIL_H

#include <cstdint>
#include <string>
#include <vector>

namespace murxla {

/* -------------------------------------------------------------------------- */

uint32_t uint32_to_value_in_range(uint32_t val, uint32_t from, uint32_t to);

/* -------------------------------------------------------------------------- */

/** Convert a binary string to a hexadecimal string. */
std::string str_bin_to_hex(const std::string& str_bin);
/** Convert a binary string to a decimal string. */
std::string str_bin_to_dec(const std::string& str_bin);
/** Convert a decimal string to a binary string. */
std::string str_dec_to_bin(const std::string& str_dec);

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
uint32_t str_to_uint32(const std::string& s);

/**
 * Convert string to uint64_t.
 * Given string must not be empty or represent a negative number.
 */
uint64_t str_to_uint64(const std::string& s);

/**
 * Convert string given as a string enclosed with '\"' characters, e.g.,
 * "\"abc\"", to a string with the enclosing '\"' characters, e.g., "abc".
 */
std::string str_to_str(const std::string& s);

/* -------------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& out,
                         const std::vector<uint32_t>& vector);

/* -------------------------------------------------------------------------- */

const std::string DEVNULL = "/dev/null";

/* -------------------------------------------------------------------------- */

class Terminal
{
 public:
  Terminal();

  bool is_term() const;

  const std::string cr() const;
  void erase(std::ostream& out) const;
  const std::string blue() const;
  const std::string defaultcolor() const;
  const std::string green() const;
  const std::string red() const;

 private:
  const std::string code(const std::string color) const;
  bool d_is_terminal;
};

/* -------------------------------------------------------------------------- */

std::string get_tmp_file_path(const std::string& filename,
                              const std::string& directory);

std::string prepend_path(const std::string& prefix,
                         const std::string& file_name);

std::string prepend_prefix_to_file_name(const std::string& prefix,
                                        const std::string& file_name);

std::string get_smt2_file_name(uint32_t seed,
                               const std::string& untrace_file_name);

std::ifstream open_input_file(const std::string& file_name, bool is_forked);

std::ofstream open_output_file(const std::string& file_name, bool is_forked);

bool compare_files(const std::string& file_name1,
                   const std::string& file_name2);

void diff_files(std::ostream& out,
                const std::string& file_name1,
                const std::string& file_name2,
                bool is_forked);

bool find_in_file(const std::string& file_name,
                  const std::string& s,
                  bool is_forked);

/* -------------------------------------------------------------------------- */

double get_cur_wall_time();

/* -------------------------------------------------------------------------- */

std::tuple<std::string, std::vector<std::string>> tokenize(
    const std::string& line);

/** Split string 's' by character 'delim'. */
std::vector<std::string> split(const std::string& s, const char delim);

/* -------------------------------------------------------------------------- */

}  // namespace murxla

#endif
