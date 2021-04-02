#include <sstream>
#include "gtest/gtest.h"
#include "util.hpp"

using namespace murxla;

TEST(util, str_bin_to_hex)
{
  ASSERT_EQ(str_bin_to_hex("0"), "0");
  ASSERT_EQ(str_bin_to_hex("0000"), "0");
  ASSERT_EQ(str_bin_to_hex("000000"), "00");
  ASSERT_EQ(str_bin_to_hex("00000000"), "00");

  ASSERT_EQ(str_bin_to_hex("1"), "1");
  ASSERT_EQ(str_bin_to_hex("0001"), "1");
  ASSERT_EQ(str_bin_to_hex("000001"), "01");
  ASSERT_EQ(str_bin_to_hex("00000001"), "01");

  ASSERT_EQ(str_bin_to_hex("1"), "1");
  ASSERT_EQ(str_bin_to_hex("1111"), "f");
  ASSERT_EQ(str_bin_to_hex("001111"), "0f");
  ASSERT_EQ(str_bin_to_hex("111111"), "3f");
  ASSERT_EQ(str_bin_to_hex("11111111"), "ff");
  ASSERT_EQ(str_bin_to_hex("111111111111"), "fff");
  ASSERT_EQ(str_bin_to_hex("1111111111111111"), "ffff");
  ASSERT_EQ(str_bin_to_hex("11111111111111111"), "1ffff");

  ASSERT_EQ(
      str_bin_to_hex(
          "01010101010101010101010101010101010101010101010101010101010101010"),
      "0aaaaaaaaaaaaaaaa");
  ASSERT_EQ(
      str_bin_to_hex(
          "10101010101010101010101010101010101010101010101010101010101010101"),
      "15555555555555555");
  ASSERT_EQ(
      str_bin_to_hex(
          "1111111011011100101110101001100001110110010101000011001000010000"),
      "fedcba9876543210");
}

TEST(util, str_bin_to_dec)
{
  ASSERT_EQ(str_bin_to_dec("0"), "0");
  ASSERT_EQ(str_bin_to_dec("0000"), "0");
  ASSERT_EQ(str_bin_to_dec("000000"), "0");
  ASSERT_EQ(str_bin_to_dec("00000000"), "0");

  ASSERT_EQ(str_bin_to_dec("1"), "1");
  ASSERT_EQ(str_bin_to_dec("0001"), "1");
  ASSERT_EQ(str_bin_to_dec("000001"), "1");
  ASSERT_EQ(str_bin_to_dec("00000001"), "1");

  ASSERT_EQ(str_bin_to_dec("1"), "1");
  ASSERT_EQ(str_bin_to_dec("1111"), "15");
  ASSERT_EQ(str_bin_to_dec("001111"), "15");
  ASSERT_EQ(str_bin_to_dec("111111"), "63");
  ASSERT_EQ(str_bin_to_dec("11111111"), "255");
  ASSERT_EQ(str_bin_to_dec("111111111111"), "4095");
  ASSERT_EQ(str_bin_to_dec("1111111111111111"), "65535");
  ASSERT_EQ(str_bin_to_dec("11111111111111111"), "131071");

  ASSERT_EQ(
      str_bin_to_dec(
          "01010101010101010101010101010101010101010101010101010101010101010"),
      "12297829382473034410");
  ASSERT_EQ(
      str_bin_to_dec(
          "10101010101010101010101010101010101010101010101010101010101010101"),
      "24595658764946068821");
  ASSERT_EQ(
      str_bin_to_dec(
          "1111111011011100101110101001100001110110010101000011001000010000"),
      "18364758544493064720");
}

TEST(util, bv_special_value_ones_uint64)
{
  for (uint32_t i = 1; i <= 64; ++i)
  {
    uint64_t res = bv_special_value_ones_uint64(i);
    uint64_t mask;
    for (uint32_t j = 0; j < i; ++j)
    {
      mask = ((uint64_t) 1u) << j;
      ASSERT_EQ(res & mask, mask);
    }
    for (uint32_t j = i; j <= 64; ++j)
    {
      mask = j == 64 ? 0u : ((uint64_t) 1u) << j;
      mask = ~mask;
      ASSERT_EQ(res | mask, mask);
    }
  }
}

TEST(util, bv_special_value_min_signed_uint64)
{
  for (uint32_t i = 1; i <= 64; ++i)
  {
    uint64_t res      = bv_special_value_min_signed_uint64(i);
    uint64_t expected = 1;
    for (uint32_t j = 1; j < i; ++j) expected *= 2;
    ASSERT_EQ(expected, res);
  }
}

TEST(util, bv_special_value_max_signed_uint64)
{
  for (uint32_t i = 1; i <= 64; ++i)
  {
    uint64_t res = bv_special_value_max_signed_uint64(i);
    uint64_t mask;
    for (uint32_t j = 0; j < i - 1; ++j)
    {
      mask = ((uint64_t) 1u) << j;
      ASSERT_EQ(res & mask, mask);
    }
    for (uint32_t j = i - 1; j <= 64; ++j)
    {
      mask = j == 64 ? 0u : ((uint64_t) 1u) << j;
      mask = ~mask;
      ASSERT_EQ(res | mask, mask);
    }
  }
}

TEST(util, is_bv_special_value_ones_uint64)
{
  ASSERT_EQ(is_bv_special_value_ones_uint64(1, 0u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(1, 1u), true);

  ASSERT_EQ(is_bv_special_value_ones_uint64(2, 0u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(2, 1u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(2, 2u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(2, 3u), true);

  ASSERT_EQ(is_bv_special_value_ones_uint64(7, 0u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(7, 1u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(7, 3u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(7, 5u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(7, 127u), true);

  ASSERT_EQ(is_bv_special_value_ones_uint64(64, 0u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(64, 1u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(64, 2863311530u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(64, 12297829382473034410u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(64, 18446744069414584320u), false);
  ASSERT_EQ(is_bv_special_value_ones_uint64(64, UINT64_MAX), true);
}

TEST(util, is_bv_special_value_min_signed_uint64)
{
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(1, 0u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(1, 1u), true);

  ASSERT_EQ(is_bv_special_value_min_signed_uint64(2, 0u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(2, 1u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(2, 3u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(2, 2u), true);

  ASSERT_EQ(is_bv_special_value_min_signed_uint64(7, 0u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(7, 1u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(7, 3u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(7, 5u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(7, 127u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(7, 64u), true);

  ASSERT_EQ(is_bv_special_value_min_signed_uint64(64, 0u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(64, 1u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(64, 2863311530u), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(64, 12297829382473034410u),
            false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(64, UINT64_MAX << 32), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(64, UINT64_MAX), false);
  ASSERT_EQ(is_bv_special_value_min_signed_uint64(64, 9223372036854775808u),
            true);
}

TEST(util, is_bv_special_value_max_signed_uint64)
{
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(1, 1u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(1, 0u), true);

  ASSERT_EQ(is_bv_special_value_max_signed_uint64(2, 0u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(2, 2u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(2, 3u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(2, 1u), true);

  ASSERT_EQ(is_bv_special_value_max_signed_uint64(7, 0u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(7, 1u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(7, 3u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(7, 5u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(7, 127u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(7, 63u), true);

  ASSERT_EQ(is_bv_special_value_max_signed_uint64(64, 0u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(64, 1u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(64, 2863311530u), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(64, 12297829382473034410u),
            false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(64, 18446744069414584320u),
            false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(64, UINT64_MAX), false);
  ASSERT_EQ(is_bv_special_value_max_signed_uint64(64, 9223372036854775807u),
            true);
}

TEST(util, bv_special_value_zero_str)
{
  for (uint32_t i = 1; i < 128; ++i)
    ASSERT_EQ(bv_special_value_zero_str(i), std::string(i, '0'));
}

TEST(util, bv_special_value_ones_str)
{
  for (uint32_t i = 1; i < 128; ++i)
    ASSERT_EQ(bv_special_value_ones_str(i), std::string(i, '1'));
}

TEST(util, bv_special_value_one_str)
{
  for (uint32_t i = 1; i < 128; ++i)
  {
    std::stringstream ss;
    if (i > 1) ss << std::string(i - 1, '0');
    ss << '1';
    ASSERT_EQ(bv_special_value_one_str(i), ss.str());
  }
}

TEST(util, bv_special_value_min_signed_str)
{
  for (uint32_t i = 1; i < 128; ++i)
  {
    std::stringstream ss;
    ss << '1';
    if (i > 1) ss << std::string(i - 1, '0');
    ASSERT_EQ(bv_special_value_min_signed_str(i), ss.str());
  }
}

TEST(util, bv_special_value_max_signed_str)
{
  for (uint32_t i = 1; i < 128; ++i)
  {
    std::stringstream ss;
    ss << '1';
    if (i > 1) ss << std::string(i - 1, '0');
    ASSERT_EQ(bv_special_value_min_signed_str(i), ss.str());
  }
}

TEST(util, is_bv_special_value_zero_str)
{
  for (uint32_t i = 1; i < 128; ++i)
  {
    std::string s = bv_special_value_zero_str(i);
    for (uint32_t j = 0, n = s.size(); j < n; ++j) ASSERT_EQ(s[j], '0');
  }
}

TEST(util, is_bv_special_value_ones_str)
{
  for (uint32_t i = 1; i < 128; ++i)
  {
    std::string s = bv_special_value_ones_str(i);
    for (uint32_t j = 0, n = s.size(); j < n; ++j) ASSERT_EQ(s[j], '1');
  }
}

TEST(util, is_bv_special_value_one_str)
{
  for (uint32_t i = 1; i < 128; ++i)
  {
    std::string s = bv_special_value_one_str(i);
    uint32_t n    = s.size();
    for (uint32_t j = 0; i > 1 && j < n - 1; ++j) ASSERT_EQ(s[j], '0');
    ASSERT_EQ(s[n - 1], '1');
  }
}

TEST(util, is_bv_special_value_min_signed_str)
{
  for (uint32_t i = 1; i < 128; ++i)
  {
    std::string s = bv_special_value_min_signed_str(i);
    ASSERT_EQ(s[0], '1');
    uint32_t n = s.size();
    for (uint32_t j = 1; i > 0 && j < n; ++j) ASSERT_EQ(s[j], '0');
  }
}

TEST(util, is_bv_special_value_max_signed_str)
{
  for (uint32_t i = 1; i < 128; ++i)
  {
    std::string s = bv_special_value_max_signed_str(i);
    ASSERT_EQ(s[0], '0');
    uint32_t n = s.size();
    for (uint32_t j = 1; i > 0 && j < n; ++j) ASSERT_EQ(s[j], '1');
  }
}
