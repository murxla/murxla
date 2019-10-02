#include "gtest/gtest.h"
#include "util.hpp"

TEST(util, str_bin_to_hex)
{
  ASSERT_EQ(smtmbt::str_bin_to_hex("0"), "0");
  ASSERT_EQ(smtmbt::str_bin_to_hex("0000"), "0");
  ASSERT_EQ(smtmbt::str_bin_to_hex("000000"), "00");
  ASSERT_EQ(smtmbt::str_bin_to_hex("00000000"), "00");

  ASSERT_EQ(smtmbt::str_bin_to_hex("1"), "1");
  ASSERT_EQ(smtmbt::str_bin_to_hex("0001"), "1");
  ASSERT_EQ(smtmbt::str_bin_to_hex("000001"), "01");
  ASSERT_EQ(smtmbt::str_bin_to_hex("00000001"), "01");

  ASSERT_EQ(smtmbt::str_bin_to_hex("1"), "1");
  ASSERT_EQ(smtmbt::str_bin_to_hex("1111"), "f");
  ASSERT_EQ(smtmbt::str_bin_to_hex("001111"), "0f");
  ASSERT_EQ(smtmbt::str_bin_to_hex("111111"), "3f");
  ASSERT_EQ(smtmbt::str_bin_to_hex("11111111"), "ff");
  ASSERT_EQ(smtmbt::str_bin_to_hex("111111111111"), "fff");
  ASSERT_EQ(smtmbt::str_bin_to_hex("1111111111111111"), "ffff");
  ASSERT_EQ(smtmbt::str_bin_to_hex("11111111111111111"), "1ffff");

  ASSERT_EQ(
      smtmbt::str_bin_to_hex(
          "01010101010101010101010101010101010101010101010101010101010101010"),
      "0aaaaaaaaaaaaaaaa");
  ASSERT_EQ(
      smtmbt::str_bin_to_hex(
          "10101010101010101010101010101010101010101010101010101010101010101"),
      "15555555555555555");
  ASSERT_EQ(
      smtmbt::str_bin_to_hex(
          "1111111011011100101110101001100001110110010101000011001000010000"),
      "fedcba9876543210");
}

TEST(util, str_bin_to_dec)
{
  ASSERT_EQ(smtmbt::str_bin_to_dec("0"), "0");
  ASSERT_EQ(smtmbt::str_bin_to_dec("0000"), "0");
  ASSERT_EQ(smtmbt::str_bin_to_dec("000000"), "0");
  ASSERT_EQ(smtmbt::str_bin_to_dec("00000000"), "0");

  ASSERT_EQ(smtmbt::str_bin_to_dec("1"), "1");
  ASSERT_EQ(smtmbt::str_bin_to_dec("0001"), "1");
  ASSERT_EQ(smtmbt::str_bin_to_dec("000001"), "1");
  ASSERT_EQ(smtmbt::str_bin_to_dec("00000001"), "1");

  ASSERT_EQ(smtmbt::str_bin_to_dec("1"), "1");
  ASSERT_EQ(smtmbt::str_bin_to_dec("1111"), "15");
  ASSERT_EQ(smtmbt::str_bin_to_dec("001111"), "15");
  ASSERT_EQ(smtmbt::str_bin_to_dec("111111"), "63");
  ASSERT_EQ(smtmbt::str_bin_to_dec("11111111"), "255");
  ASSERT_EQ(smtmbt::str_bin_to_dec("111111111111"), "4095");
  ASSERT_EQ(smtmbt::str_bin_to_dec("1111111111111111"), "65535");
  ASSERT_EQ(smtmbt::str_bin_to_dec("11111111111111111"), "131071");

  ASSERT_EQ(
      smtmbt::str_bin_to_dec(
          "01010101010101010101010101010101010101010101010101010101010101010"),
      "12297829382473034410");
  ASSERT_EQ(
      smtmbt::str_bin_to_dec(
          "10101010101010101010101010101010101010101010101010101010101010101"),
      "24595658764946068821");
  ASSERT_EQ(
      smtmbt::str_bin_to_dec(
          "1111111011011100101110101001100001110110010101000011001000010000"),
      "18364758544493064720");
}

TEST(util, bv_special_value_ones_uint64)
{
  for (uint32_t i = 1; i <= 64; ++i)
  {
    uint64_t res = smtmbt::bv_special_value_ones_uint64(i);
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
    uint64_t res      = smtmbt::bv_special_value_min_signed_uint64(i);
    uint64_t expected = 1;
    for (uint32_t j = 1; j < i; ++j) expected *= 2;
    ASSERT_EQ(expected, res);
  }
}

TEST(util, bv_special_value_max_signed_uint64)
{
  for (uint32_t i = 1; i <= 64; ++i)
  {
    uint64_t res = smtmbt::bv_special_value_max_signed_uint64(i);
    uint64_t mask;
    for (uint32_t j = 0; j < i - 1; ++j)
    {
      mask = ((uint64_t) 1u) << j;
      ASSERT_EQ(res & mask, mask);
    }
    if (i == 1)
    {
      ASSERT_EQ(res, ((uint64_t) 1u));
    }
    else
    {
      for (uint32_t j = i - 1; j <= 64; ++j)
      {
        mask = j == 64 ? 0u : ((uint64_t) 1u) << j;
        mask = ~mask;
        ASSERT_EQ(res | mask, mask);
      }
    }
  }
}

TEST(util, bv_special_value_ones_str)
{
  for (uint32_t i = 1; i < 128; ++i)
    ASSERT_EQ(smtmbt::bv_special_value_ones_str(i), std::string(i, '1'));
}

// TODO
// bool is_bv_special_value_ones_uint64(uint32_t bw, uint64_t value);
// bool is_bv_special_value_min_signed_uint64(uint32_t bw, uint64_t value);
// bool is_bv_special_value_max_signed_uint64(uint32_t bw, uint64_t value);
//
// std::string bv_special_value_zero_str(uint32_t bw);
// std::string bv_special_value_one_str(uint32_t bw);
// std::string bv_special_value_ones_str(uint32_t bw);
// std::string bv_special_value_min_signed_str(uint32_t bw);
// std::string bv_special_value_max_signed_str(uint32_t bw);
//
// bool is_bv_special_value_zero_str(std::string& value);
// bool is_bv_special_value_one_str(std::string& value);
// bool is_bv_special_value_ones_str(std::string& value);
// bool is_bv_special_value_min_signed_str(std::string& value);
// bool is_bv_special_value_max_signed_str(std::string& value);
