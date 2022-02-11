/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifdef MURXLA_USE_BOOLECTOR

#include "btor_solver.hpp"

#include <bitset>
#include <cassert>
#include <cstdlib>

#include "action.hpp"
#include "config.hpp"
#include "solver/btor/profile.hpp"
#include "theory.hpp"
#include "util.hpp"

extern "C" {
void boolector_chkclone(Btor*);
}

namespace murxla {
namespace btor {

/* -------------------------------------------------------------------------- */

namespace {

bool
is_power_of_2(uint32_t x)
{
  assert(x > 0);
  return (x & (x - 1)) == 0;
}

}  // namespace

/* -------------------------------------------------------------------------- */
/* BtorSort                                                                   */
/* -------------------------------------------------------------------------- */

BoolectorSort
BtorSort::get_btor_sort(Sort sort)
{
  return checked_cast<BtorSort*>(sort.get())->d_sort;
}

BtorSort::BtorSort(Btor* btor,
                   BoolectorSort sort,
                   const std::vector<BoolectorSort>& domain)
    : d_solver(btor), d_sort(boolector_copy_sort(btor, sort)), d_domain(domain)
{
}

BtorSort::~BtorSort() { boolector_release_sort(d_solver, d_sort); }

size_t
BtorSort::hash() const
{
  return std::hash<BoolectorSort>{}(d_sort);
}

bool
BtorSort::equals(const Sort& other) const
{
  BtorSort* btor_sort = checked_cast<BtorSort*>(other.get());
  if (btor_sort)
  {
    return d_sort == btor_sort->d_sort;
  }
  return false;
}

std::string
BtorSort::bv_sort_to_string(BoolectorSort sort) const
{
  assert(boolector_is_bitvec_sort(d_solver, sort));
  uint32_t bw = boolector_bitvec_sort_get_width(d_solver, sort);
  return "(_ BitVec " + std::to_string(bw) + ")";
}

std::string
BtorSort::to_string() const
{
  if (boolector_is_bitvec_sort(d_solver, d_sort))
  {
    return bv_sort_to_string(d_sort);
  }
  if (boolector_is_array_sort(d_solver, d_sort))
  {
    assert(d_domain.size() == 2);
    return "(Array " + bv_sort_to_string(d_domain[0]) + " "
           + bv_sort_to_string(d_domain[1]) + ")";
  }
  MURXLA_TEST(boolector_is_fun_sort(d_solver, d_sort));
  std::stringstream ss;
  ss << "(-> ";
  for (BoolectorSort s : d_domain) ss << " " << bv_sort_to_string(s);
  ss << ")";
  return ss.str();
}

bool
BtorSort::is_array() const
{
  return boolector_is_array_sort(d_solver, d_sort);
}

bool
BtorSort::is_bool() const
{
  BoolectorSort s = boolector_bool_sort(d_solver);
  bool res        = s == d_sort;
  boolector_release_sort(d_solver, s);
  return res && d_kind == SORT_BOOL;
}

bool
BtorSort::is_bv() const
{
  return boolector_is_bitvec_sort(d_solver, d_sort);
}

bool
BtorSort::is_fun() const
{
  return boolector_is_fun_sort(d_solver, d_sort);
}

uint32_t
BtorSort::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = boolector_bitvec_sort_get_width(d_solver, d_sort);
  MURXLA_TEST(res);
  return res;
}

Sort
BtorSort::get_array_index_sort() const
{
  assert(is_array());
  BoolectorNode* n = boolector_array(d_solver, d_sort, nullptr);
  BoolectorSort btor_res =
      boolector_bitvec_sort(d_solver, boolector_get_index_width(d_solver, n));
  MURXLA_TEST(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, n);
  boolector_release_sort(d_solver, btor_res);
  return res;
}

Sort
BtorSort::get_array_element_sort() const
{
  assert(is_array());
  BoolectorNode* n = boolector_array(d_solver, d_sort, nullptr);
  BoolectorSort btor_res =
      boolector_bitvec_sort(d_solver, boolector_get_width(d_solver, n));
  MURXLA_TEST(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, n);
  boolector_release_sort(d_solver, btor_res);
  return res;
}

uint32_t
BtorSort::get_fun_arity() const
{
  assert(is_fun());
  BoolectorNode* n = boolector_uf(d_solver, d_sort, nullptr);
  uint32_t res     = boolector_get_fun_arity(d_solver, n);
  boolector_release(d_solver, n);
  return res;
}

Sort
BtorSort::get_fun_codomain_sort() const
{
  assert(is_fun());
  BoolectorNode* n       = boolector_uf(d_solver, d_sort, nullptr);
  BoolectorSort btor_res = boolector_fun_get_codomain_sort(d_solver, n);
  MURXLA_TEST(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, n);
  return res;
}

/* -------------------------------------------------------------------------- */
/* BtorTerm                                                                   */
/* -------------------------------------------------------------------------- */

BoolectorNode*
BtorTerm::get_btor_term(Term term)
{
  return checked_cast<BtorTerm*>(term.get())->d_term;
}

BtorTerm::BtorTerm(Btor* btor, BoolectorNode* term)
    : d_solver(btor), d_term(boolector_copy(btor, term))
{
}

BtorTerm::~BtorTerm() { boolector_release(d_solver, d_term); }

/* Boolector_get_node_id does not distinguish between inverted and not inverted
 * nodes, but for hashing we need this distinction. This function returns a
 * negative id if the node is inverted, and else a positive id. */
static int32_t
get_btor_node_id(Btor* btor, BoolectorNode* node)
{
  bool is_inverted = ((uintptr_t) 1 & (uintptr_t) node) != 0;
  int32_t id       = boolector_get_node_id(btor, node);
  if (is_inverted) return -id;
  return id;
}

size_t
BtorTerm::hash() const
{
  return get_btor_node_id(d_solver, d_term);
}

bool
BtorTerm::equals(const Term& other) const
{
  BtorTerm* btor_term = checked_cast<BtorTerm*>(other.get());
  if (btor_term)
  {
    return get_btor_node_id(d_solver, d_term)
           == get_btor_node_id(btor_term->d_solver, btor_term->d_term);
  }
  return false;
}

std::string
BtorTerm::to_string() const
{
  FILE* tmp_file = std::tmpfile();
  boolector_dump_smt2_node(d_solver, tmp_file, d_term);
  std::rewind(tmp_file);
  std::stringstream ss;
  int32_t ch;
  while ((ch = std::fgetc(tmp_file)) != EOF)
  {
    ss << (char) ch;
  }
  MURXLA_EXIT_ERROR(std::ferror(tmp_file))
      << "error while reading from tmp file";
  std::fclose(tmp_file);
  return ss.str();
}

bool
BtorTerm::is_array() const
{
  return boolector_is_array(d_solver, d_term);
}

bool
BtorTerm::is_bool_value() const
{
  return is_bool() && boolector_is_const(d_solver, d_term);
}

bool
BtorTerm::is_bv_value() const
{
  return boolector_is_const(d_solver, d_term);
}

bool
BtorTerm::is_special_value(const SpecialValueKind& kind) const
{
  if (kind == AbsTerm::SPECIAL_VALUE_BV_ZERO)
  {
    return boolector_is_bv_const_zero(d_solver, d_term);
  }
  else if (kind == SPECIAL_VALUE_BV_ONE)
  {
    return boolector_is_bv_const_one(d_solver, d_term);
  }
  else if (kind == SPECIAL_VALUE_BV_ONES)
  {
    return boolector_is_bv_const_ones(d_solver, d_term);
  }
  else if (kind == SPECIAL_VALUE_BV_MIN_SIGNED)
  {
    return boolector_is_bv_const_min_signed(d_solver, d_term);
  }
  else if (kind == SPECIAL_VALUE_BV_MAX_SIGNED)
  {
    return boolector_is_bv_const_max_signed(d_solver, d_term);
  }
  return AbsTerm::is_special_value(kind);
}

bool
BtorTerm::is_const() const
{
  return boolector_is_var(d_solver, d_term)
         || boolector_is_array_var(d_solver, d_term)
         || boolector_is_uf(d_solver, d_term);
}

bool
BtorTerm::is_var() const
{
  return boolector_is_param(d_solver, d_term);
}

uint32_t
BtorTerm::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = boolector_get_width(d_solver, d_term);
  MURXLA_TEST(res);
  return res;
}

Sort
BtorTerm::get_array_index_sort() const
{
  assert(is_array());
  BoolectorSort btor_res = boolector_bitvec_sort(
      d_solver, boolector_get_index_width(d_solver, d_term));
  MURXLA_TEST(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  assert(res);
  boolector_release_sort(d_solver, btor_res);
  return res;
}

Sort
BtorTerm::get_array_element_sort() const
{
  assert(is_array());
  BoolectorSort btor_res =
      boolector_bitvec_sort(d_solver, boolector_get_width(d_solver, d_term));
  MURXLA_TEST(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  assert(res);
  boolector_release_sort(d_solver, btor_res);
  return res;
}

uint32_t
BtorTerm::get_fun_arity() const
{
  assert(is_fun());
  return boolector_get_fun_arity(d_solver, d_term);
}

Sort
BtorTerm::get_fun_codomain_sort() const
{
  assert(is_fun());
  BoolectorSort btor_res = boolector_fun_get_codomain_sort(d_solver, d_term);
  MURXLA_TEST(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  assert(res);
  return res;
}

/* -------------------------------------------------------------------------- */
/* BtorSolver                                                                 */
/* -------------------------------------------------------------------------- */

BtorSolver::~BtorSolver()
{
  if (d_solver)
  {
    boolector_delete(d_solver);
    d_solver = nullptr;
  }
}

void
BtorSolver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = boolector_new();

  /* Initialize Boolector options */
  if (d_option_name_to_enum.empty())
  {
    for (BtorOption opt = boolector_first_opt(d_solver);
         boolector_has_opt(d_solver, opt);
         opt = boolector_next_opt(d_solver, opt))
    {
      std::string name(boolector_get_opt_lng(d_solver, opt));
      d_option_name_to_enum[name] = opt;
    }
  }
}

void
BtorSolver::delete_solver()
{
  assert(d_solver != nullptr);
  MURXLA_TEST(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) == 0);
  boolector_delete(d_solver);
  d_solver = nullptr;
}

Btor*
BtorSolver::get_solver()
{
  return d_solver;
}

bool
BtorSolver::is_initialized() const
{
  return d_solver != nullptr;
}

const std::string
BtorSolver::get_name() const
{
  return "Boolector";
}

const std::string
BtorSolver::get_profile() const
{
  return s_profile;
}

Sort
BtorSolver::mk_sort(SortKind kind)
{
  MURXLA_CHECK_CONFIG(kind == SORT_BOOL)
      << "unsupported sort kind '" << kind
      << "' as argument to BtorSolver::mk_sort, expected '" << SORT_BOOL << "'";
  BoolectorSort btor_res = boolector_bool_sort(d_solver);
  assert(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  boolector_release_sort(d_solver, btor_res);
  assert(res);
  return res;
}

Sort
BtorSolver::mk_sort(SortKind kind, uint32_t size)
{
  MURXLA_CHECK_CONFIG(kind == SORT_BV)
      << "unsupported sort kind '" << kind
      << "' as argument to BtorSolver::mk_sort, expected '" << SORT_BV << "'";
  BoolectorSort btor_res = boolector_bitvec_sort(d_solver, size);
  assert(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  boolector_release_sort(d_solver, btor_res);
  assert(res);
  return res;
}

Sort
BtorSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  BoolectorSort btor_res = 0;
  std::vector<BoolectorSort> domain;

  switch (kind)
  {
    case SORT_ARRAY:
    {
      BoolectorSort isort = BtorSort::get_btor_sort(sorts[0]);
      BoolectorSort esort = BtorSort::get_btor_sort(sorts[1]);
      btor_res            = boolector_array_sort(d_solver, isort, esort);
      domain.push_back(isort);
      domain.push_back(esort);
    }
    break;

    case SORT_FUN:
    {
      BoolectorSort codomain = BtorSort::get_btor_sort(sorts.back());
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        domain.push_back(BtorSort::get_btor_sort(*it));
      }
      btor_res =
          boolector_fun_sort(d_solver, domain.data(), domain.size(), codomain);
      break;
    }

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unsupported sort kind '" << kind
          << "' as argument to BtorSolver::mk_sort, expected '" << SORT_ARRAY
          << "' or '" << SORT_FUN << "'";
  }
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res, domain));
  assert(btor_res);
  boolector_release_sort(d_solver, btor_res);
  assert(res);
  return res;
}

Term
BtorSolver::mk_var(Sort sort, const std::string& name)
{
  BoolectorNode* btor_res;
  std::stringstream ss;
  std::string symbol;
  const char* cname = nullptr;

  /* Make sure that symbol is unique. */
  if (!name.empty())
  {
    ss << "sym" << d_num_symbols << "@" << name;
    ++d_num_symbols;
    symbol = ss.str();
    cname  = symbol.c_str();
  }

  btor_res = boolector_param(d_solver, BtorSort::get_btor_sort(sort), cname);
  assert(btor_res);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_const(Sort sort, const std::string& name)
{
  BoolectorNode* btor_res;
  std::stringstream ss;
  std::string symbol;
  const char* cname = nullptr;

  /* Make sure that symbol is unique. */
  if (!name.empty())
  {
    ss << "sym" << d_num_symbols << "@" << name;
    ++d_num_symbols;
    symbol = ss.str();
    cname  = symbol.c_str();
  }

  if (sort->get_kind() == SORT_ARRAY)
  {
    btor_res = boolector_array(d_solver, BtorSort::get_btor_sort(sort), cname);
    d_have_array = true;
  }
  else if (sort->get_kind() == SORT_FUN)
  {
    btor_res  = boolector_uf(d_solver, BtorSort::get_btor_sort(sort), cname);
    d_have_uf = true;
  }
  else
  {
    btor_res = boolector_var(d_solver, BtorSort::get_btor_sort(sort), cname);
  }
  MURXLA_TEST(btor_res);
  if (d_rng.pick_with_prob(1))
  {
    MURXLA_TEST(boolector_is_equal_sort(d_solver, btor_res, btor_res));
  }
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_fun(const std::string& name,
                   const std::vector<Term>& args,
                   Term body)
{
  std::vector<BoolectorNode*> btor_args = terms_to_btor_terms(args);
  BoolectorNode* btor_body              = BtorTerm::get_btor_term(body);

  BoolectorNode* btor_res =
      boolector_fun(d_solver, btor_args.data(), btor_args.size(), btor_body);
  boolector_set_symbol(d_solver, btor_res, name.c_str());

  MURXLA_TEST(btor_res);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  d_have_fun = true;
  return res;
}

Term
BtorSolver::mk_value(Sort sort, bool value)
{
  MURXLA_CHECK_CONFIG(sort->is_bool())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BtorSolver::mk_value, expected Boolean sort";

  BoolectorNode* btor_res =
      value ? boolector_true(d_solver) : boolector_false(d_solver);
  MURXLA_TEST(btor_res);
  MURXLA_TEST(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
  if (d_rng.pick_with_prob(10))
  {
    const char* bits = boolector_get_bits(d_solver, btor_res);
    MURXLA_TEST(std::string(bits) == (value ? "1" : "0"));
    boolector_free_bits(d_solver, bits);
  }
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

BoolectorNode*
BtorSolver::mk_value_bv_uint32(Sort sort, uint32_t value)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BtorSolver::mk_value, expected bit-vector sort";

  BoolectorNode* btor_res = 0;
  BoolectorSort btor_sort = BtorSort::get_btor_sort(sort);
  uint32_t bw             = sort->get_bv_size();
  assert(bw <= 32);
  bool check_bits = d_rng.pick_with_prob(10);
  std::string str;

  if (d_rng.flip_coin())
  {
    btor_res = boolector_unsigned_int(
        d_solver, static_cast<uint32_t>(value), btor_sort);
    if (check_bits)
    {
      str = std::bitset<MURXLA_BW_MAX>(static_cast<uint32_t>(value))
                .to_string()
                .substr(MURXLA_BW_MAX - bw, bw);
      assert(str.size() == bw);
    }
  }
  else
  {
    btor_res = boolector_int(d_solver, static_cast<int32_t>(value), btor_sort);
    if (check_bits)
    {
      str = std::bitset<MURXLA_BW_MAX>(static_cast<int32_t>(value))
                .to_string()
                .substr(MURXLA_BW_MAX - bw, bw);
      assert(str.size() == bw);
    }
  }
  if (check_bits)
  {
    const char* bits = boolector_get_bits(d_solver, btor_res);
    assert(!str.empty());
    MURXLA_TEST(std::string(bits) == str);
    boolector_free_bits(d_solver, bits);
  }
  MURXLA_TEST(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
  MURXLA_TEST(btor_res);
  return btor_res;
}

Term
BtorSolver::mk_value(Sort sort, const std::string& value, Base base)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BtorSolver::mk_value, expected bit-vector sort";

  BoolectorNode* btor_res;
  BoolectorSort btor_sort = BtorSort::get_btor_sort(sort);
  uint32_t bw             = sort->get_bv_size();

  switch (base)
  {
    case HEX:
      if (bw <= 32 && d_rng.flip_coin())
      {
        btor_res =
            mk_value_bv_uint32(sort, strtoull(value.c_str(), nullptr, 16));
      }
      else
      {
        btor_res = boolector_consth(d_solver, btor_sort, value.c_str());
        if (d_rng.pick_with_prob(10))
        {
          const char* bits = boolector_get_bits(d_solver, btor_res);
          MURXLA_TEST(str_bin_to_hex(bits) == value);
          boolector_free_bits(d_solver, bits);
        }
      }
      break;

    case DEC:
      if (bw <= 32 && d_rng.flip_coin())
      {
        btor_res =
            mk_value_bv_uint32(sort, strtoull(value.c_str(), nullptr, 10));
      }
      else
      {
        btor_res = boolector_constd(d_solver, btor_sort, value.c_str());
        if (d_rng.pick_with_prob(10))
        {
          const char* bits = boolector_get_bits(d_solver, btor_res);
          MURXLA_TEST(str_bin_to_dec(bits, value[0] == '-') == value);
          boolector_free_bits(d_solver, bits);
        }
      }
      break;

    default:
      assert(base == BIN);
      if (bw <= 32 && d_rng.flip_coin())
      {
        btor_res =
            mk_value_bv_uint32(sort, strtoull(value.c_str(), nullptr, 2));
      }
      else
      {
        btor_res = boolector_const(d_solver, value.c_str());
        if (d_rng.pick_with_prob(10))
        {
          const char* bits = boolector_get_bits(d_solver, btor_res);
          MURXLA_TEST(bits == value);
          boolector_free_bits(d_solver, bits);
        }
      }
  }
  MURXLA_TEST(btor_res);
  MURXLA_TEST(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_special_value(Sort sort, const AbsTerm::SpecialValueKind& value)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to BtorSolver::mk_special_value, expected bit-vector "
         "sort";

  BoolectorNode* btor_res = 0;
  BoolectorSort btor_sort = BtorSort::get_btor_sort(sort);
  uint32_t bw             = sort->get_bv_size();
  bool check_bits         = bw <= 64 && d_rng.pick_with_prob(10);
  std::string str;

  if (value == AbsTerm::SPECIAL_VALUE_BV_ZERO)
  {
    btor_res = boolector_zero(d_solver, btor_sort);
    if (check_bits)
    {
      str = std::string(bw, '0');
    }
  }
  else if (value == AbsTerm::SPECIAL_VALUE_BV_ONE)
  {
    btor_res = boolector_one(d_solver, btor_sort);
    if (check_bits)
    {
      std::stringstream ss;
      if (bw > 1)
      {
        ss << std::string(bw - 1, '0');
      }
      ss << "1";
      str = ss.str();
    }
  }
  else if (value == AbsTerm::SPECIAL_VALUE_BV_ONES)
  {
    btor_res = boolector_ones(d_solver, btor_sort);
    if (check_bits) str = std::string(bw, '1');
  }
  else if (value == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED)
  {
    btor_res = boolector_min_signed(d_solver, btor_sort);
    if (check_bits) str = bv_special_value_min_signed_str(bw);
  }
  else
  {
    assert(value == AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED);
    btor_res = boolector_max_signed(d_solver, btor_sort);
    if (check_bits) str = bv_special_value_max_signed_str(bw);
  }
  MURXLA_TEST(btor_res);
  MURXLA_TEST(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
  if (check_bits)
  {
    const char* bits = boolector_get_bits(d_solver, btor_res);
    assert(!str.empty());
    MURXLA_TEST(std::string(bits) == str);
    boolector_free_bits(d_solver, bits);
  }
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_term(const Op::Kind& kind,
                    const std::vector<Term>& args,
                    const std::vector<uint32_t>& indices)
{
  BoolectorNode* btor_res = nullptr;
  size_t n_args           = args.size();
  size_t n_indices        = indices.size();
  std::vector<BoolectorNode*> vars;
  std::vector<BoolectorNode*> btor_args = terms_to_btor_terms(args);

  if (kind == Op::DISTINCT)
  {
    assert(n_args > 1);
    btor_res = mk_term_pairwise(btor_args, boolector_ne);
  }
  else if (kind == Op::EQUAL)
  {
    assert(n_args > 1);
    btor_res = mk_term_chained(btor_args, boolector_eq);
  }
  else if (kind == Op::BV_COMP)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_eq);
  }
  else if (kind == Op::IFF)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_iff);
  }
  else if (kind == Op::ITE)
  {
    assert(n_args == 3);
    btor_res =
        boolector_cond(d_solver, btor_args[0], btor_args[1], btor_args[2]);
  }
  else if (kind == Op::IMPLIES)
  {
    assert(n_args > 1);
    btor_res = mk_term_right_assoc(btor_args, boolector_implies);
  }
  else if (kind == Op::BV_EXTRACT)
  {
    assert(n_args == 1);
    assert(n_indices == 2);
    btor_res = boolector_slice(d_solver, btor_args[0], indices[0], indices[1]);
  }
  else if (kind == Op::BV_REPEAT)
  {
    assert(n_args == 1);
    assert(n_indices == 1);
    btor_res = boolector_repeat(d_solver, btor_args[0], indices[0]);
  }
  else if (kind == Op::BV_ROTATE_LEFT || kind == Op::BV_ROTATE_RIGHT)
  {
    assert(n_args == 1);
    assert(n_indices == 1);
    BoolectorNode* arg = btor_args[0];
    BoolectorSort s    = boolector_get_sort(d_solver, arg);
    uint32_t bw        = boolector_bitvec_sort_get_width(d_solver, s);

    /* use boolector_rori vs boolector_ror with 50% probability */
    if (d_rng.flip_coin())
    {
      btor_res = (kind == Op::BV_ROTATE_LEFT)
                     ? boolector_roli(d_solver, arg, indices[0])
                     : boolector_rori(d_solver, arg, indices[0]);
    }
    else
    {
      BoolectorNode* tmp;
      /* use same bit-width vs log2 bit-width (if possible) with 50% prob
       */
      if (bw > 1 && is_power_of_2(bw) && d_rng.flip_coin())
      {
        /* arg has bw that is power of 2, nbits argument with log2 bw */
        uint32_t bw2     = static_cast<uint32_t>(log2(bw));
        BoolectorSort s2 = boolector_bitvec_sort(d_solver, bw2);
        uint32_t nbits   = indices[0] % bw;
        tmp              = boolector_unsigned_int(d_solver, nbits, s2);
        boolector_release_sort(d_solver, s2);
      }
      else
      {
        /* arg and nbits argument with same bw */
        tmp = boolector_unsigned_int(d_solver, indices[0], s);
      }
      btor_res = (kind == Op::BV_ROTATE_LEFT)
                     ? boolector_rol(d_solver, arg, tmp)
                     : boolector_ror(d_solver, arg, tmp);
      boolector_release(d_solver, tmp);
    }
  }
  else if (kind == Op::BV_SIGN_EXTEND)
  {
    assert(n_args == 1);
    assert(n_indices == 1);
    btor_res = boolector_sext(d_solver, btor_args[0], indices[0]);
  }
  else if (kind == Op::BV_ZERO_EXTEND)
  {
    assert(n_args == 1);
    assert(n_indices == 1);
    btor_res = boolector_uext(d_solver, btor_args[0], indices[0]);
  }
  else if (kind == Op::BV_CONCAT)
  {
    assert(n_args > 1);
    btor_res = mk_term_left_assoc(btor_args, boolector_concat);
  }
  else if (kind == Op::AND || kind == Op::BV_AND)
  {
    assert(n_args > 1);
    btor_res = mk_term_left_assoc(btor_args, boolector_and);
  }
  else if (kind == Op::OR || kind == Op::BV_OR)
  {
    assert(n_args > 1);
    btor_res = mk_term_left_assoc(btor_args, boolector_or);
  }
  else if (kind == Op::XOR || kind == Op::BV_XOR)
  {
    assert(n_args > 1);
    btor_res = mk_term_left_assoc(btor_args, boolector_xor);
  }
  else if (kind == Op::BV_MULT)
  {
    assert(n_args > 1);
    btor_res = mk_term_left_assoc(btor_args, boolector_mul);
  }
  else if (kind == Op::BV_ADD)
  {
    assert(n_args > 1);
    btor_res = mk_term_left_assoc(btor_args, boolector_add);
  }
  else if (kind == Op::NOT || kind == Op::BV_NOT)
  {
    assert(n_args == 1);
    btor_res = boolector_not(d_solver, btor_args[0]);
  }
  else if (kind == Op::BV_NEG)
  {
    assert(n_args == 1);
    btor_res = boolector_neg(d_solver, btor_args[0]);
  }
  else if (kind == Op::BV_NAND)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_nand);
  }
  else if (kind == Op::BV_NOR)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_nor);
  }
  else if (kind == Op::BV_XNOR)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_xnor);
  }
  else if (kind == Op::BV_SUB)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_sub);
  }
  else if (kind == Op::BV_UDIV)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_udiv);
  }
  else if (kind == Op::BV_UREM)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_urem);
  }
  else if (kind == Op::BV_SDIV)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_sdiv);
  }
  else if (kind == Op::BV_SREM)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_srem);
  }
  else if (kind == Op::BV_SMOD)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_smod);
  }
  else if (kind == Op::BV_SHL)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_sll);
  }
  else if (kind == Op::BV_LSHR)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_srl);
  }
  else if (kind == Op::BV_ASHR)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_sra);
  }
  else if (kind == Op::BV_UGT)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_ugt);
  }
  else if (kind == Op::BV_UGE)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_ugte);
  }
  else if (kind == Op::BV_ULT)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_ult);
  }
  else if (kind == Op::BV_ULE)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_ulte);
  }
  else if (kind == Op::BV_SGT)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_sgt);
  }
  else if (kind == Op::BV_SGE)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_sgte);
  }
  else if (kind == Op::BV_SLT)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_slt);
  }
  else if (kind == Op::BV_SLE)
  {
    assert(n_args == 2);
    btor_res = mk_term_left_assoc(btor_args, boolector_slte);
  }
  else if (kind == Op::ARRAY_SELECT)
  {
    assert(n_args == 2);
    btor_res = boolector_read(d_solver, btor_args[0], btor_args[1]);
  }
  else if (kind == Op::ARRAY_STORE)
  {
    assert(n_args == 3);
    btor_res =
        boolector_write(d_solver, btor_args[0], btor_args[1], btor_args[2]);
  }
  else if (kind == Op::EXISTS || kind == Op::FORALL)
  {
    for (size_t i = 0, n = btor_args.size() - 1; i < n; ++i)
    {
      vars.push_back(btor_args[i]);
    }
    if (kind == Op::EXISTS)
    {
      btor_res = boolector_exists(
          d_solver, vars.data(), vars.size(), btor_args.back());
    }
    else
    {
      btor_res = boolector_forall(
          d_solver, vars.data(), vars.size(), btor_args.back());
    }
    d_have_quant = true;
  }
  else if (kind == Op::UF_APPLY)
  {
    btor_res = boolector_apply(
        d_solver, btor_args.data() + 1, n_args - 1, btor_args[0]);
  }
  else
  {
    /* solver-specific operators */
    if (kind == BtorSolver::OP_REDAND)
    {
      assert(n_args == 1);
      btor_res = boolector_redand(d_solver, btor_args[0]);
    }
    else if (kind == BtorSolver::OP_REDOR)
    {
      assert(n_args == 1);
      btor_res = boolector_redor(d_solver, btor_args[0]);
    }
    else if (kind == BtorSolver::OP_REDXOR)
    {
      assert(n_args == 1);
      btor_res = boolector_redxor(d_solver, btor_args[0]);
    }
    else if (kind == BtorSolver::OP_INC)
    {
      assert(n_args == 1);
      btor_res = boolector_inc(d_solver, btor_args[0]);
    }
    else if (kind == BtorSolver::OP_DEC)
    {
      assert(n_args == 1);
      btor_res = boolector_dec(d_solver, btor_args[0]);
    }
    else if (kind == BtorSolver::OP_UADDO)
    {
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(btor_args, boolector_uaddo);
    }
    else if (kind == BtorSolver::OP_UMULO)
    {
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(btor_args, boolector_umulo);
    }
    else if (kind == BtorSolver::OP_USUBO)
    {
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(btor_args, boolector_usubo);
    }
    else if (kind == BtorSolver::OP_SADDO)
    {
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(btor_args, boolector_saddo);
    }
    else if (kind == BtorSolver::OP_SDIVO)
    {
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(btor_args, boolector_sdivo);
    }
    else if (kind == BtorSolver::OP_SMULO)
    {
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(btor_args, boolector_smulo);
    }
    else if (kind == BtorSolver::OP_SSUBO)
    {
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(btor_args, boolector_ssubo);
    }
    else
    {
      MURXLA_CHECK_CONFIG(false)
          << "BtorSolver: operator kind '" << kind << "' not configured";
    }
  }
  MURXLA_TEST(btor_res);
  MURXLA_TEST(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Sort
BtorSolver::get_sort(Term term, SortKind sort_kind) const
{
  (void) sort_kind;
  return std::shared_ptr<BtorSort>(new BtorSort(
      d_solver, boolector_get_sort(d_solver, BtorTerm::get_btor_term(term))));
}

void
BtorSolver::assert_formula(const Term& t)
{
  boolector_assert(d_solver, BtorTerm::get_btor_term(t));
}

Solver::Result
BtorSolver::check_sat()
{
  int32_t res;

  if (d_rng.pick_with_prob(100))
  {
    res = boolector_limited_sat(d_solver,
                                d_rng.pick<int32_t>(-1, 10000),
                                d_rng.pick<int32_t>(-1, 10000));
  }
  else
  {
    res = boolector_sat(d_solver);
  }
  if (res == BOOLECTOR_SAT) return Result::SAT;
  if (res == BOOLECTOR_UNSAT) return Result::UNSAT;
  MURXLA_TEST(res == BOOLECTOR_UNKNOWN);
  return Result::UNKNOWN;
}

Solver::Result
BtorSolver::check_sat_assuming(const std::vector<Term>& assumptions)
{
  int32_t res;
  for (const Term& t : assumptions)
  {
    boolector_assume(d_solver, BtorTerm::get_btor_term(t));
  }
  res = boolector_sat(d_solver);
  if (res == BOOLECTOR_SAT) return Result::SAT;
  if (res == BOOLECTOR_UNSAT) return Result::UNSAT;
  MURXLA_TEST(res == BOOLECTOR_UNKNOWN);
  return Result::UNKNOWN;
}

std::vector<Term>
BtorSolver::get_unsat_assumptions()
{
  std::vector<Term> res;
  BoolectorNode** btor_res = boolector_get_failed_assumptions(d_solver);
  for (uint32_t i = 0; btor_res[i] != nullptr; ++i)
  {
    res.push_back(
        std::shared_ptr<BtorTerm>(new BtorTerm(d_solver, btor_res[i])));
  }
  return res;
}

std::vector<Term>
BtorSolver::get_value(const std::vector<Term>& terms)
{
  std::vector<Term> res;
  std::vector<BoolectorNode*> btor_res;
  std::vector<BoolectorNode*> btor_terms = terms_to_btor_terms(terms);

  for (BoolectorNode* t : btor_terms)
  {
    btor_res.push_back(boolector_get_value(d_solver, t));
  }
  res = btor_terms_to_terms(btor_res);
  for (BoolectorNode* t : btor_res)
  {
    boolector_release(d_solver, t);
  }
  return res;
}

void
BtorSolver::push(uint32_t n_levels)
{
  boolector_push(d_solver, n_levels);
}

void
BtorSolver::pop(uint32_t n_levels)
{
  boolector_pop(d_solver, n_levels);
}

void
BtorSolver::print_model()
{
  const char* fmt = d_rng.flip_coin() ? "btor" : "smt2";
  boolector_print_model(d_solver, (char*) fmt, stdout);
}

void
BtorSolver::reset()
{
  boolector_delete(d_solver);
  d_solver = nullptr;
  new_solver();
}

void
BtorSolver::reset_assertions()
{
  /* boolector does not support this yet */
  assert(false);
}

std::unordered_map<std::string, std::string>
BtorSolver::get_required_options(TheoryId theory) const
{
  std::unordered_map<std::string, std::string> reqopts;
  if (theory == THEORY_QUANT)
  {
    reqopts.emplace("incremental", "false");
    reqopts.emplace("model-gen", "false");
    reqopts.emplace("produce-unsat-cores", "false");
  }
  return reqopts;
}

/* -------------------------------------------------------------------------- */

std::vector<std::string>
BtorSolver::get_supported_sat_solvers()
{
  return {"cadical", "cms", "lingeling", "minisat", "picosat"};
}

bool
BtorSolver::is_unsat_assumption(const Term& t) const
{
  return boolector_failed(d_solver, BtorTerm::get_btor_term(t));
}

/* -------------------------------------------------------------------------- */

BoolectorNode*
BtorSolver::mk_term_left_assoc(std::vector<BoolectorNode*>& args,
                               BoolectorNode* (*fun)(Btor*,
                                                     BoolectorNode*,
                                                     BoolectorNode*) ) const
{
  assert(args.size() >= 2);
  BoolectorNode *res, *tmp;

  res = fun(d_solver, args[0], args[1]);
  for (uint32_t i = 2, n_args = args.size(); i < n_args; ++i)
  {
    tmp = fun(d_solver, res, args[i]);
    boolector_release(d_solver, res);
    res = tmp;
  }
  MURXLA_TEST(res);
  return res;
}

BoolectorNode*
BtorSolver::mk_term_right_assoc(std::vector<BoolectorNode*>& args,
                                BoolectorNode* (*fun)(Btor*,
                                                      BoolectorNode*,
                                                      BoolectorNode*) ) const
{
  uint32_t n_args = args.size();
  assert(n_args >= 2);
  BoolectorNode *res, *tmp;
  res = boolector_copy(d_solver, args[n_args - 1]);
  for (uint32_t i = 1; i < n_args; ++i)
  {
    tmp = fun(d_solver, args[n_args - i - 1], res);
    boolector_release(d_solver, res);
    res = tmp;
  }
  MURXLA_TEST(res);
  return res;
}

BoolectorNode*
BtorSolver::mk_term_pairwise(std::vector<BoolectorNode*>& args,
                             BoolectorNode* (*fun)(Btor*,
                                                   BoolectorNode*,
                                                   BoolectorNode*) ) const
{
  assert(args.size() >= 2);
  BoolectorNode *res, *tmp, *old;

  res = 0;
  for (uint32_t i = 0, n_args = args.size(); i < n_args - 1; ++i)
  {
    for (uint32_t j = i + 1; j < n_args; ++j)
    {
      tmp = fun(d_solver, args[i], args[j]);
      if (res)
      {
        old = res;
        res = boolector_and(d_solver, old, tmp);
        boolector_release(d_solver, old);
        boolector_release(d_solver, tmp);
      }
      else
      {
        res = tmp;
      }
    }
  }
  MURXLA_TEST(res);
  return res;
}

BoolectorNode*
BtorSolver::mk_term_chained(std::vector<BoolectorNode*>& args,
                            BoolectorNode* (*fun)(Btor*,
                                                  BoolectorNode*,
                                                  BoolectorNode*) ) const
{
  assert(args.size() >= 2);
  BoolectorNode *res, *tmp, *old;

  res = 0;
  for (uint32_t i = 0, j = 1, n_args = args.size(); j < n_args; ++i, ++j)
  {
    tmp = fun(d_solver, args[i], args[j]);
    if (res)
    {
      old = res;
      res = boolector_and(d_solver, old, tmp);
      boolector_release(d_solver, old);
      boolector_release(d_solver, tmp);
    }
    else
    {
      res = tmp;
    }
  }
  MURXLA_TEST(res);
  return res;
}

namespace {
void
btor_throw(const char* msg)
{
  throw MurxlaSolverOptionException(msg);
}
}  // namespace

void
BtorSolver::set_opt(const std::string& opt, const std::string& value)
{
  if (opt == "produce-unsat-assumptions")
  {
    /* always enabled in Boolector, can not be configured via set_opt */
    return;
  }

  if (opt == "produce-unsat-cores")
  {
    /* not supported */
    return;
  }

  /* Boolector options are all integer values */
  uint32_t val = 0;

  if (value == "true")
  {
    val = 1;
  }
  else if (value != "false")
  {
    val = std::stoul(value);
  }
  BtorOption btor_opt = d_option_name_to_enum.at(opt);
  MURXLA_TEST(val >= boolector_get_opt_min(d_solver, btor_opt));
  MURXLA_TEST(val <= boolector_get_opt_max(d_solver, btor_opt));
  boolector_set_abort(btor_throw);
  boolector_set_opt(d_solver, btor_opt, val);
  boolector_set_abort(nullptr);
  MURXLA_TEST(val == boolector_get_opt(d_solver, btor_opt));
  MURXLA_TEST(val != boolector_get_opt_dflt(d_solver, btor_opt)
              || boolector_get_opt(d_solver, btor_opt)
                     == boolector_get_opt_dflt(d_solver, btor_opt));
}

std::string
BtorSolver::get_option_name_incremental() const
{
  return boolector_get_opt_lng(d_solver, BTOR_OPT_INCREMENTAL);
}

std::string
BtorSolver::get_option_name_model_gen() const
{
  return boolector_get_opt_lng(d_solver, BTOR_OPT_MODEL_GEN);
}

std::string
BtorSolver::get_option_name_unsat_assumptions() const
{
  /* always enabled in Boolector, can not be configured via set_opt */
  return "produce-unsat-assumptions";
}

std::string
BtorSolver::get_option_name_unsat_cores() const
{
  /* always enabled in Boolector, can not be configured via set_opt */
  return "produce-unsat-cores";
}

bool
BtorSolver::option_incremental_enabled() const
{
  return boolector_get_opt(d_solver, BTOR_OPT_INCREMENTAL) > 0;
}

bool
BtorSolver::option_model_gen_enabled() const
{
  return boolector_get_opt(d_solver, BTOR_OPT_MODEL_GEN) > 0;
}

bool
BtorSolver::option_unsat_assumptions_enabled() const
{
  /* always enabled in Boolector, can not be configured via set_opt */
  return true;
}

bool
BtorSolver::option_unsat_cores_enabled() const
{
  /* not supported */
  return false;
}

/* -------------------------------------------------------------------------- */

std::vector<Term>
BtorSolver::btor_terms_to_terms(const std::vector<BoolectorNode*>& terms) const
{
  std::vector<Term> res;
  for (BoolectorNode* t : terms)
  {
    res.push_back(std::shared_ptr<BtorTerm>(new BtorTerm(d_solver, t)));
  }
  return res;
}

std::vector<BoolectorNode*>
BtorSolver::terms_to_btor_terms(const std::vector<Term>& terms) const
{
  std::vector<BoolectorNode*> res;
  for (auto& t : terms)
  {
    res.push_back(BtorTerm::get_btor_term(t));
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* OpKindManager configuration.                                               */
/* -------------------------------------------------------------------------- */

void
BtorSolver::configure_opmgr(OpKindManager* opmgr) const
{
  opmgr->add_op_kind(OP_DEC, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(OP_INC, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(OP_REDAND, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(OP_REDOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(OP_REDXOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(OP_UADDO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(OP_UMULO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(OP_USUBO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(OP_SADDO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(OP_SDIVO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(OP_SMULO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(OP_SSUBO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
}

/* -------------------------------------------------------------------------- */
/* FSM configuration.                                                         */
/* -------------------------------------------------------------------------- */

class BtorActionArrayAssignment : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-array-assignment";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionArrayAssignment(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    if (!d_smgr.has_term(SORT_ARRAY, 0)) return false;
    Term term = d_smgr.pick_term(SORT_ARRAY, 0);
    run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    run(term);
    return {};
  }

 private:
  void run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    BoolectorNode* btor_term = BtorTerm::get_btor_term(term);
    BtorSolver& btor_solver  = static_cast<BtorSolver&>(d_smgr.get_solver());
    Btor* btor               = btor_solver.get_solver();
    char **indices = nullptr, **values = nullptr;
    uint32_t size = 0;
    boolector_array_assignment(btor, btor_term, &indices, &values, &size);
    if (d_smgr.d_incremental)
    {
      /* assume assignment and check if result is still SAT */
      std::vector<Term> assumptions;
      for (size_t i = 0; i < size; ++i)
      {
        Term idx = d_solver.mk_value(term->get_sort()->get_array_index_sort(),
                                     indices[i],
                                     Solver::Base::BIN);
        Term val = d_solver.mk_value(term->get_sort()->get_array_element_sort(),
                                     values[i],
                                     Solver::Base::BIN);
        BoolectorNode* btor_idx    = BtorTerm::get_btor_term(idx);
        BoolectorNode* btor_val    = BtorTerm::get_btor_term(val);
        BoolectorNode* btor_select = boolector_read(btor, btor_term, btor_idx);
        BoolectorNode* btor_eq     = boolector_eq(btor, btor_select, btor_val);
        assumptions.push_back(
            std::shared_ptr<BtorTerm>(new BtorTerm(btor, btor_eq)));
        boolector_release(btor, btor_eq);
        boolector_release(btor, btor_select);
      }
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
    if (size)
    {
      boolector_free_array_assignment(btor, indices, values, size);
    }
  }
};

class BtorActionBvAssignment : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-bv-assignment";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionBvAssignment(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    if (!d_smgr.has_term(SORT_BV, 0)) return false;
    Term term = d_smgr.pick_term(SORT_BV, 0);
    run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    run(term);
    return {};
  }

 private:
  void run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    BtorSolver& btor_solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    const char* assignment  = boolector_bv_assignment(
        btor_solver.get_solver(), BtorTerm::get_btor_term(term));
    if (d_smgr.d_incremental)
    {
      /* assume assignment and check if result is still SAT */
      Term term_bv_val =
          d_solver.mk_value(term->get_sort(), assignment, Solver::Base::BIN);
      std::vector<Term> assumptions{
          d_solver.mk_term(Op::EQUAL, {term, term_bv_val}, {})};
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
    boolector_free_bv_assignment(btor_solver.get_solver(), assignment);
  }
};

class BtorActionUFAssignment : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-uf-assignment";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionUFAssignment(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    if (!d_smgr.has_term(SORT_FUN, 0)) return false;
    Term term = d_smgr.pick_term(SORT_FUN, 0);
    run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    run(term);
    return {};
  }

 private:
  void run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    BoolectorNode* btor_term = BtorTerm::get_btor_term(term);
    BtorSolver& btor_solver  = static_cast<BtorSolver&>(d_smgr.get_solver());
    Btor* btor               = btor_solver.get_solver();
    char **args = nullptr, **values = nullptr;
    uint32_t size = 0;
    boolector_uf_assignment(btor, btor_term, &args, &values, &size);
    if (d_smgr.d_incremental)
    {
      /* assume assignment and check if result is still SAT */
      const auto& sorts = term->get_sort()->get_sorts();
      std::vector<Sort> domain{sorts.begin(), sorts.end() - 1};
      Sort codomain = sorts.back();
      std::vector<Term> assumptions;
      for (size_t i = 0; i < size; ++i)
      {
        std::vector<std::string> _args = split(args[i], ' ');
        uint32_t arity                 = _args.size();
        std::vector<Term> apply_args{term};
        MURXLA_TEST(arity == domain.size());
        for (uint32_t j = 0; j < arity; ++j)
        {
          apply_args.push_back(
              d_solver.mk_value(domain[j], _args[j], Solver::Base::BIN));
        }
        Term apply = d_solver.mk_term(Op::UF_APPLY, apply_args, {});
        Term val   = d_solver.mk_value(codomain, values[i], Solver::Base::BIN);
        BoolectorNode* btor_apply = BtorTerm::get_btor_term(apply);
        BoolectorNode* btor_val   = BtorTerm::get_btor_term(val);
        BoolectorNode* btor_eq    = boolector_eq(btor, btor_apply, btor_val);
        assumptions.push_back(
            std::shared_ptr<BtorTerm>(new BtorTerm(btor, btor_eq)));
        boolector_release(btor, btor_eq);
      }
      MURXLA_TEST(d_solver.check_sat_assuming(assumptions)
                  == Solver::Result::SAT);
    }
    if (size)
    {
      boolector_free_uf_assignment(btor, args, values, size);
    }
  }
};

class BtorActionClone : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-clone";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionClone(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    run();
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    run();
    return {};
  }

 private:
  void run()
  {
    MURXLA_TRACE << get_kind();
    BtorSolver& solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    Btor* btor         = solver.get_solver();
    Btor* clone        = boolector_clone(btor);

    if (d_rng.flip_coin())
    {
      boolector_reset_stats(clone);
    }
    if (d_rng.flip_coin())
    {
      boolector_reset_time(clone);
    }
    if (d_rng.flip_coin())
    {
      boolector_print_stats(clone);
    }
    if (d_smgr.has_term() && d_rng.flip_coin())
    {
      for (uint64_t i = 0, n = d_smgr.get_num_terms_max_level(); i < n; ++i)
      {
        Term t = d_smgr.pick_term();
        BoolectorNode *t_btor, *t_clone;
        BoolectorSort sort;
        int32_t id;
        const char* s;
        std::string symbol;

        t_btor = BtorTerm::get_btor_term(t);
        MURXLA_TEST(boolector_get_btor(t_btor) == btor);
        id     = boolector_get_node_id(btor, t_btor);
        sort   = boolector_get_sort(btor, t_btor);
        s      = boolector_get_symbol(btor, t_btor);
        symbol = s ? s : "";

        /* first, test boolector_match_node */
        t_clone = boolector_match_node(clone, t_btor);
        MURXLA_TEST(boolector_get_btor(t_clone) == clone);
        MURXLA_TEST(id == boolector_get_node_id(clone, t_clone));
        MURXLA_TEST(sort == boolector_get_sort(clone, t_clone));
        s = boolector_get_symbol(clone, t_clone);
        MURXLA_TEST(symbol.empty() || s);
        MURXLA_TEST(!s || symbol == s);
        if (boolector_is_fun(btor, t_btor))
        {
          MURXLA_TEST(boolector_is_fun(clone, t_clone));
          MURXLA_TEST(boolector_fun_get_domain_sort(btor, t_btor)
                      == boolector_fun_get_domain_sort(clone, t_clone));
          MURXLA_TEST(boolector_fun_get_codomain_sort(btor, t_btor)
                      == boolector_fun_get_codomain_sort(clone, t_clone));
        }
        boolector_release(clone, t_clone);

        /* second, test boolector_match_node_by_id */
        t_clone = boolector_match_node_by_id(clone, id < 0 ? -id : id);
        MURXLA_TEST(boolector_get_btor(t_clone) == clone);
        MURXLA_TEST(sort == boolector_get_sort(clone, t_clone));
        s = boolector_get_symbol(clone, t_clone);
        MURXLA_TEST(symbol.empty() || s);
        MURXLA_TEST(!s || symbol == s);
        if (boolector_is_fun(btor, t_btor))
        {
          MURXLA_TEST(boolector_is_fun(clone, t_clone));
          MURXLA_TEST(boolector_fun_get_domain_sort(btor, t_btor)
                      == boolector_fun_get_domain_sort(clone, t_clone));
          MURXLA_TEST(boolector_fun_get_codomain_sort(btor, t_btor)
                      == boolector_fun_get_codomain_sort(clone, t_clone));
        }
        boolector_release(clone, t_clone);

        /* finally, test boolector_match_node_by_symbol */
        if (!symbol.empty())
        {
          t_clone = boolector_match_node_by_symbol(clone, symbol.c_str());
          MURXLA_TEST(boolector_get_btor(t_clone) == clone);
          MURXLA_TEST(id == boolector_get_node_id(clone, t_clone));
          MURXLA_TEST(sort == boolector_get_sort(clone, t_clone));
          if (boolector_is_fun(btor, t_btor))
          {
            MURXLA_TEST(boolector_is_fun(clone, t_clone));
            MURXLA_TEST(boolector_fun_get_domain_sort(btor, t_btor)
                        == boolector_fun_get_domain_sort(clone, t_clone));
            MURXLA_TEST(boolector_fun_get_codomain_sort(btor, t_btor)
                        == boolector_fun_get_codomain_sort(clone, t_clone));
          }
          boolector_release(clone, t_clone);
        }
      }
    }
    boolector_delete(clone);

    if (d_rng.pick_with_prob(100))
    {
      boolector_chkclone(btor);
    }
  }
};

class BtorActionFailed : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-failed";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionFailed(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::UNSAT) return false;
    if (!d_smgr.d_incremental) return false;
    if (!d_smgr.has_assumed()) return false;
    Term term = d_smgr.pick_assumed_assumption();
    run(term);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    run(term);
    return {};
  }

 private:
  void run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    BtorSolver& btor_solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    (void) boolector_failed(btor_solver.get_solver(),
                            BtorTerm::get_btor_term(term));
  }
};

class BtorActionFixateAssumptions : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-fixate-assumptions";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionFixateAssumptions(SolverManager& smgr) : Action(smgr, s_name, NONE)
  {
  }

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_incremental) return false;
    run();
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    run();
    return {};
  }

 private:
  void run()
  {
    MURXLA_TRACE << get_kind();
    reset_sat();
    boolector_fixate_assumptions(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionOptIterator : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-opt-iterator";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionOptIterator(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    run();
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    run();
    return {};
  }

 private:
  void run()
  {
    MURXLA_TRACE << get_kind();
    Btor* btor = static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver();
    for (BtorOption opt = boolector_first_opt(btor); opt < BTOR_OPT_NUM_OPTS;
         opt            = boolector_next_opt(btor, opt))
    {
      MURXLA_TEST(boolector_has_opt(btor, opt));
      MURXLA_TEST(boolector_get_opt(btor, opt)
                  >= boolector_get_opt_min(btor, opt));
      MURXLA_TEST(boolector_get_opt(btor, opt)
                  <= boolector_get_opt_max(btor, opt));
      MURXLA_TEST(boolector_get_opt_min(btor, opt)
                  <= boolector_get_opt_max(btor, opt));
      MURXLA_TEST(boolector_get_opt_dflt(btor, opt)
                  >= boolector_get_opt_min(btor, opt));
      MURXLA_TEST(boolector_get_opt_dflt(btor, opt)
                  <= boolector_get_opt_max(btor, opt));
      std::string lng = boolector_get_opt_lng(btor, opt);
      const char* s   = boolector_get_opt_shrt(btor, opt);
      if (s != nullptr)
      {
        std::string shrt(s);
        MURXLA_TEST(shrt.size() <= lng.size());
      }
      (void) boolector_get_opt_desc(btor, opt);
    }
    MURXLA_TEST(!boolector_has_opt(
        btor,
        (BtorOption) d_rng.pick<uint32_t>(BTOR_OPT_NUM_OPTS, UINT32_MAX)));
  }
};

class BtorActionReleaseAll : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-release-all";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionReleaseAll(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    run();
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    run();
    return {};
  }

 private:
  void run()
  {
    MURXLA_TRACE << get_kind();
    d_smgr.clear();
    boolector_release_all(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionResetAssumptions : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-reset-assumptions";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionResetAssumptions(SolverManager& smgr) : Action(smgr, s_name, NONE)
  {
  }

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_incremental) return false;
    run();
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    run();
    return {};
  }

 private:
  void run()
  {
    MURXLA_TRACE << get_kind();
    d_smgr.clear_assumptions();
    boolector_reset_assumptions(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionSetSatSolver : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-set-sat-solver";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionSetSatSolver(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    BtorSolver& solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    std::string sat_solver =
        d_rng.pick_from_set<std::vector<std::string>, std::string>(
            solver.get_supported_sat_solvers());
    run(sat_solver);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    assert(tokens.size() == 1);
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    run(tokens[0]);
    return {};
  }

 private:
  void run(std::string sat_solver)
  {
    MURXLA_TRACE << get_kind() << " " << sat_solver;
    BtorSolver& solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    boolector_set_sat_solver(solver.get_solver(), sat_solver.c_str());
  }
};

class BtorActionSimplify : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-simplify";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionSimplify(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    BtorSolver& solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    if (solver.get_solver() == nullptr) return false;
    run();
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_EMPTY(tokens);
    run();
    return {};
  }

 private:
  void run()
  {
    MURXLA_TRACE << get_kind();
    reset_sat();
    boolector_simplify(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionSetSymbol : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-set-symbol";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionSetSymbol(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    Term term          = d_smgr.pick_term();
    std::string symbol = d_smgr.pick_symbol();
    run(term, symbol);
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(2, tokens.size());
    Term term = get_untraced_term(untrace_str_to_id(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    std::string symbol = str_to_str(tokens[1]);
    run(term, symbol);
    return {};
  }

 private:
  void run(Term term, std::string symbol)
  {
    MURXLA_TRACE << get_kind() << " " << term << " \"" << symbol << "\"";
    BtorSolver& btor_solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    (void) boolector_set_symbol(btor_solver.get_solver(),
                                BtorTerm::get_btor_term(term),
                                symbol.c_str());
  }
};

class BtorActionMisc : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-misc";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionMisc(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    run();
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(0, tokens.size());
    run();
    return {};
  }

 private:
  void run()
  {
    MURXLA_TRACE << get_kind();
    BtorSolver& btor_solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    Btor* btor              = btor_solver.get_solver();

    const char* version = boolector_version(btor);
    MURXLA_TEST(version && std::string(version) != "");
    const char* copyright = boolector_copyright(btor);
    MURXLA_TEST(copyright && std::string(copyright) != "");
    const char* git_id = boolector_git_id(btor);
    MURXLA_TEST(git_id && std::string(git_id) != "");
    std::string msg_prefix = d_rng.pick_string(10);
    boolector_set_msg_prefix(btor, msg_prefix.c_str());
  }
};

class BtorActionPrintParse : public Action
{
 public:
  /** The name of this action. */
  inline static const Kind s_name = "btor-print-parse";

  /**
   * Constructor.
   * @param smgr  The associated solver manager.
   */
  BtorActionPrintParse(SolverManager& smgr) : Action(smgr, s_name, NONE) {}

  bool generate() override
  {
    assert(d_solver.is_initialized());
    if (d_solver.option_incremental_enabled()) return false;
    run();
    return true;
  }

  std::vector<uint64_t> untrace(const std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(0, tokens.size());
    run();
    return {};
  }

 private:
  void run()
  {
    MURXLA_TRACE << get_kind();
    BtorSolver& btor_solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    Btor* btor              = btor_solver.get_solver();
    auto& rng               = btor_solver.get_rng();

    bool parse_smt2 = false, parse_btor = false;
    FILE* tmp_file = nullptr;

    if (!btor_solver.d_have_uf && !btor_solver.d_have_fun
        && !btor_solver.d_have_array && !btor_solver.d_have_quant
        && rng.flip_coin())
    {
      if (rng.flip_coin())
      {
        boolector_dump_aiger_ascii(btor, stdout, rng.flip_coin());
      }
      else
      {
        boolector_dump_aiger_binary(btor, stdout, rng.flip_coin());
      }
    }
    else
    {
      tmp_file = std::tmpfile();
      if (rng.flip_coin() && !btor_solver.d_have_uf)
      {
        boolector_dump_btor(btor, tmp_file);
        parse_btor = true;
      }
      else
      {
        boolector_dump_smt2(btor, tmp_file);
        parse_smt2 = true;
      }
    }

    if (tmp_file)
    {
      std::rewind(tmp_file);
      Btor* btor_parse = boolector_new();
      char* error_msg  = nullptr;
      int32_t status   = 0;
      if (rng.flip_coin())
      {
        bool parsed_smt2 = false;
        boolector_parse(btor_parse,
                        tmp_file,
                        "tmpfile",
                        stdout,
                        &error_msg,
                        &status,
                        &parsed_smt2);
        MURXLA_TEST(parse_smt2 == parsed_smt2);
      }
      else if (parse_smt2)
      {
        boolector_parse_smt2(
            btor_parse, tmp_file, "tmpfile", stdout, &error_msg, &status);
      }
      else if (parse_btor)
      {
        if (!btor_solver.d_have_quant)
        {
          boolector_parse_btor(
              btor_parse, tmp_file, "tmpfile", stdout, &error_msg, &status);
        }
      }
      MURXLA_TEST(error_msg == nullptr) << error_msg;
      boolector_delete(btor_parse);
      std::fclose(tmp_file);
    }
  }
};

/* -------------------------------------------------------------------------- */

void
BtorSolver::configure_fsm(FSM* fsm) const
{
  SolverManager& smgr = fsm->get_smgr();

  State* s_assert           = fsm->get_state(State::ASSERT);
  State* s_check_sat        = fsm->get_state(State::CHECK_SAT);
  State* s_create_sorts     = fsm->get_state(State::CREATE_SORTS);
  State* s_create_inputs    = fsm->get_state(State::CREATE_INPUTS);
  State* s_create_terms     = fsm->get_state(State::CREATE_TERMS);
  State* s_delete           = fsm->get_state(State::DELETE);
  State* s_opt              = fsm->get_state(State::OPT);
  State* s_push_pop         = fsm->get_state(State::PUSH_POP);
  State* s_sat              = fsm->get_state(State::SAT);
  State* s_decide_sat_unsat = fsm->get_state(State::DECIDE_SAT_UNSAT);

  /* Solver-specific states. */
  State* s_fix_reset_assumptions = fsm->new_state(STATE_FIX_RESET_ASSUMPTIONS);
  State* s_unknown = fsm->new_choice_state(STATE_UNKNOWN, [&smgr]() {
    return smgr.d_sat_called && smgr.d_sat_result == Solver::Result::UNKNOWN;
  });

  /* Modify precondition of existing states. */
  s_sat->update_precondition([&smgr]() {
    return smgr.d_sat_called && smgr.d_sat_result == Solver::Result::SAT;
  });

  auto t_default = fsm->new_action<TransitionDefault>();

  /* Add solver-specific actions and reconfigure existing states. */
  s_decide_sat_unsat->add_action(t_default, 1, s_unknown);

  // options
  auto a_opt_it = fsm->new_action<BtorActionOptIterator>();
  fsm->add_action_to_all_states(a_opt_it, 100);

  // boolector_array_assignment
  auto a_arr_ass = fsm->new_action<BtorActionArrayAssignment>();
  s_sat->add_action(a_arr_ass, 2);
  // boolector_bv_assignment
  auto a_bv_ass = fsm->new_action<BtorActionBvAssignment>();
  s_sat->add_action(a_bv_ass, 2);
  // boolector_uf_assignment
  auto a_uf_ass = fsm->new_action<BtorActionUFAssignment>();
  s_sat->add_action(a_uf_ass, 2);

  // boolector_clone
  auto a_clone = fsm->new_action<BtorActionClone>();
  fsm->add_action_to_all_states(a_clone, 1000);

  // boolector_failed
  auto a_failed = fsm->new_action<BtorActionFailed>();
  fsm->add_action_to_all_states(a_failed, 100);

  // boolector_fixate_assumptions
  // boolector_reset_assumptions
  auto a_fix_assumptions   = fsm->new_action<BtorActionFixateAssumptions>();
  auto a_reset_assumptions = fsm->new_action<BtorActionResetAssumptions>();
  s_fix_reset_assumptions->add_action(a_fix_assumptions, 5);
  s_fix_reset_assumptions->add_action(a_reset_assumptions, 5);
  s_fix_reset_assumptions->add_action(t_default, 1, s_assert);
  fsm->add_action_to_all_states_next(t_default, 2, s_fix_reset_assumptions);

  // boolector_release_all
  auto a_release_all = fsm->new_action<BtorActionReleaseAll>();
  s_delete->add_action(a_release_all, 100);

  // boolector_simplify
  auto a_simplify = fsm->new_action<BtorActionSimplify>();
  s_assert->add_action(a_simplify, 1000);
  s_create_sorts->add_action(a_simplify, 1000);
  s_create_inputs->add_action(a_simplify, 1000);
  s_create_terms->add_action(a_simplify, 1000);
  s_opt->add_action(a_simplify, 1000);
  s_push_pop->add_action(a_simplify, 1000);
  s_check_sat->add_action(a_simplify, 1000, s_assert);

  // boolector_set_sat_solver
  auto a_set_sat_solver = fsm->new_action<BtorActionSetSatSolver>();
  s_opt->add_action(a_set_sat_solver, 100);

  // boolector_set_symbol
  auto a_set_symbol = fsm->new_action<BtorActionSetSymbol>();
  fsm->add_action_to_all_states(a_set_symbol, 100);

  auto a_misc = fsm->new_action<BtorActionMisc>();
  fsm->add_action_to_all_states(a_misc, 100000);
  auto a_print_parse = fsm->new_action<BtorActionPrintParse>();
  s_assert->add_action(a_print_parse, 100);

  /* Configure solver-specific states. */
  s_unknown->add_action(t_default, 1, s_check_sat);
}

void
BtorSolver::configure_options(SolverManager* smgr) const
{
  Btor* slv = boolector_new();
  for (auto o = boolector_first_opt(slv); boolector_has_opt(slv, o);
       o      = boolector_next_opt(slv, o))
  {
    smgr->add_option(
        new SolverOptionNum<uint32_t>(boolector_get_opt_lng(slv, o),
                                      boolector_get_opt_min(slv, o),
                                      boolector_get_opt_max(slv, o),
                                      boolector_get_opt_dflt(slv, o)));
  }
  boolector_delete(slv);
}

void
BtorSolver::disable_unsupported_actions(FSM* fsm) const
{
  fsm->disable_action(ActionResetAssertions::s_name);
  fsm->disable_action(ActionInstantiateSort::s_name);
}

}  // namespace btor
}  // namespace murxla

#endif
