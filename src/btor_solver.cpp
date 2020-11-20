#ifdef SMTMBT_USE_BOOLECTOR

#include "btor_solver.hpp"

#include <bitset>
#include <cassert>
#include <cstdlib>

#include "config.hpp"
#include "theory.hpp"
#include "util.hpp"

namespace smtmbt {
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

BtorSort::BtorSort(Btor* btor, BoolectorSort sort)
    : d_solver(btor), d_sort(boolector_copy_sort(btor, sort))
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
  BtorSort* btor_sort = dynamic_cast<BtorSort*>(other.get());
  if (btor_sort)
  {
    return d_sort == btor_sort->d_sort;
  }
  return false;
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
BtorSort::is_fp() const
{
  return false;
}

bool
BtorSort::is_fun() const
{
  return boolector_is_fun_sort(d_solver, d_sort);
}

bool
BtorSort::is_int() const
{
  return false;
}

bool
BtorSort::is_real() const
{
  return false;
}

bool
BtorSort::is_rm() const
{
  return false;
}

bool
BtorSort::is_string() const
{
  return false;
}

bool
BtorSort::is_reglan() const
{
  return false;
}

uint32_t
BtorSort::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = boolector_bitvec_sort_get_width(d_solver, d_sort);
  assert(res);
  return res;
}

/* -------------------------------------------------------------------------- */
/* BtorTerm                                                                   */
/* -------------------------------------------------------------------------- */

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
  BtorTerm* btor_term = dynamic_cast<BtorTerm*>(other.get());
  if (btor_term)
  {
    return get_btor_node_id(d_solver, d_term)
           == get_btor_node_id(btor_term->d_solver, btor_term->d_term);
  }
  return false;
}

bool
BtorTerm::is_array() const
{
  return get_sort()->is_array();
}

bool
BtorTerm::is_bool() const
{
  return get_sort()->is_bool();
}

bool
BtorTerm::is_bv() const
{
  return get_sort()->is_bv();
}

bool
BtorTerm::is_fp() const
{
  return get_sort()->is_fp();
}

bool
BtorTerm::is_fun() const
{
  return get_sort()->is_fun();
}

bool
BtorTerm::is_int() const
{
  return get_sort()->is_int();
}

bool
BtorTerm::is_real() const
{
  return get_sort()->is_real();
}

bool
BtorTerm::is_rm() const
{
  return get_sort()->is_rm();
}

bool
BtorTerm::is_string() const
{
  return get_sort()->is_string();
}

bool
BtorTerm::is_reglan() const
{
  return get_sort()->is_reglan();
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
  assert(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) == 0);
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

TheoryIdVector
BtorSolver::get_supported_theories() const
{
  return {THEORY_ARRAY, THEORY_BV, THEORY_BOOL, THEORY_QUANT, THEORY_UF};
}

OpKindSet
BtorSolver::get_unsupported_op_kinds() const
{
  return {};
}

SortKindSet
BtorSolver::get_unsupported_var_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
}

SortKindSet
BtorSolver::get_unsupported_array_index_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
}

SortKindSet
BtorSolver::get_unsupported_array_element_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
}

SortKindSet
BtorSolver::get_unsupported_fun_domain_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
}

Sort
BtorSolver::mk_sort(SortKind kind)
{
  assert(kind == SORT_BOOL);
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
  assert(kind == SORT_BV);
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
  BoolectorSort btor_res;

  switch (kind)
  {
    case SORT_ARRAY:
      btor_res = boolector_array_sort(
          d_solver, get_btor_sort(sorts[0]), get_btor_sort(sorts[1]));
      break;

    case SORT_FUN:
    {
      BoolectorSort codomain = get_btor_sort(sorts.back());
      std::vector<BoolectorSort> domain;
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        domain.push_back(get_btor_sort(*it));
      }
      btor_res =
          boolector_fun_sort(d_solver, domain.data(), domain.size(), codomain);
      break;
    }

    default: assert(false);
  }
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
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

  btor_res = boolector_param(d_solver, get_btor_sort(sort), cname);
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
    btor_res = boolector_array(d_solver, get_btor_sort(sort), cname);
  }
  else if (sort->get_kind() == SORT_FUN)
  {
    btor_res = boolector_uf(d_solver, get_btor_sort(sort), cname);
  }
  else
  {
    btor_res = boolector_var(d_solver, get_btor_sort(sort), cname);
  }
  assert(btor_res);
  if (d_rng.pick_with_prob(10))
  {
    RNGenerator::Choice pick = d_rng.pick_one_of_three();
    switch (pick)
    {
      case RNGenerator::Choice::FIRST:
        assert(!pick_fun_is_bv_const()(d_solver, btor_res));
        break;
      case RNGenerator::Choice::SECOND:
        assert(!boolector_is_const(d_solver, btor_res));
        break;
      default:
        assert(pick == RNGenerator::Choice::THIRD);
        assert(sort->get_kind() == SORT_ARRAY || sort->get_kind() == SORT_FUN
               || boolector_is_var(d_solver, btor_res));
        assert(sort->get_kind() != SORT_ARRAY || sort->get_kind() != SORT_FUN
               || boolector_is_array_var(d_solver, btor_res)
               || boolector_is_uf(d_solver, btor_res));
    }
  }
  if (d_rng.pick_with_prob(1))
  {
    assert(boolector_is_equal_sort(d_solver, btor_res, btor_res));
  }
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_value(Sort sort, bool value)
{
  assert(sort->is_bool());
  BoolectorNode* btor_res =
      value ? boolector_true(d_solver) : boolector_false(d_solver);
  assert(btor_res);
  assert(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
  if (d_rng.pick_with_prob(10))
  {
    if (value)
    {
      check_is_bv_const(Solver::SPECIAL_VALUE_BV_ONE, btor_res);
    }
    else
    {
      check_is_bv_const(Solver::SPECIAL_VALUE_BV_ZERO, btor_res);
    }
  }
  if (d_rng.pick_with_prob(10))
  {
    const char* bits = boolector_get_bits(d_solver, btor_res);
    assert(std::string(bits) == (value ? "1" : "0"));
    boolector_free_bits(d_solver, bits);
  }
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

BoolectorNode*
BtorSolver::mk_value_bv_uint64(Sort sort, uint64_t value)
{
  assert(sort->is_bv());

  BoolectorNode* btor_res = 0;
  BoolectorSort btor_sort = get_btor_sort(sort);
  uint32_t bw             = sort->get_bv_size();
  bool check_bits         = bw <= 64 && d_rng.pick_with_prob(10);
  std::string str;

  if (d_rng.flip_coin())
  {
    btor_res = boolector_unsigned_int(
        d_solver, static_cast<uint32_t>(value), btor_sort);
    if (check_bits)
    {
      str = std::bitset<SMTMBT_BW_MAX>(static_cast<uint32_t>(value))
                .to_string()
                .substr(SMTMBT_BW_MAX - bw, bw);
      assert(str.size() == bw);
    }
  }
  else
  {
    btor_res = boolector_int(d_solver, static_cast<int32_t>(value), btor_sort);
    if (check_bits)
    {
      str = std::bitset<SMTMBT_BW_MAX>(static_cast<int32_t>(value))
                .to_string()
                .substr(SMTMBT_BW_MAX - bw, bw);
      assert(str.size() == bw);
    }
  }
  if (check_bits)
  {
    const char* bits = boolector_get_bits(d_solver, btor_res);
    assert(!str.empty());
    assert(std::string(bits) == str);
    boolector_free_bits(d_solver, bits);
  }
  assert(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
  assert(btor_res);
  return btor_res;
}

Term
BtorSolver::mk_value(Sort sort, std::string value, Base base)
{
  assert(sort->is_bv());

  BoolectorNode* btor_res;
  BoolectorSort btor_sort = get_btor_sort(sort);
  uint32_t bw             = sort->get_bv_size();

  switch (base)
  {
    case HEX:
      if (bw <= 64 && d_rng.flip_coin())
      {
        btor_res =
            mk_value_bv_uint64(sort, strtoull(value.c_str(), nullptr, 16));
      }
      else
      {
        btor_res = boolector_consth(d_solver, btor_sort, value.c_str());
        if (d_rng.pick_with_prob(10))
        {
          const char* bits = boolector_get_bits(d_solver, btor_res);
          assert(str_bin_to_hex(bits) == value);
          boolector_free_bits(d_solver, bits);
        }
      }
      break;

    case DEC:
      if (bw <= 64 && d_rng.flip_coin())
      {
        btor_res =
            mk_value_bv_uint64(sort, strtoull(value.c_str(), nullptr, 10));
      }
      else
      {
        btor_res = boolector_constd(d_solver, btor_sort, value.c_str());
        if (d_rng.pick_with_prob(10))
        {
          const char* bits = boolector_get_bits(d_solver, btor_res);
          assert(str_bin_to_dec(bits) == value);
          boolector_free_bits(d_solver, bits);
        }
      }
      break;

    default:
      assert(base == BIN);
      if (bw <= 64 && d_rng.flip_coin())
      {
        btor_res =
            mk_value_bv_uint64(sort, strtoull(value.c_str(), nullptr, 2));
      }
      else
      {
        btor_res = boolector_const(d_solver, value.c_str());
        if (d_rng.pick_with_prob(10))
        {
          const char* bits = boolector_get_bits(d_solver, btor_res);
          assert(bits == value);
          boolector_free_bits(d_solver, bits);
        }
      }
  }
  assert(btor_res);
  assert(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_special_value(Sort sort, const SpecialValueKind& value)
{
  assert(sort->is_bv());
  BoolectorNode* btor_res = 0;
  BoolectorSort btor_sort = get_btor_sort(sort);
  uint32_t bw             = sort->get_bv_size();
  bool check              = d_rng.pick_with_prob(10);
  bool check_bits         = bw <= 64 && d_rng.pick_with_prob(10);
  std::string str;

  if (value == SPECIAL_VALUE_BV_ZERO)
  {
    btor_res = boolector_zero(d_solver, btor_sort);
    if (check) check_is_bv_const(Solver::SPECIAL_VALUE_BV_ZERO, btor_res);
    if (check_bits)
    {
      str = std::string(bw, '0');
    }
  }
  else if (value == SPECIAL_VALUE_BV_ONE)
  {
    btor_res = boolector_one(d_solver, btor_sort);
    if (check) check_is_bv_const(Solver::SPECIAL_VALUE_BV_ONE, btor_res);
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
  else if (value == SPECIAL_VALUE_BV_ONES)
  {
    btor_res = boolector_ones(d_solver, btor_sort);
    if (check) check_is_bv_const(Solver::SPECIAL_VALUE_BV_ONES, btor_res);
    if (check_bits) str = std::string(bw, '1');
  }
  else if (value == SPECIAL_VALUE_BV_MIN_SIGNED)
  {
    btor_res = boolector_min_signed(d_solver, btor_sort);
    if (check) check_is_bv_const(Solver::SPECIAL_VALUE_BV_MIN_SIGNED, btor_res);
    if (check_bits) str = bv_special_value_min_signed_str(bw);
  }
  else
  {
    assert(value == SPECIAL_VALUE_BV_MAX_SIGNED);
    btor_res = boolector_max_signed(d_solver, btor_sort);
    if (check) check_is_bv_const(Solver::SPECIAL_VALUE_BV_MAX_SIGNED, btor_res);
    if (check_bits) str = bv_special_value_max_signed_str(bw);
  }
  assert(btor_res);
  assert(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
  if (check_bits)
  {
    const char* bits = boolector_get_bits(d_solver, btor_res);
    assert(!str.empty());
    assert(std::string(bits) == str);
    boolector_free_bits(d_solver, bits);
  }
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_term(const OpKind& kind,
                    std::vector<Term>& args,
                    std::vector<uint32_t>& params)
{
  BoolectorNode* btor_res = nullptr;
  size_t n_args           = args.size();
  size_t n_params         = params.size();
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
    assert(n_params == 2);
    btor_res = boolector_slice(d_solver, btor_args[0], params[0], params[1]);
  }
  else if (kind == Op::BV_REPEAT)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    btor_res = boolector_repeat(d_solver, btor_args[0], params[0]);
  }
  else if (kind == Op::BV_ROTATE_LEFT || kind == Op::BV_ROTATE_RIGHT)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    BoolectorNode* arg = btor_args[0];
    BoolectorSort s    = boolector_get_sort(d_solver, arg);
    uint32_t bw        = boolector_bitvec_sort_get_width(d_solver, s);

    /* use boolector_rori vs boolector_ror with 50% probability */
    if (d_rng.flip_coin())
    {
      btor_res = (kind == Op::BV_ROTATE_LEFT)
                     ? boolector_roli(d_solver, arg, params[0])
                     : boolector_rori(d_solver, arg, params[0]);
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
        uint32_t nbits   = params[0] % bw;
        tmp              = boolector_unsigned_int(d_solver, nbits, s2);
        boolector_release_sort(d_solver, s2);
      }
      else
      {
        /* arg and nbits argument with same bw */
        tmp = boolector_unsigned_int(d_solver, params[0], s);
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
    assert(n_params == 1);
    btor_res = boolector_sext(d_solver, btor_args[0], params[0]);
  }
  else if (kind == Op::BV_ZERO_EXTEND)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    btor_res = boolector_uext(d_solver, btor_args[0], params[0]);
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
      assert(false);
    }
  }
  assert(btor_res);
  assert(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
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
      d_solver, boolector_get_sort(d_solver, get_btor_term(term))));
}

void
BtorSolver::assert_formula(const Term& t)
{
  boolector_assert(d_solver, get_btor_term(t));
}

Solver::Result
BtorSolver::check_sat()
{
  int32_t res = boolector_sat(d_solver);
  if (res == BOOLECTOR_SAT) return Result::SAT;
  if (res == BOOLECTOR_UNSAT) return Result::UNSAT;
  assert(res == BOOLECTOR_UNKNOWN);
  return Result::UNKNOWN;
}

Solver::Result
BtorSolver::check_sat_assuming(std::vector<Term>& assumptions)
{
  int32_t res;
  for (const Term& t : assumptions)
  {
    boolector_assume(d_solver, get_btor_term(t));
  }
  res = boolector_sat(d_solver);
  if (res == BOOLECTOR_SAT) return Result::SAT;
  if (res == BOOLECTOR_UNSAT) return Result::UNSAT;
  assert(res == BOOLECTOR_UNKNOWN);
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
BtorSolver::get_value(std::vector<Term>& terms)
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
BtorSolver::reset_assertions()
{
  /* boolector does not support this yet */
}

/* -------------------------------------------------------------------------- */

std::vector<std::string>
BtorSolver::get_supported_sat_solvers()
{
  return {"cadical", "cms", "lingeling", "minisat", "picosat"};
}

bool
BtorSolver::check_unsat_assumption(const Term& t) const
{
  return boolector_failed(d_solver, get_btor_term(t));
}

/* -------------------------------------------------------------------------- */

BoolectorSort
BtorSolver::get_btor_sort(Sort sort) const
{
  BtorSort* btor_sort = dynamic_cast<BtorSort*>(sort.get());
  assert(btor_sort);
  return btor_sort->d_sort;
}

BoolectorNode*
BtorSolver::get_btor_term(Term term) const
{
  BtorTerm* btor_term = dynamic_cast<BtorTerm*>(term.get());
  assert(btor_term);
  return btor_term->d_term;
}

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
  assert(res);
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
  assert(res);
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
  assert(res);
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
  assert(res);
  return res;
}

void
BtorSolver::set_opt(const std::string& opt, const std::string& value)
{
  if (opt == "produce-unsat-assumptions")
  {
    /* always enabled in Boolector, can not be configured via set_opt */
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
  assert(val >= boolector_get_opt_min(d_solver, btor_opt));
  assert(val <= boolector_get_opt_max(d_solver, btor_opt));
  boolector_set_opt(d_solver, btor_opt, val);
  assert(val == boolector_get_opt(d_solver, btor_opt));
  assert(val != boolector_get_opt_dflt(d_solver, btor_opt)
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

/* -------------------------------------------------------------------------- */

std::vector<Term>
BtorSolver::btor_terms_to_terms(std::vector<BoolectorNode*>& terms) const
{
  std::vector<Term> res;
  for (BoolectorNode* t : terms)
  {
    res.push_back(std::shared_ptr<BtorTerm>(new BtorTerm(d_solver, t)));
  }
  return res;
}

std::vector<BoolectorNode*>
BtorSolver::terms_to_btor_terms(std::vector<Term>& terms) const
{
  std::vector<BoolectorNode*> res;
  for (Term& t : terms)
  {
    res.push_back(get_btor_term(t));
  }
  return res;
}

BtorSolver::BtorFunBoolUnary
BtorSolver::pick_fun_bool_unary(BtorFunBoolUnaryVector& funs) const
{
  return d_rng.pick_from_set<BtorFunBoolUnaryVector, BtorFunBoolUnary>(funs);
}

BtorSolver::BtorFunBoolUnary
BtorSolver::pick_fun_is_bv_const() const
{
  BtorFunBoolUnaryVector funs = {boolector_is_bv_const_zero,
                                 boolector_is_bv_const_one,
                                 boolector_is_bv_const_ones,
                                 boolector_is_bv_const_max_signed,
                                 boolector_is_bv_const_min_signed};
  return pick_fun_bool_unary(funs);
}

void
BtorSolver::check_is_bv_const(const Solver::SpecialValueKind& kind,
                              BoolectorNode* node) const
{
  uint32_t bw              = boolector_get_width(d_solver, node);
  RNGenerator::Choice pick = d_rng.pick_one_of_three();

  if (pick == RNGenerator::Choice::FIRST)
  {
    BtorFunBoolUnaryVector is_funs;
    BtorFunBoolUnaryVector is_not_funs;
    if (kind == Solver::SPECIAL_VALUE_BV_ONE)
    {
      is_funs.push_back(boolector_is_bv_const_one);
      if (bw > 1)
      {
        is_not_funs.push_back(boolector_is_bv_const_zero);
        is_not_funs.push_back(boolector_is_bv_const_ones);
        is_not_funs.push_back(boolector_is_bv_const_min_signed);
        is_not_funs.push_back(boolector_is_bv_const_max_signed);
      }
      else
      {
        is_funs.push_back(boolector_is_bv_const_ones);
        is_funs.push_back(boolector_is_bv_const_min_signed);

        is_not_funs.push_back(boolector_is_bv_const_zero);
        is_not_funs.push_back(boolector_is_bv_const_max_signed);
      }
    }
    else if (kind == Solver::SPECIAL_VALUE_BV_ONES)
    {
      is_funs.push_back(boolector_is_bv_const_ones);
      if (bw > 1)
      {
        is_not_funs.push_back(boolector_is_bv_const_one);
        is_not_funs.push_back(boolector_is_bv_const_zero);
        is_not_funs.push_back(boolector_is_bv_const_min_signed);
        is_not_funs.push_back(boolector_is_bv_const_max_signed);
      }
      else
      {
        is_funs.push_back(boolector_is_bv_const_one);
        is_funs.push_back(boolector_is_bv_const_min_signed);

        is_not_funs.push_back(boolector_is_bv_const_zero);
        is_not_funs.push_back(boolector_is_bv_const_max_signed);
      }
    }
    else if (kind == Solver::SPECIAL_VALUE_BV_ZERO)
    {
      is_funs.push_back(boolector_is_bv_const_zero);
      if (bw > 1)
      {
        is_not_funs.push_back(boolector_is_bv_const_one);
        is_not_funs.push_back(boolector_is_bv_const_ones);
        is_not_funs.push_back(boolector_is_bv_const_min_signed);
        is_not_funs.push_back(boolector_is_bv_const_max_signed);
      }
      else
      {
        is_funs.push_back(boolector_is_bv_const_max_signed);

        is_not_funs.push_back(boolector_is_bv_const_one);
        is_not_funs.push_back(boolector_is_bv_const_ones);
        is_not_funs.push_back(boolector_is_bv_const_min_signed);
      }
    }
    else if (kind == Solver::SPECIAL_VALUE_BV_MIN_SIGNED)
    {
      is_funs.push_back(boolector_is_bv_const_min_signed);
      if (bw > 1)
      {
        is_not_funs.push_back(boolector_is_bv_const_zero);
        is_not_funs.push_back(boolector_is_bv_const_one);
        is_not_funs.push_back(boolector_is_bv_const_ones);
        is_not_funs.push_back(boolector_is_bv_const_max_signed);
      }
      else
      {
        is_funs.push_back(boolector_is_bv_const_one);
        is_funs.push_back(boolector_is_bv_const_ones);

        is_not_funs.push_back(boolector_is_bv_const_zero);
        is_not_funs.push_back(boolector_is_bv_const_max_signed);
      }
    }
    else
    {
      assert(kind == Solver::SPECIAL_VALUE_BV_MAX_SIGNED);
      is_funs.push_back(boolector_is_bv_const_max_signed);
      if (bw > 1)
      {
        is_not_funs.push_back(boolector_is_bv_const_zero);
        is_not_funs.push_back(boolector_is_bv_const_one);
        is_not_funs.push_back(boolector_is_bv_const_ones);
        is_not_funs.push_back(boolector_is_bv_const_min_signed);
      }
      else
      {
        is_funs.push_back(boolector_is_bv_const_zero);

        is_not_funs.push_back(boolector_is_bv_const_one);
        is_not_funs.push_back(boolector_is_bv_const_ones);
        is_not_funs.push_back(boolector_is_bv_const_max_signed);
      }
    }
    if (d_rng.flip_coin())
    {
      assert(pick_fun_bool_unary(is_funs)(d_solver, node));
    }
    else
    {
      assert(!pick_fun_bool_unary(is_not_funs)(d_solver, node));
    }
  }
  else if (pick == RNGenerator::Choice::SECOND)
  {
    assert(boolector_is_const(d_solver, node));
  }
  else
  {
    assert(pick == RNGenerator::Choice::THIRD);
    assert(!boolector_is_var(d_solver, node));
  }
}

/* -------------------------------------------------------------------------- */
/* Solver-specific operators, SolverManager configuration.                    */
/* -------------------------------------------------------------------------- */

const OpKind BtorSolver::OP_DEC    = "btor-OP_DEC";
const OpKind BtorSolver::OP_INC    = "btor-OP_INC";
const OpKind BtorSolver::OP_REDAND = "btor-OP_REDAND";
const OpKind BtorSolver::OP_REDOR  = "btor-OP_REDOR";
const OpKind BtorSolver::OP_REDXOR = "btor-OP_REDXOR";
const OpKind BtorSolver::OP_UADDO  = "btor-OP_UADDO";
const OpKind BtorSolver::OP_UMULO  = "btor-OP_UMULO";
const OpKind BtorSolver::OP_USUBO  = "btor-OP_USUBO";
const OpKind BtorSolver::OP_SADDO  = "btor-OP_SADDO";
const OpKind BtorSolver::OP_SDIVO  = "btor-OP_SDIVO";
const OpKind BtorSolver::OP_SMULO  = "btor-OP_SMULO";
const OpKind BtorSolver::OP_SSUBO  = "btor-OP_SSUBO";

void
BtorSolver::configure_smgr(SolverManager* smgr) const
{
  smgr->add_op_kind(OP_DEC, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_INC, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  smgr->add_op_kind(OP_REDAND, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_REDOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_REDXOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  smgr->add_op_kind(OP_UADDO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_UMULO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_USUBO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_SADDO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_SDIVO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_SMULO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_SSUBO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
}

/* -------------------------------------------------------------------------- */
/* Solver-specific actions and states, FSM configuration.                     */
/* -------------------------------------------------------------------------- */

const ActionKind BtorSolver::ACTION_OPT_ITERATOR  = "btor-opt-iterator";
const ActionKind BtorSolver::ACTION_BV_ASSIGNMENT = "btor-bv-assignment";
const ActionKind BtorSolver::ACTION_CLONE         = "btor-clone";
const ActionKind BtorSolver::ACTION_FAILED        = "btor-failed";
const ActionKind BtorSolver::ACTION_FIXATE_ASSUMPTIONS =
    "btor-fixate-assumptions";
const ActionKind BtorSolver::ACTION_RESET_ASSUMPTIONS =
    "btor-reset-assumptions";
const ActionKind BtorSolver::ACTION_RELEASE_ALL    = "btor-release-all";
const ActionKind BtorSolver::ACTION_SIMPLIFY       = "btor-simplify";
const ActionKind BtorSolver::ACTION_SET_SAT_SOLVER = "btor-set-sat-solver";
const ActionKind BtorSolver::ACTION_SET_SYMBOL     = "btor-set-symbol";

const StateKind BtorSolver::STATE_FIX_RESET_ASSUMPTIONS =
    "btor-fix-reset-assumptions";

class BtorActionBvAssignment : public Action
{
 public:
  BtorActionBvAssignment(SolverManager& smgr)
      : Action(smgr, BtorSolver::ACTION_BV_ASSIGNMENT, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_model_gen) return false;
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::SAT) return false;
    if (!d_smgr.has_term(SORT_BV)) return false;
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    SMTMBT_CHECK_TRACE_EMPTY(tokens);
    _run();
    return 0;
  }

 private:
  void _run()
  {
    /* Note: This implements just the very basic testing for this API call.
     *       Boolector does some nasty tricks with the pointers returned by
     *       boolector_bv_assignment, which makes testing this in non-batch
     *       mode quite complicated. This API functionality should be removed
     *       as it is implemented now, and since its API will not change / be
     *       extended anymore (Boolector is succeeded by Bitwuzla), we consider
     *       it not worth the effort. */
    SMTMBT_TRACE << get_kind();
    uint64_t n = d_rng.pick<uint64_t>(1, d_smgr.get_n_terms(SORT_BV));
    BtorSolver& btor_solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    std::vector<const char*> assignments;
    for (uint64_t i = 0; i < n; ++i)
    {
      Term t                    = d_smgr.pick_term(SORT_BV);
      const char* bv_assignment = boolector_bv_assignment(
          btor_solver.get_solver(), btor_solver.get_btor_term(t));
      assignments.push_back(bv_assignment);
    }
    for (uint64_t i = 0; i < n; ++i)
    {
      boolector_free_bv_assignment(btor_solver.get_solver(), assignments[i]);
    }
  }
};

class BtorActionClone : public Action
{
 public:
  BtorActionClone(SolverManager& smgr)
      : Action(smgr, BtorSolver::ACTION_CLONE, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    SMTMBT_CHECK_TRACE_EMPTY(tokens);
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
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
      for (uint64_t i = 0, n = d_smgr.get_n_terms(); i < n; ++i)
      {
        Term t = d_smgr.pick_term();
        BoolectorNode *t_btor, *t_clone;
        BoolectorSort sort;
        int32_t id;
        const char* s;
        std::string symbol;

        t_btor = solver.get_btor_term(t);
        assert(boolector_get_btor(t_btor) == btor);
        id     = boolector_get_node_id(btor, t_btor);
        sort   = boolector_get_sort(btor, t_btor);
        s      = boolector_get_symbol(btor, t_btor);
        symbol = s ? s : "";

        /* first, test boolector_match_node */
        t_clone = boolector_match_node(clone, t_btor);
        assert(boolector_get_btor(t_clone) == clone);
        assert(id == boolector_get_node_id(clone, t_clone));
        assert(sort == boolector_get_sort(clone, t_clone));
        s = boolector_get_symbol(clone, t_clone);
        assert(symbol.empty() || s);
        assert(!s || symbol == s);
        if (boolector_is_fun(btor, t_btor))
        {
          assert(boolector_is_fun(clone, t_clone));
          assert(boolector_fun_get_domain_sort(btor, t_btor)
                 == boolector_fun_get_domain_sort(clone, t_clone));
          assert(boolector_fun_get_codomain_sort(btor, t_btor)
                 == boolector_fun_get_codomain_sort(clone, t_clone));
        }
        boolector_release(clone, t_clone);

        /* second, test boolector_match_node_by_id */
        t_clone = boolector_match_node_by_id(clone, id < 0 ? -id : id);
        assert(boolector_get_btor(t_clone) == clone);
        assert(sort == boolector_get_sort(clone, t_clone));
        s = boolector_get_symbol(clone, t_clone);
        assert(symbol.empty() || s);
        assert(!s || symbol == s);
        if (boolector_is_fun(btor, t_btor))
        {
          assert(boolector_is_fun(clone, t_clone));
          assert(boolector_fun_get_domain_sort(btor, t_btor)
                 == boolector_fun_get_domain_sort(clone, t_clone));
          assert(boolector_fun_get_codomain_sort(btor, t_btor)
                 == boolector_fun_get_codomain_sort(clone, t_clone));
        }
        boolector_release(clone, t_clone);

        /* finally, test boolector_match_node_by_symbol */
        if (!symbol.empty())
        {
          t_clone = boolector_match_node_by_symbol(clone, symbol.c_str());
          assert(boolector_get_btor(t_clone) == clone);
          assert(id == boolector_get_node_id(clone, t_clone));
          assert(sort == boolector_get_sort(clone, t_clone));
          if (boolector_is_fun(btor, t_btor))
          {
            assert(boolector_is_fun(clone, t_clone));
            assert(boolector_fun_get_domain_sort(btor, t_btor)
                   == boolector_fun_get_domain_sort(clone, t_clone));
            assert(boolector_fun_get_codomain_sort(btor, t_btor)
                   == boolector_fun_get_codomain_sort(clone, t_clone));
          }
          boolector_release(clone, t_clone);
        }
      }
    }
    boolector_delete(clone);
  }
};

class BtorActionFailed : public Action
{
 public:
  BtorActionFailed(SolverManager& smgr)
      : Action(smgr, BtorSolver::ACTION_FAILED, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_sat_called) return false;
    if (d_smgr.d_sat_result != Solver::Result::UNSAT) return false;
    if (!d_smgr.d_incremental) return false;
    if (!d_smgr.has_assumed()) return false;
    Term term = d_smgr.pick_assumed_assumption();
    _run(term);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    SMTMBT_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = d_smgr.get_term(str_to_uint32(tokens[0]));
    SMTMBT_CHECK_TRACE_TERM(term, tokens[0]);
    _run(term);
    return 0;
  }

 private:
  void _run(Term term)
  {
    SMTMBT_TRACE << get_kind() << " " << term;
    BtorSolver& btor_solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    (void) boolector_failed(btor_solver.get_solver(),
                            btor_solver.get_btor_term(term));
  }
};

class BtorActionFixateAssumptions : public Action
{
 public:
  BtorActionFixateAssumptions(SolverManager& smgr)
      : Action(smgr, BtorSolver::ACTION_FIXATE_ASSUMPTIONS, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_incremental) return false;
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    SMTMBT_CHECK_TRACE_EMPTY(tokens);
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    d_smgr.clear();
    boolector_fixate_assumptions(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionOptIterator : public Action
{
 public:
  BtorActionOptIterator(SolverManager& smgr)
      : Action(smgr, BtorSolver::ACTION_OPT_ITERATOR, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    SMTMBT_CHECK_TRACE_EMPTY(tokens);
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    Btor* btor = static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver();
    for (BtorOption opt = boolector_first_opt(btor); opt < BTOR_OPT_NUM_OPTS;
         opt            = boolector_next_opt(btor, opt))
    {
      assert(boolector_has_opt(btor, opt));
      assert(boolector_get_opt(btor, opt) >= boolector_get_opt_min(btor, opt));
      assert(boolector_get_opt(btor, opt) <= boolector_get_opt_max(btor, opt));
      assert(boolector_get_opt_min(btor, opt)
             <= boolector_get_opt_max(btor, opt));
      assert(boolector_get_opt_dflt(btor, opt)
             >= boolector_get_opt_min(btor, opt));
      assert(boolector_get_opt_dflt(btor, opt)
             <= boolector_get_opt_max(btor, opt));
      std::string lng = boolector_get_opt_lng(btor, opt);
      const char* s   = boolector_get_opt_shrt(btor, opt);
      if (s != nullptr)
      {
        std::string shrt(s);
        assert(shrt.size() <= lng.size());
      }
      (void) boolector_get_opt_desc(btor, opt);
    }
    assert(!boolector_has_opt(
        btor,
        (BtorOption) d_rng.pick<uint32_t>(BTOR_OPT_NUM_OPTS, UINT32_MAX)));
  }
};

class BtorActionReleaseAll : public Action
{
 public:
  BtorActionReleaseAll(SolverManager& smgr)
      : Action(smgr, BtorSolver::ACTION_RELEASE_ALL, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    SMTMBT_CHECK_TRACE_EMPTY(tokens);
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    d_smgr.clear();
    boolector_release_all(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionResetAssumptions : public Action
{
 public:
  BtorActionResetAssumptions(SolverManager& smgr)
      : Action(smgr, BtorSolver::ACTION_RESET_ASSUMPTIONS, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.d_incremental) return false;
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    SMTMBT_CHECK_TRACE_EMPTY(tokens);
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    d_smgr.clear();
    boolector_reset_assumptions(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionSetSatSolver : public Action
{
 public:
  BtorActionSetSatSolver(SolverManager& smgr)
      : Action(smgr, BtorSolver::ACTION_SET_SAT_SOLVER, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    BtorSolver& solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    std::string sat_solver =
        d_rng.pick_from_set<std::vector<std::string>, std::string>(
            solver.get_supported_sat_solvers());
    _run(sat_solver);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size() == 1);
    SMTMBT_CHECK_TRACE_NTOKENS(1, tokens.size());
    _run(tokens[0]);
    return 0;
  }

 private:
  void _run(std::string sat_solver)
  {
    SMTMBT_TRACE << get_kind() << " " << sat_solver;
    BtorSolver& solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    boolector_set_sat_solver(solver.get_solver(), sat_solver.c_str());
  }
};

class BtorActionSimplify : public Action
{
 public:
  BtorActionSimplify(SolverManager& smgr)
      : Action(smgr, BtorSolver::ACTION_SIMPLIFY, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    BtorSolver& solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    if (solver.get_solver() == nullptr) return false;
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    SMTMBT_CHECK_TRACE_EMPTY(tokens);
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    boolector_simplify(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionSetSymbol : public Action
{
 public:
  BtorActionSetSymbol(SolverManager& smgr)
      : Action(smgr, BtorSolver::ACTION_SET_SYMBOL, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    Term term          = d_smgr.pick_term();
    std::string symbol = d_smgr.pick_symbol();
    _run(term, symbol);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    SMTMBT_CHECK_TRACE_NTOKENS(2, tokens.size());
    Term term = d_smgr.get_term(str_to_uint32(tokens[0]));
    SMTMBT_CHECK_TRACE_TERM(term, tokens[0]);
    std::string symbol = str_to_str(tokens[1]);
    _run(term, symbol);
    return 0;
  }

 private:
  void _run(Term term, std::string symbol)
  {
    SMTMBT_TRACE << get_kind() << " " << term << " \"" << symbol << "\"";
    BtorSolver& btor_solver = static_cast<BtorSolver&>(d_smgr.get_solver());
    (void) boolector_set_symbol(btor_solver.get_solver(),
                                btor_solver.get_btor_term(term),
                                symbol.c_str());
  }
};

/* -------------------------------------------------------------------------- */

void
BtorSolver::configure_fsm(FSM* fsm) const
{
  State* s_assert = fsm->get_state(State::ASSERT);
  State* s_delete = fsm->get_state(State::DELETE);
  State* s_opt    = fsm->get_state(State::OPT);

  State* s_fix_reset_assumptions = fsm->new_state(STATE_FIX_RESET_ASSUMPTIONS);

  auto t_default = fsm->new_action<TransitionDefault>();

  // options
  auto a_opt_it = fsm->new_action<BtorActionOptIterator>();
  fsm->add_action_to_all_states(a_opt_it, 100);

  // boolector_bv_assignment
  auto a_bv_ass = fsm->new_action<BtorActionBvAssignment>();
  fsm->add_action_to_all_states(a_bv_ass, 100);

  // boolector_clone
  auto a_clone = fsm->new_action<BtorActionClone>();
  fsm->add_action_to_all_states(a_clone, 100);

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
  fsm->add_action_to_all_states_next(
      t_default, 2, s_fix_reset_assumptions, {State::OPT});

  // boolector_release_all
  auto a_release_all = fsm->new_action<BtorActionReleaseAll>();
  s_delete->add_action(a_release_all, 100);

  // boolector_simplify
  auto a_simplify = fsm->new_action<BtorActionSimplify>();
  fsm->add_action_to_all_states(a_simplify, 100);

  // boolector_set_sat_solver
  auto a_set_sat_solver = fsm->new_action<BtorActionSetSatSolver>();
  s_opt->add_action(a_set_sat_solver, 100);

  // boolector_set_symbol
  auto a_set_symbol = fsm->new_action<BtorActionSetSymbol>();
  fsm->add_action_to_all_states(a_set_symbol, 100);
}

}  // namespace btor
}  // namespace smtmbt

#endif
