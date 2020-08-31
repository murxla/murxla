#ifdef SMTMBT_USE_YICES

#include "yices_solver.hpp"

#include "util.hpp"

namespace smtmbt {
namespace yices {

/* -------------------------------------------------------------------------- */
/* YicesSort */
/* -------------------------------------------------------------------------- */

size_t
YicesSort::hash() const
{
  return d_sort;
}

bool
YicesSort::equals(const Sort& other) const
{
  YicesSort* yices_sort = dynamic_cast<YicesSort*>(other.get());
  if (yices_sort)
  {
    return d_sort == yices_sort->d_sort;
  }
  return false;
}

bool
YicesSort::is_bool() const
{
  return yices_type_is_bool(d_sort);
}

bool
YicesSort::is_bv() const
{
  return yices_type_is_bitvector(d_sort);
}

bool
YicesSort::is_fp() const
{
  return false;
}

bool
YicesSort::is_int() const
{
  bool res = yices_type_is_int(d_sort);
  assert(!res || yices_type_is_arithmetic(d_sort));
  return res;
}

bool
YicesSort::is_real() const
{
  bool res = yices_type_is_real(d_sort);
  assert(!res || yices_type_is_arithmetic(d_sort));
  return res;
}

bool
YicesSort::is_reglan() const
{
  return false;
}

bool
YicesSort::is_rm() const
{
  return false;
}

bool
YicesSort::is_string() const
{
  return false;
}

uint32_t
YicesSort::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = yices_bvtype_size(d_sort);
  assert(res);
  return res;
}

/* -------------------------------------------------------------------------- */
/* YicesTerm */
/* -------------------------------------------------------------------------- */

size_t
YicesTerm::hash() const
{
  return d_term;
}

bool
YicesTerm::equals(const Term& other) const
{
  YicesTerm* yices_term = dynamic_cast<YicesTerm*>(other.get());
  if (yices_term)
  {
    return d_term == yices_term->d_term;
  }
  return false;
}

/* -------------------------------------------------------------------------- */
/* YicesSolver */
/* -------------------------------------------------------------------------- */

void
YicesSolver::new_solver()
{
  yices_init();
  d_config         = yices_new_config();
  d_is_initialized = true;
}

void
YicesSolver::delete_solver()
{
  assert(d_config);
  if (d_context) yices_free_context(d_context);
  yices_free_config(d_config);
  yices_exit();
}

bool
YicesSolver::is_initialized() const
{
  return d_is_initialized;
}

TheoryIdVector
YicesSolver::get_supported_theories() const
{
  return {THEORY_ARRAY, THEORY_BV, THEORY_BOOL, THEORY_INT, THEORY_REAL};
}

OpKindSet
YicesSolver::get_unsupported_op_kinds() const
{
  return {OP_BV_DEC,
          OP_BV_INC,
          OP_BV_REDXOR,
          OP_BV_SADDO,
          OP_BV_SDIVO,
          OP_BV_SMULO,
          OP_BV_SSUBO,
          OP_BV_UADDO,
          OP_BV_UMULO,
          OP_BV_USUBO};
}

void
YicesSolver::set_opt(const std::string& opt, const std::string& value)
{
  if (opt == "produce-models" || opt == "produce-unsat-assumptions")
  {
    /* always enabled in Yices, can not be configured via set_opt */
    return;
  }

  assert(d_config);
  assert(d_context == nullptr);
  assert(opt == "incremental");
  if (value == "true")
  {
    yices_set_config(d_config, "mode", "push-pop");
    d_incremental = true;
  }
  else
  {
    assert(value == "false");
    yices_set_config(d_config, "mode", "one-shot");
    d_incremental = false;
  }
}

bool
YicesSolver::check_failed_assumption(const Term& t) const
{
  // TODO
}

std::string
YicesSolver::get_option_name_incremental() const
{
  return "incremental";
}

std::string
YicesSolver::get_option_name_model_gen() const
{
  /* always enabled in Yices, can not be configured via set_opt */
  return "produce-models";
}

std::string
YicesSolver::get_option_name_unsat_assumptions() const
{
  /* always enabled in Yices, can not be configured via set_opt */
  return "produce-unsat-assumptions";
}

bool
YicesSolver::option_incremental_enabled() const
{
  return d_incremental;
}

bool
YicesSolver::option_model_gen_enabled() const
{
  return true;
}

bool
YicesSolver::option_unsat_assumptions_enabled() const
{
  return true;
}

type_t
YicesSolver::get_yices_sort(Sort sort) const
{
  YicesSort* yices_sort = dynamic_cast<YicesSort*>(sort.get());
  assert(yices_sort);
  return yices_sort->d_sort;
}

term_t
YicesSolver::get_yices_term(Term term) const
{
  YicesTerm* yices_term = dynamic_cast<YicesTerm*>(term.get());
  assert(yices_term);
  return yices_term->d_term;
}

Term
YicesSolver::mk_var(Sort sort, const std::string& name)
{
  term_t yices_term = yices_new_variable(get_yices_sort(sort));
  assert(yices_term >= 0);
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_term));
  assert(res);
  return res;
}

Term
YicesSolver::mk_const(Sort sort, const std::string& name)
{
  term_t yices_term = yices_new_uninterpreted_term(get_yices_sort(sort));
  assert(yices_term >= 0);
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_term));
  assert(res);
  return res;
}

Term
YicesSolver::mk_value(Sort sort, bool value)
{
  term_t yices_term = value ? yices_true() : yices_false();
  assert(yices_term >= 0);
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_term));
  assert(res);
  return res;
}

Term
YicesSolver::mk_value(Sort sort, std::string value)
{
  term_t yices_res;

  switch (sort->get_kind())
  {
    case SORT_INT:
    {
      assert(sort->is_int());
      RNGenerator::Choice pick = d_rng.pick_one_of_three();
      switch (pick)
      {
        case RNGenerator::Choice::FIRST:
          yices_res = yices_int32(
              static_cast<int32_t>(strtoul(value.c_str(), nullptr, 10)));
          break;
        case RNGenerator::Choice::SECOND:
          yices_res = yices_int64(
              static_cast<int64_t>(strtoull(value.c_str(), nullptr, 10)));
          break;
        default:
          assert(pick == RNGenerator::Choice::THIRD);
          yices_res = yices_parse_rational(value.c_str());
      }
    }
    break;

    case SORT_REAL:
      assert(sort->is_real());
      if (value.find('.') == std::string::npos && d_rng.flip_coin())
      {
        RNGenerator::Choice pick = d_rng.pick_one_of_three();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            yices_res = yices_int32(
                static_cast<int32_t>(strtoul(value.c_str(), nullptr, 10)));
            break;
          case RNGenerator::Choice::SECOND:
            yices_res = yices_int64(
                static_cast<int64_t>(strtoull(value.c_str(), nullptr, 10)));
            break;
          default:
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_parse_rational(value.c_str());
        }
      }
      else
      {
        yices_res = yices_parse_float(value.c_str());
      }
      break;

    default: assert(false);
  }
  assert(yices_res >= 0);
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_res));
  assert(res);
  return res;
}

Term
YicesSolver::mk_value(Sort sort, std::string num, std::string den)
{
  assert(sort->is_real());
  term_t yices_res;

  if (d_rng.flip_coin())
  {
    yices_res = yices_rational32(
        static_cast<int32_t>(strtoul(num.c_str(), nullptr, 10)),
        static_cast<uint32_t>(strtoul(den.c_str(), nullptr, 10)));
  }
  else
  {
    yices_res = yices_rational64(
        static_cast<int64_t>(strtoull(num.c_str(), nullptr, 10)),
        static_cast<uint64_t>(strtoull(den.c_str(), nullptr, 10)));
  }
  assert(yices_res >= 0);
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_res));
  assert(res);
  return res;
}

std::vector<int32_t>
YicesSolver::bin_str_to_int_array(std::string s)
{
  std::vector<int32_t> res;
  for (char c : s)
  {
    assert(c == '0' || c == '1');
    res.push_back(c == '0' ? 0 : 1);
  }
  return res;
}

term_t
YicesSolver::mk_value_bv_int_or_special(Sort sort, std::string value, Base base)
{
  assert(sort->is_bv());

  term_t yices_res;
  uint64_t val;
  uint32_t bw          = sort->get_bv_size();
  bool use_special_fun = d_rng.flip_coin();
  bool check_bits      = bw <= 64 && d_rng.pick_with_prob(10);
  std::string str;

  if (base == DEC)
  {
    std::stringstream ss;
    ss << (d_rng.flip_coin() ? "-" : "") << value;
    value = ss.str();
    val   = static_cast<uint64_t>(strtoul(value.c_str(), nullptr, 10));
  }
  else if (base == HEX)
  {
    val = static_cast<uint64_t>(strtoul(value.c_str(), nullptr, 16));
  }
  else
  {
    assert(base == BIN);
    val = static_cast<uint64_t>(strtoul(value.c_str(), nullptr, 2));
  }

  if (use_special_fun && val == 0)
  {
    yices_res = yices_bvconst_zero(bw);
    if (check_bits)
    {
      str = std::string(bw, '0');
    }
  }
  else if (use_special_fun && val == 1)
  {
    yices_res = yices_bvconst_one(bw);
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
  else if (use_special_fun && is_bv_special_value_ones_uint64(bw, val))
  {
    yices_res = yices_bvconst_minus_one(bw);
    if (check_bits) str = std::string(bw, '1');
  }
  else
  {
    RNGenerator::Choice pick = d_rng.pick_one_of_four();
    switch (pick)
    {
      case RNGenerator::Choice::FIRST:
        yices_res = yices_bvconst_uint32(bw, static_cast<uint32_t>(val));
        if (check_bits)
        {
          str = std::bitset<64>(static_cast<uint32_t>(val))
                    .to_string()
                    .substr(64 - bw, bw);
        }
        break;
      case RNGenerator::Choice::SECOND:
        yices_res = yices_bvconst_uint64(bw, static_cast<uint64_t>(val));
        if (check_bits)
        {
          str = std::bitset<64>(static_cast<uint64_t>(val))
                    .to_string()
                    .substr(64 - bw, bw);
        }
        break;
      case RNGenerator::Choice::THIRD:
        yices_res = yices_bvconst_int32(bw, static_cast<int32_t>(val));
        if (check_bits)
        {
          str = std::bitset<64>(static_cast<int32_t>(val))
                    .to_string()
                    .substr(64 - bw, bw);
        }
        break;
      default:
        assert(pick == RNGenerator::Choice::FOURTH);
        yices_res = yices_bvconst_int64(bw, static_cast<int64_t>(val));
        if (check_bits)
        {
          str = std::bitset<64>(static_cast<int64_t>(val))
                    .to_string()
                    .substr(64 - bw, bw);
        }
    }
  }
  assert(yices_res >= 0);
  if (check_bits)
  {
    assert(!str.empty());
    assert(str.size() == bw);
    std::vector<int32_t> expected = bin_str_to_int_array(str);
    std::vector<int32_t> bits(bw);
    int32_t r = yices_bv_const_value(yices_res, &bits[0]);
    assert(r >= 0);
    for (size_t i = 0; i < bw; ++i)
    {
      assert(expected[i] == bits[i]);
    }
  }
  return yices_res;
}

Term
YicesSolver::mk_value(Sort sort, std::string value, Base base)
{
  assert(sort->is_bv());

  term_t yices_res;
  uint32_t bw = sort->get_bv_size();

  switch (base)
  {
    case DEC: yices_res = mk_value_bv_int_or_special(sort, value, base); break;

    case HEX:
    {
      if (d_rng.flip_coin())
      {
        yices_res = mk_value_bv_int_or_special(sort, value, base);
      }
      else
      {
        yices_res = yices_parse_bvhex(value.c_str());
      }
    }
    break;

    default:
    {
      assert(base == BIN);
      RNGenerator::Choice pick = d_rng.pick_one_of_three();
      switch (pick)
      {
        case RNGenerator::Choice::FIRST:
          yices_res = mk_value_bv_int_or_special(sort, value, base);
          break;
        case RNGenerator::Choice::SECOND:
          {
            std::vector<int32_t> a = bin_str_to_int_array(value);
            yices_res              = yices_bvconst_from_array(bw, &a[0]);
          }
          break;
        default:
          assert(pick == RNGenerator::Choice::THIRD);
          yices_res = yices_parse_bvbin(value.c_str());
      }
    }
  }
  assert(yices_res >= 0);
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_res));
  assert(res);
  return res;
}

Sort
YicesSolver::mk_sort(SortKind kind)
{
  type_t yices_res;
  switch (kind)
  {
    case SORT_BOOL: yices_res = yices_bool_type(); break;
    case SORT_INT: yices_res = yices_int_type(); break;
    case SORT_REAL: yices_res = yices_real_type(); break;

    default: assert(false);
  }
  assert(yices_res > 0);
  std::shared_ptr<YicesSort> res(new YicesSort(yices_res));
  assert(res);
}

Sort
YicesSolver::mk_sort(SortKind kind, uint32_t size)
{
  type_t yices_res;
  switch (kind)
  {
    case SORT_BV: yices_res = yices_bv_type(size); break;
    default: assert(false);
  }
  std::shared_ptr<YicesSort> res(new YicesSort(yices_res));
  assert(res);
}

Sort
YicesSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  // TODO
}

//////
////
//__YICES_DLLSPEC__ extern term_t yices_application(term_t fun, uint32_t n,
// const term_t arg[]);
//__YICES_DLLSPEC__ extern term_t yices_application1(term_t fun, term_t arg1);
//__YICES_DLLSPEC__ extern term_t yices_application2(term_t fun, term_t arg1,
// term_t arg2);
//__YICES_DLLSPEC__ extern term_t yices_application3(term_t fun, term_t arg1,
// term_t arg2, term_t arg3);
//__YICES_DLLSPEC__ extern term_t yices_tuple(uint32_t n, const term_t arg[]);
//__YICES_DLLSPEC__ extern term_t yices_pair(term_t arg1, term_t arg2);
//__YICES_DLLSPEC__ extern term_t yices_triple(term_t arg1, term_t arg2, term_t
// arg3);
//__YICES_DLLSPEC__ extern term_t yices_select(uint32_t index, term_t tuple);
//__YICES_DLLSPEC__ extern term_t yices_tuple_update(term_t tuple, uint32_t
// index, term_t new_v);
//__YICES_DLLSPEC__ extern term_t yices_update(term_t fun, uint32_t n, const
// term_t arg[], term_t new_v);
//__YICES_DLLSPEC__ extern term_t yices_update1(term_t fun, term_t arg1, term_t
// new_v);
//__YICES_DLLSPEC__ extern term_t yices_update2(term_t fun, term_t arg1, term_t
// arg2, term_t new_v);
//__YICES_DLLSPEC__ extern term_t yices_update3(term_t fun, term_t arg1, term_t
// arg2, term_t arg3, term_t new_v);
//__YICES_DLLSPEC__ extern term_t yices_forall(uint32_t n, term_t var[], term_t
// body);
//__YICES_DLLSPEC__ extern term_t yices_exists(uint32_t n, term_t var[], term_t
// body);
//__YICES_DLLSPEC__ extern term_t yices_lambda(uint32_t n, const term_t var[],
// term_t body);
//__YICES_DLLSPEC__ extern term_t yices_zero(void);
//__YICES_DLLSPEC__ extern term_t yices_parse_float(const char *s);
//__YICES_DLLSPEC__ extern term_t yices_add(term_t t1, term_t t2);     // t1 +
// t2
//__YICES_DLLSPEC__ extern term_t yices_sub(term_t t1, term_t t2);     // t1 -
// t2
//__YICES_DLLSPEC__ extern term_t yices_neg(term_t t1);                // -t1
//__YICES_DLLSPEC__ extern term_t yices_mul(term_t t1, term_t t2);     // t1 *
// t2
//__YICES_DLLSPEC__ extern term_t yices_square(term_t t1);             // t1 *
// t1
//__YICES_DLLSPEC__ extern term_t yices_power(term_t t1, uint32_t d);  // t1 ^ d
//__YICES_DLLSPEC__ extern term_t yices_sum(uint32_t n, const term_t t[]);
//__YICES_DLLSPEC__ extern term_t yices_product(uint32_t n, const term_t t[]);
//__YICES_DLLSPEC__ extern term_t yices_division(term_t t1, term_t t2);
//__YICES_DLLSPEC__ extern term_t yices_idiv(term_t t1, term_t t2);
//__YICES_DLLSPEC__ extern term_t yices_imod(term_t t1, term_t t2);
//__YICES_DLLSPEC__ extern term_t yices_divides_atom(term_t t1, term_t t2);
//__YICES_DLLSPEC__ extern term_t yices_is_int_atom(term_t t);
//__YICES_DLLSPEC__ extern term_t yices_abs(term_t t);
//__YICES_DLLSPEC__ extern term_t yices_floor(term_t t);
//__YICES_DLLSPEC__ extern term_t yices_ceil(term_t t);
//__YICES_DLLSPEC__ extern term_t yices_poly_int32(uint32_t n, const int32_t
// a[], const term_t t[]);
//__YICES_DLLSPEC__ extern term_t yices_poly_int64(uint32_t n, const int64_t
// a[], const term_t t[]);
//__YICES_DLLSPEC__ extern term_t yices_poly_rational32(uint32_t n, const
// int32_t num[], const uint32_t den[], const term_t t[]);
//__YICES_DLLSPEC__ extern term_t yices_poly_rational64(uint32_t n, const
// int64_t num[], const uint64_t den[], const term_t t[]);
//__YICES_DLLSPEC__ extern term_t yices_arith_eq_atom(term_t t1, term_t t2); //
// t1 == t2
//__YICES_DLLSPEC__ extern term_t yices_arith_neq_atom(term_t t1, term_t t2); //
// t1 != t2
//__YICES_DLLSPEC__ extern term_t yices_arith_geq_atom(term_t t1, term_t t2); //
// t1 >= t2
//__YICES_DLLSPEC__ extern term_t yices_arith_leq_atom(term_t t1, term_t t2); //
// t1 <= t2
//__YICES_DLLSPEC__ extern term_t yices_arith_gt_atom(term_t t1, term_t t2); //
// t1 > t2
//__YICES_DLLSPEC__ extern term_t yices_arith_lt_atom(term_t t1, term_t t2); //
// t1 < t2
//__YICES_DLLSPEC__ extern term_t yices_arith_eq0_atom(term_t t);   // t == 0
//__YICES_DLLSPEC__ extern term_t yices_arith_neq0_atom(term_t t);  // t != 0
//__YICES_DLLSPEC__ extern term_t yices_arith_geq0_atom(term_t t);  // t >= 0
//__YICES_DLLSPEC__ extern term_t yices_arith_leq0_atom(term_t t);  // t <= 0
//__YICES_DLLSPEC__ extern term_t yices_arith_gt0_atom(term_t t);   // t > 0
//__YICES_DLLSPEC__ extern term_t yices_arith_lt0_atom(term_t t);   // t < 0
// int32_t a[]);
//__YICES_DLLSPEC__ extern term_t yices_parse_bvbin(const char *s);
//__YICES_DLLSPEC__ extern term_t yices_parse_bvhex(const char *s);
// ubtraction (t1 - t2)
//__YICES_DLLSPEC__ extern term_t yices_bvsquare(term_t t1);             //
// square (t1 * t1)
//__YICES_DLLSPEC__ extern term_t yices_bvpower(term_t t1, uint32_t d);  //
// exponentiation (t1 ^ d)
//__YICES_DLLSPEC__ extern term_t yices_bvsum(uint32_t n, const term_t t[]);
//__YICES_DLLSPEC__ extern term_t yices_bvproduct(uint32_t n, const term_t t[]);
//__YICES_DLLSPEC__ extern term_t yices_shift_left0(term_t t, uint32_t n);
//__YICES_DLLSPEC__ extern term_t yices_shift_left1(term_t t, uint32_t n);
//__YICES_DLLSPEC__ extern term_t yices_shift_right0(term_t t, uint32_t n);
//__YICES_DLLSPEC__ extern term_t yices_shift_right1(term_t t, uint32_t n);
//__YICES_DLLSPEC__ extern term_t yices_ashift_right(term_t t, uint32_t n);
//__YICES_DLLSPEC__ extern term_t yices_bvarray(uint32_t n, const term_t arg[]);
//__YICES_DLLSPEC__ extern term_t yices_bitextract(term_t t, uint32_t i);
//__YICES_DLLSPEC__ extern term_t yices_bveq_atom(term_t t1, term_t t2);   // t1
//== t2
//__YICES_DLLSPEC__ extern term_t yices_bvneq_atom(term_t t1, term_t t2);  // t1
//!= t2
//////

Term
YicesSolver::mk_term(const OpKind& kind,
                     std::vector<Term>& args,
                     std::vector<uint32_t>& params)
{
  term_t yices_res;
  size_t n_args                  = args.size();
  size_t n_params                = params.size();
  std::vector<term_t> yices_args = terms_to_yices_terms(args);
  std::vector<term_t> vars;

  switch (kind)
  {
    case OP_DISTINCT:
      assert(n_args > 1);
      if (d_rng.flip_coin())
      {
        yices_res = yices_distinct(n_args, &yices_args[0]);
      }
      else
      {
        yices_res = mk_term_pairwise(yices_args, yices_neq);
      }
      break;

    case OP_EQUAL:
      assert(n_args == 2);
      yices_res = yices_eq(yices_args[0], yices_args[1]);
      break;

    case OP_ITE:
      assert(n_args == 3);
      yices_res = yices_ite(yices_args[0], yices_args[1], yices_args[2]);
      break;

    /* Arrays */
    case OP_ARRAY_SELECT:
      // TODO
      break;

    case OP_ARRAY_STORE:
      // TODO
      break;

    /* Boolean */
    case OP_AND:
      if (n_args > 3)
      {
        yices_res = yices_and(n_args, &yices_args[0]);
      }
      else if (n_args == 3)
      {
        RNGenerator::Choice pick = d_rng.pick_one_of_three();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            yices_res = yices_and3(yices_args[0], yices_args[1], yices_args[2]);
            break;
          case RNGenerator::Choice::SECOND:
            yices_res = mk_term_pairwise(yices_args, yices_and2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_and(n_args, &yices_args[0]);
          }
        }
      }
      else
      {
        assert(n_args == 2);
        if (d_rng.flip_coin())
        {
          yices_res = yices_and2(yices_args[0], yices_args[1]);
        }
        else
        {
          yices_res = yices_and(n_args, &yices_args[0]);
        }
      }
      break;

    case OP_IFF:
      assert(n_args == 2);
      yices_res = yices_iff(yices_args[0], yices_args[1]);
      break;

    case OP_IMPLIES:
      assert(n_args == 2);
      yices_res = yices_implies(yices_args[0], yices_args[1]);
      break;

    case OP_NOT:
      assert(n_args == 1);
      yices_res = yices_not(yices_args[0]);
      break;

    case OP_OR:
      if (n_args > 3)
      {
        yices_res = yices_or(n_args, &yices_args[0]);
      }
      else if (n_args == 3)
      {
        RNGenerator::Choice pick = d_rng.pick_one_of_three();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            yices_res = yices_or3(yices_args[0], yices_args[1], yices_args[2]);
            break;
          case RNGenerator::Choice::SECOND:
            yices_res = mk_term_pairwise(yices_args, yices_or2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_or(n_args, &yices_args[0]);
          }
        }
      }
      else
      {
        assert(n_args == 2);
        if (d_rng.flip_coin())
        {
          yices_res =
              yices_or2(get_yices_term(args[0]), get_yices_term(args[1]));
        }
        else
        {
          yices_res = yices_or(n_args, &yices_args[0]);
        }
      }
      break;

    case OP_XOR:
      if (n_args > 3)
      {
        yices_res = yices_xor(n_args, &yices_args[0]);
      }
      else if (n_args == 3)
      {
        RNGenerator::Choice pick = d_rng.pick_one_of_three();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            yices_res = yices_xor3(yices_args[0], yices_args[1], yices_args[2]);
            break;
          case RNGenerator::Choice::SECOND:
            yices_res = mk_term_pairwise(yices_args, yices_xor2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_xor(n_args, &yices_args[0]);
          }
        }
      }
      else
      {
        assert(n_args == 2);
        if (d_rng.flip_coin())
        {
          yices_res = yices_xor2(yices_args[0], yices_args[1]);
        }
        else
        {
          yices_res = yices_xor(n_args, &yices_args[0]);
        }
      }
      break;

    /* BV */
    case OP_BV_EXTRACT:
      assert(n_args == 1);
      assert(n_params == 2);
      yices_res = yices_bvextract(yices_args[0], params[1], params[0]);
      break;

    case OP_BV_REPEAT:
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_bvrepeat(yices_args[0], params[0]);
      break;

    case OP_BV_ROTATE_LEFT:
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_rotate_left(yices_args[0], params[0]);
      break;

    case OP_BV_ROTATE_RIGHT:
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_rotate_right(yices_args[0], params[0]);
      break;

    case OP_BV_SIGN_EXTEND:
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_sign_extend(yices_args[0], params[0]);
      break;
    case OP_BV_ZERO_EXTEND:
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_zero_extend(yices_args[0], params[0]);
      break;

    case OP_BV_ADD:
      assert(n_args == 2);
      yices_res = yices_bvadd(yices_args[0], yices_args[1]);
      break;

    case OP_BV_AND:
      if (n_args > 3)
      {
        yices_res = yices_bvand(n_args, &yices_args[0]);
      }
      else if (n_args == 3)
      {
        RNGenerator::Choice pick = d_rng.pick_one_of_three();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            yices_res =
                yices_bvand3(yices_args[0], yices_args[1], yices_args[2]);
            break;
          case RNGenerator::Choice::SECOND:
            yices_res = mk_term_pairwise(yices_args, yices_bvand2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_bvand(n_args, &yices_args[0]);
          }
        }
      }
      else
      {
        assert(n_args == 2);
        if (d_rng.flip_coin())
        {
          yices_res = yices_bvand2(yices_args[0], yices_args[1]);
        }
        else
        {
          yices_res = yices_bvand(n_args, &yices_args[0]);
        }
      }
      break;

    case OP_BV_ASHR:
      assert(n_args == 2);
      yices_res = yices_bvashr(yices_args[0], yices_args[1]);
      break;
    case OP_BV_COMP:
      assert(n_args == 2);
      yices_res = yices_redcomp(yices_args[0], yices_args[1]);
      break;
    case OP_BV_CONCAT:
      assert(n_args > 1);
      if (d_rng.flip_coin())
      {
        yices_res = yices_bvconcat(n_args, &yices_args[0]);
      }
      else
      {
        yices_res = mk_term_pairwise(yices_args, yices_bvconcat2);
      }
      break;
    case OP_BV_LSHR:
      assert(n_args == 2);
      yices_res = yices_bvlshr(yices_args[0], yices_args[1]);
      break;
    case OP_BV_MULT:
      assert(n_args == 2);
      yices_res = yices_bvmul(yices_args[0], yices_args[1]);
      break;
    case OP_BV_NAND:
      assert(n_args == 2);
      yices_res = yices_bvnand(yices_args[0], yices_args[1]);
      break;
    case OP_BV_NEG:
      assert(n_args == 1);
      yices_res = yices_bvneg(yices_args[0]);
      break;
    case OP_BV_NOR:
      assert(n_args == 2);
      yices_res = yices_bvnor(yices_args[0], yices_args[1]);
      break;
    case OP_BV_NOT:
      assert(n_args == 1);
      yices_res = yices_bvnot(yices_args[0]);
      break;

    case OP_BV_OR:
      if (n_args > 3)
      {
        yices_res = yices_bvor(n_args, &yices_args[0]);
      }
      else if (n_args == 3)
      {
        RNGenerator::Choice pick = d_rng.pick_one_of_three();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            yices_res =
                yices_bvor3(yices_args[0], yices_args[1], yices_args[2]);
            break;
          case RNGenerator::Choice::SECOND:
            yices_res = mk_term_pairwise(yices_args, yices_bvor2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_bvor(n_args, &yices_args[0]);
          }
        }
      }
      else
      {
        assert(n_args == 2);
        if (d_rng.flip_coin())
        {
          yices_res = yices_bvor2(yices_args[0], yices_args[1]);
        }
        else
        {
          yices_res = yices_bvor(n_args, &yices_args[0]);
        }
      }
      break;

    case OP_BV_REDAND:
      assert(n_args == 1);
      yices_res = yices_redand(yices_args[0]);
      break;
    case OP_BV_REDOR:
      assert(n_args == 1);
      yices_res = yices_redor(yices_args[0]);
      break;
    case OP_BV_SDIV:
      assert(n_args == 2);
      yices_res = yices_bvsdiv(yices_args[0], yices_args[1]);
      break;
    case OP_BV_SGE:
      assert(n_args == 2);
      yices_res = yices_bvsge_atom(yices_args[0], yices_args[1]);
      break;
    case OP_BV_SGT:
      assert(n_args == 2);
      yices_res = yices_bvsgt_atom(yices_args[0], yices_args[1]);
      break;
    case OP_BV_SHL:
      assert(n_args == 2);
      yices_res = yices_bvshl(yices_args[0], yices_args[1]);
      break;
    case OP_BV_SLE:
      assert(n_args == 2);
      yices_res = yices_bvsle_atom(yices_args[0], yices_args[1]);
      break;
    case OP_BV_SLT:
      assert(n_args == 2);
      yices_res = yices_bvslt_atom(yices_args[0], yices_args[1]);
      break;
    case OP_BV_SMOD:
      assert(n_args == 2);
      yices_res = yices_bvsmod(yices_args[0], yices_args[1]);
      break;
    case OP_BV_SREM:
      assert(n_args == 2);
      yices_res = yices_bvsrem(yices_args[0], yices_args[1]);
      break;
    case OP_BV_SUB:
      assert(n_args == 2);
      yices_res = yices_bvsub(yices_args[0], yices_args[1]);
      break;
    case OP_BV_UDIV:
      assert(n_args == 2);
      yices_res = yices_bvdiv(yices_args[0], yices_args[1]);
      break;
    case OP_BV_UGE:
      assert(n_args == 2);
      yices_res = yices_bvge_atom(yices_args[0], yices_args[1]);
      break;
    case OP_BV_UGT:
      assert(n_args == 2);
      yices_res = yices_bvgt_atom(yices_args[0], yices_args[1]);
      break;
    case OP_BV_ULE:
      assert(n_args == 2);
      yices_res = yices_bvle_atom(yices_args[0], yices_args[1]);
      break;
    case OP_BV_ULT:
      assert(n_args == 2);
      yices_res = yices_bvlt_atom(yices_args[0], yices_args[1]);
      break;
    case OP_BV_UREM:
      assert(n_args == 2);
      yices_res = yices_bvrem(yices_args[0], yices_args[1]);
      break;
    case OP_BV_XNOR:
      assert(n_args == 2);
      yices_res = yices_bvxnor(yices_args[0], yices_args[1]);
      break;

    case OP_BV_XOR:
      if (n_args > 3)
      {
        yices_res = yices_bvor(n_args, &yices_args[0]);
      }
      else if (n_args == 3)
      {
        RNGenerator::Choice pick = d_rng.pick_one_of_three();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
            yices_res =
                yices_bvor3(yices_args[0], yices_args[1], yices_args[2]);
            break;
          case RNGenerator::Choice::SECOND:
            yices_res = mk_term_pairwise(yices_args, yices_bvor2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_bvor(n_args, &yices_args[0]);
          }
        }
      }
      else
      {
        assert(n_args == 2);
        if (d_rng.flip_coin())
        {
          yices_res = yices_bvor2(yices_args[0], yices_args[1]);
        }
        else
        {
          yices_res = yices_bvor(n_args, &yices_args[0]);
        }
      }
      break;

    /* Ints */
    case OP_INT_IS_DIV:
      // TODO
      break;
    case OP_INT_NEG:
      // TODO
      break;
    case OP_INT_SUB:
      // TODO
      break;
    case OP_INT_ADD:
      // TODO
      break;
    case OP_INT_MUL:
      // TODO
      break;
    case OP_INT_DIV:
      // TODO
      break;
    case OP_INT_MOD:
      // TODO
      break;
    case OP_INT_ABS:
      // TODO
      break;
    case OP_INT_LT:
      // TODO
      break;
    case OP_INT_LTE:
      // TODO
      break;
    case OP_INT_GT:
      // TODO
      break;
    case OP_INT_GTE:
      // TODO
      break;

    /* Reals */
    case OP_REAL_NEG:
      // TODO
      break;
    case OP_REAL_SUB:
      // TODO
      break;
    case OP_REAL_ADD:
      // TODO
      break;
    case OP_REAL_MUL:
      // TODO
      break;
    case OP_REAL_DIV:
      // TODO
      break;
    case OP_REAL_LT:
      // TODO
      break;
    case OP_REAL_LTE:
      // TODO
      break;
    case OP_REAL_GT:
      // TODO
      break;
    case OP_REAL_GTE:
      // TODO
      break;

    /* Quantifiers */
    case OP_FORALL:
      // TODO
      break;
    case OP_EXISTS:
      // TODO
      break;

    default: assert(false);
  }
  assert(yices_res >= 0);
}

Sort
YicesSolver::get_sort(Term term, SortKind sort_kind) const
{
  // TODO
}

void
YicesSolver::assert_formula(const Term& t)
{
  if (d_context == nullptr) d_context = yices_new_context(d_config);
  // TODO
}

Solver::Result
YicesSolver::check_sat() const
{
  // TODO
}

Solver::Result
YicesSolver::check_sat_assuming(std::vector<Term>& assumptions) const
{
  // TODO
}

std::vector<Term>
YicesSolver::get_unsat_assumptions() const
{
  // TODO
}

std::vector<Term>
YicesSolver::get_value(std::vector<Term>& terms) const
{
  // TODO
}

void
YicesSolver::push(uint32_t n_levels) const
{
  // TODO
}

void
YicesSolver::pop(uint32_t n_levels) const
{
  // TODO
}

void
YicesSolver::print_model() const
{
  // TODO
}

void
YicesSolver::reset_assertions() const
{
  // TODO
}

/* -------------------------------------------------------------------------- */

term_t
YicesSolver::mk_term_left_assoc(std::vector<term_t>& args,
                                term_t (*fun)(term_t, term_t)) const
{
  assert(args.size() >= 2);
  term_t res, tmp;

  res = fun(args[0], args[1]);
  for (uint32_t i = 2, n_args = args.size(); i < n_args; ++i)
  {
    tmp = fun(res, args[i]);
    assert(tmp >= 0);
    res = tmp;
  }
  assert(res >= 0);
  return res;
}

term_t
YicesSolver::mk_term_pairwise(std::vector<term_t>& args,
                              term_t (*fun)(term_t, term_t)) const
{
  assert(args.size() >= 2);
  term_t res, tmp, old;

  res = 0;
  for (uint32_t i = 0, n_args = args.size(); i < n_args - 1; ++i)
  {
    for (uint32_t j = i + 1; j < n_args; ++j)
    {
      tmp = fun(args[i], args[j]);
      if (res)
      {
        old = res;
        res = yices_and2(old, tmp);
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

std::vector<term_t>
YicesSolver::terms_to_yices_terms(std::vector<Term>& terms) const
{
  std::vector<term_t> res;
  for (Term& t : terms)
  {
    res.push_back(get_yices_term(t));
  }
  return res;
}

/* -------------------------------------------------------------------------- */

void
YicesSolver::configure_fsm(FSM* fsm) const
{
  // TODO
}

/* -------------------------------------------------------------------------- */

}  // namespace yices
}  // namespace smtmbt

#endif
