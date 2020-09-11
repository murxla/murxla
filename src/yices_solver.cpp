#ifdef SMTMBT_USE_YICES

#include "yices_solver.hpp"

#include "config.hpp"
#include "util.hpp"

namespace smtmbt {
namespace yices {

#define SMTMBT_YICES_MAX_DEGREE 10

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
  bool res = yices_type_is_arithmetic(d_sort);
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
  d_config = yices_new_config();
  assert(d_config);
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

void
YicesSolver::reset_sat()
{
  if (d_model)
  {
    yices_free_model(d_model);
    d_model = nullptr;
  }
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
  return true;
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

bool
YicesSolver::is_valid_sort(type_t sort) const
{
  return sort >= 0;
}

bool
YicesSolver::is_valid_term(term_t term) const
{
  return term >= 0;
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
  assert(is_valid_term(yices_term));
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_term));
  assert(res);
  return res;
}

Term
YicesSolver::mk_const(Sort sort, const std::string& name)
{
  term_t yices_term = yices_new_uninterpreted_term(get_yices_sort(sort));
  assert(is_valid_term(yices_term));
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_term));
  assert(res);
  return res;
}

Term
YicesSolver::mk_value(Sort sort, bool value)
{
  term_t yices_term = value ? yices_true() : yices_false();
  assert(is_valid_term(yices_term));
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
    case SORT_REAL:
    {
      assert(sort->get_kind() != SORT_INT || sort->is_int());
      assert(sort->is_real());
      if (value.find('.') == std::string::npos && d_rng.flip_coin())
      {
        RNGenerator::Choice pick = d_rng.pick_one_of_three();
        switch (pick)
        {
          case RNGenerator::Choice::FIRST:
          {
            int32_t val =
                static_cast<int32_t>(strtoul(value.c_str(), nullptr, 10));
            if (val == 0 && d_rng.flip_coin())
            {
              yices_res = yices_zero();
            }
            else
            {
              yices_res = yices_int32(val);
            }
          }
          break;
          case RNGenerator::Choice::SECOND:
          {
            int64_t val =
                static_cast<int64_t>(strtoull(value.c_str(), nullptr, 10));
            if (val == 0 && d_rng.flip_coin())
            {
              yices_res = yices_zero();
            }
            else
            {
              yices_res = yices_int64(val);
            }
          }
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
    }
    break;

    default: assert(false);
  }
  assert(is_valid_term(yices_res));
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
  assert(is_valid_term(yices_res));
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
  assert(is_valid_term(yices_res));
  if (check_bits)
  {
    assert(!str.empty());
    assert(str.size() == bw);
    std::vector<int32_t> expected = bin_str_to_int_array(str);
    std::vector<int32_t> bits(bw);
    // LSB is at index 0
    int32_t r = yices_bv_const_value(yices_res, &bits[0]);
    assert(r >= 0);
    for (size_t i = 0; i < bw; ++i)
    {
      assert(expected[i] == bits[bw - 1 - i]);
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
  assert(is_valid_term(yices_res));
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
  assert(is_valid_sort(yices_res));
  std::shared_ptr<YicesSort> res(new YicesSort(yices_res));
  assert(res);
  return res;
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
  assert(is_valid_sort(yices_res));
  std::shared_ptr<YicesSort> res(new YicesSort(yices_res));
  assert(res);
  return res;
}

Sort
YicesSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  type_t yices_res;
  std::vector<type_t> yices_sorts = sorts_to_yices_sorts(sorts);

  switch (kind)
  {
    case SORT_ARRAY:
    {
      assert(sorts.size() == 2);
      type_t yices_domain = yices_sorts[0];
      type_t yices_range  = yices_sorts[1];
      if (d_rng.flip_coin())
      {
        std::vector<type_t> yices_domain_vector = {yices_domain};
        yices_res =
            yices_function_type(1, yices_domain_vector.data(), yices_range);
      }
      else
      {
        yices_res = yices_function_type1(yices_domain, yices_range);
      }
    }
    break;

    default: assert(false);
  }
  assert(is_valid_sort(yices_res));
  std::shared_ptr<YicesSort> res(new YicesSort(yices_res));
  assert(res);
  return res;
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
//__YICES_DLLSPEC__ extern term_t yices_lambda(uint32_t n, const term_t var[],
// term_t body);
//////

Term
YicesSolver::mk_term(const OpKind& kind,
                     std::vector<Term>& args,
                     std::vector<uint32_t>& params)
{
  term_t yices_res               = -1;
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
        yices_res = yices_distinct(n_args, yices_args.data());
      }
      else
      {
        if (args[0]->get_sort()->is_bv() && d_rng.flip_coin())
        {
          yices_res = mk_term_pairwise(yices_args, yices_bvneq_atom);
        }
        else if (args[0]->get_sort()->is_real() && d_rng.flip_coin())
        {
          // applies to equalities over Int and Real terms
          yices_res = mk_term_pairwise(yices_args, yices_arith_neq_atom);
        }
        else
        {
          yices_res = mk_term_pairwise(yices_args, yices_neq);
        }
      }
      break;

    case OP_EQUAL:
      assert(n_args > 1);
      if (args[0]->get_sort()->is_bv() && d_rng.flip_coin())
      {
        yices_res = mk_term_chained(yices_args, yices_bveq_atom);
      }
      else if (args[0]->get_sort()->is_real() && d_rng.flip_coin())
      {
        // applies to equalities over Int and Real terms
        yices_res = mk_term_chained(yices_args, yices_arith_eq_atom);
      }
      else
      {
        yices_res = mk_term_chained(yices_args, yices_eq);
      }
      break;

    case OP_ITE:
      assert(n_args == 3);
      yices_res = yices_ite(yices_args[0], yices_args[1], yices_args[2]);
      break;

    /* Arrays */
    case OP_ARRAY_SELECT:
      assert(n_args == 2);
      yices_res = yices_application1(yices_args[0], yices_args[1]);
      break;

    case OP_ARRAY_STORE:
      assert(n_args == 3);
      yices_res = yices_update1(yices_args[0], yices_args[1], yices_args[2]);
      break;

    /* Boolean */
    case OP_AND:
      if (n_args > 3)
      {
        yices_res = yices_and(n_args, yices_args.data());
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
            yices_res = mk_term_left_assoc(yices_args, yices_and2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_and(n_args, yices_args.data());
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
          yices_res = yices_and(n_args, yices_args.data());
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
        yices_res = yices_or(n_args, yices_args.data());
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
            yices_res = mk_term_left_assoc(yices_args, yices_or2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_or(n_args, yices_args.data());
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
          yices_res = yices_or(n_args, yices_args.data());
        }
      }
      break;

    case OP_XOR:
      if (n_args > 3)
      {
        yices_res = yices_xor(n_args, yices_args.data());
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
            yices_res = mk_term_left_assoc(yices_args, yices_xor2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_xor(n_args, yices_args.data());
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
          yices_res = yices_xor(n_args, yices_args.data());
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
      assert(n_args > 1);
      if (d_rng.flip_coin())
      {
        yices_res = yices_bvsum(n_args, yices_args.data());
      }
      else
      {
        yices_res = mk_term_left_assoc(yices_args, yices_bvadd);
      }
      break;

    case OP_BV_AND:
      if (n_args > 3)
      {
        yices_res = yices_bvand(n_args, yices_args.data());
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
            yices_res = mk_term_left_assoc(yices_args, yices_bvand2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_bvand(n_args, yices_args.data());
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
          yices_res = yices_bvand(n_args, yices_args.data());
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
        yices_res = yices_bvconcat(n_args, yices_args.data());
      }
      else
      {
        yices_res = mk_term_left_assoc(yices_args, yices_bvconcat2);
      }
      break;
    case OP_BV_LSHR:
      assert(n_args == 2);
      yices_res = yices_bvlshr(yices_args[0], yices_args[1]);
      break;
    case OP_BV_MULT:
      assert(n_args > 1);
      if (d_rng.flip_coin())
      {
        yices_res = yices_bvproduct(n_args, yices_args.data());
      }
      else
      {
        yices_res = mk_term_left_assoc(yices_args, yices_bvmul);
      }
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
        yices_res = yices_bvor(n_args, yices_args.data());
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
            yices_res = mk_term_left_assoc(yices_args, yices_bvor2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_bvor(n_args, yices_args.data());
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
          yices_res = yices_bvor(n_args, yices_args.data());
        }
      }
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
        yices_res = yices_bvor(n_args, yices_args.data());
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
            yices_res = mk_term_left_assoc(yices_args, yices_bvor2);
            break;
          default:
          {
            assert(pick == RNGenerator::Choice::THIRD);
            yices_res = yices_bvor(n_args, yices_args.data());
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
          yices_res = yices_bvor(n_args, yices_args.data());
        }
      }
      break;

    /* Ints, Reals */
    case OP_INT_IS_INT:
    case OP_REAL_IS_INT:
      assert(n_args == 1);
      yices_res = yices_is_int_atom(yices_args[0]);
      break;
    case OP_INT_NEG:
    case OP_REAL_NEG:
      assert(n_args == 1);
      yices_res = yices_neg(yices_args[0]);
      break;
    case OP_INT_SUB:
    case OP_REAL_SUB:
      assert(n_args > 1);
      yices_res = mk_term_left_assoc(yices_args, yices_sub);
      break;
    case OP_INT_ADD:
    case OP_REAL_ADD:
      assert(n_args > 1);
      if (d_rng.flip_coin())
      {
        yices_res = yices_sum(n_args, yices_args.data());
      }
      else
      {
        yices_res = mk_term_left_assoc(yices_args, yices_add);
      }
      break;
    case OP_INT_MUL:
    case OP_REAL_MUL:
      assert(n_args > 1);
      if (d_rng.flip_coin())
      {
        yices_res = yices_product(n_args, yices_args.data());
      }
      else
      {
        yices_res = mk_term_left_assoc(yices_args, yices_mul);
      }
      break;

    /* Ints */
    case OP_INT_IS_DIV:
    {
      assert(n_args == 1);
      assert(n_params == 1);
      std::stringstream ss;
      ss << params[0];
      term_t c = yices_parse_rational(ss.str().c_str());
      assert(is_valid_term(c));
      yices_res = yices_divides_atom(c, yices_args[0]);
    }
      break;
    case OP_INT_DIV:
      assert(n_args > 1);
      yices_res = mk_term_left_assoc(yices_args, yices_idiv);
      break;
    case OP_INT_MOD:
      assert(n_args == 2);
      yices_res = yices_imod(yices_args[0], yices_args[1]);
      break;
    case OP_INT_ABS:
      assert(n_args == 1);
      yices_res = yices_abs(yices_args[0]);
      break;
    case OP_INT_LT:
    case OP_REAL_LT:
      assert(n_args > 1);
      yices_res = mk_term_chained(yices_args, yices_arith_lt_atom);
      break;
    case OP_INT_LTE:
    case OP_REAL_LTE:
      assert(n_args > 1);
      yices_res = mk_term_chained(yices_args, yices_arith_leq_atom);
      break;
    case OP_INT_GT:
    case OP_REAL_GT:
      assert(n_args > 1);
      yices_res = mk_term_chained(yices_args, yices_arith_gt_atom);
      break;
    case OP_INT_GTE:
    case OP_REAL_GTE:
      assert(n_args > 1);
      yices_res = mk_term_chained(yices_args, yices_arith_geq_atom);
      break;

    /* Reals */
    case OP_REAL_DIV:
      assert(n_args > 1);
      yices_res = mk_term_left_assoc(yices_args, yices_division);
      break;

    /* Quantifiers */
    case OP_FORALL:
    case OP_EXISTS:
    {
      uint32_t n = yices_args.size() - 1;
      for (uint32_t i = 0; i < n; ++i)
      {
        vars.push_back(yices_args[i]);
      }
      if (kind == OP_EXISTS)
      {
        yices_res = yices_exists(n, vars.data(), yices_args.back());
      }
      else
      {
        yices_res = yices_forall(n, vars.data(), yices_args.back());
      }
    }
    break;

    /* Solver-specific operators */
    default:
      // BV
      if (kind == d_op_redand)
      {
        assert(n_args == 1);
        yices_res = yices_redand(yices_args[0]);
      }
      else if (kind == d_op_redor)
      {
        assert(n_args == 1);
        yices_res = yices_redor(yices_args[0]);
      }
      else if (kind == d_op_bvsquare)
      {
        assert(n_args == 1);
        yices_res = yices_bvsquare(yices_args[0]);
      }
      else if (kind == d_op_bvpower)
      {
        assert(n_args == 1);
        assert(n_params == 1);
        yices_res = yices_bvpower(
            yices_args[0],
            uint32_to_value_in_range(
                params[0], 0, args[0]->get_sort()->get_bv_size()));
      }
      else if (kind == d_op_shift_left0)
      {
        assert(n_args == 1);
        assert(n_params == 1);
        yices_res = yices_shift_left0(
            yices_args[0],
            uint32_to_value_in_range(
                params[0], 0, args[0]->get_sort()->get_bv_size()));
      }
      else if (kind == d_op_shift_left1)
      {
        assert(n_args == 1);
        assert(n_params == 1);
        yices_res = yices_shift_left1(
            yices_args[0],
            uint32_to_value_in_range(
                params[0], 0, args[0]->get_sort()->get_bv_size()));
      }
      else if (kind == d_op_shift_right0)
      {
        assert(n_args == 1);
        assert(n_params == 1);
        yices_res = yices_shift_right0(
            yices_args[0],
            uint32_to_value_in_range(
                params[0], 0, args[0]->get_sort()->get_bv_size()));
      }
      else if (kind == d_op_shift_right1)
      {
        assert(n_args == 1);
        assert(n_params == 1);
        yices_res = yices_shift_right1(
            yices_args[0],
            uint32_to_value_in_range(
                params[0], 0, args[0]->get_sort()->get_bv_size()));
      }
      else if (kind == d_op_ashift_right)
      {
        assert(n_args == 1);
        assert(n_params == 1);
        yices_res = yices_ashift_right(
            yices_args[0],
            uint32_to_value_in_range(
                params[0], 0, args[0]->get_sort()->get_bv_size()));
      }
      else if (kind == d_op_bitextract)
      {
        assert(n_args == 1);
        assert(n_params == 1);
        yices_res = yices_bitextract(
            yices_args[0],
            uint32_to_value_in_range(
                params[0], 0, args[0]->get_sort()->get_bv_size() - 1));
      }
      else if (kind == d_op_bvarray)
      {
        assert(n_args > 0);
        yices_res = yices_bvarray(n_args, yices_args.data());
      }
      // Arithmetic
      else if (kind == d_op_int_eq0 || kind == d_op_real_eq0)
      {
        assert(n_args == 1);
        yices_res = yices_arith_eq0_atom(yices_args[0]);
      }
      else if (kind == d_op_int_neq0 || kind == d_op_real_neq0)
      {
        assert(n_args == 1);
        yices_res = yices_arith_neq0_atom(yices_args[0]);
      }
      else if (kind == d_op_int_geq0 || kind == d_op_real_geq0)
      {
        assert(n_args == 1);
        yices_res = yices_arith_geq0_atom(yices_args[0]);
      }
      else if (kind == d_op_int_leq0 || kind == d_op_real_leq0)
      {
        assert(n_args == 1);
        yices_res = yices_arith_leq0_atom(yices_args[0]);
      }
      else if (kind == d_op_int_gt0 || kind == d_op_real_gt0)
      {
        assert(n_args == 1);
        yices_res = yices_arith_gt0_atom(yices_args[0]);
      }
      else if (kind == d_op_int_lt0 || kind == d_op_real_lt0)
      {
        assert(n_args == 1);
        yices_res = yices_arith_lt0_atom(yices_args[0]);
      }
      else if (kind == d_op_int_power || kind == d_op_real_power)
      {
        assert(n_args == 1);
        assert(n_params == 1);
        yices_res = yices_power(
            yices_args[0],
            uint32_to_value_in_range(params[0], 0, SMTMBT_YICES_MAX_DEGREE));
      }
      else if (kind == d_op_int_square || kind == d_op_real_square)
      {
        assert(n_args == 1);
        yices_res = yices_square(yices_args[0]);
      }
      else if (kind == d_op_int_ceil || kind == d_op_real_ceil)
      {
        assert(n_args == 1);
        yices_res = yices_ceil(yices_args[0]);
      }
      else if (kind == d_op_int_floor || kind == d_op_real_floor)
      {
        assert(n_args == 1);
        yices_res = yices_floor(yices_args[0]);
      }
      else if (kind == d_op_int_poly || kind == d_op_real_poly)
      {
        assert(n_args > 0);
        if (d_rng.flip_coin())
        {
          std::vector<int32_t> a;
          for (uint32_t i = 0; i < n_args; ++i)
          {
            a.push_back(d_rng.pick<int32_t>());
          }
          yices_res = yices_poly_int32(n_args, a.data(), yices_args.data());
        }
        else
        {
          std::vector<int64_t> a;
          for (uint32_t i = 0; i < n_args; ++i)
          {
            a.push_back(d_rng.pick<int64_t>());
          }
          yices_res = yices_poly_int64(n_args, a.data(), yices_args.data());
        }
      }
      else if (kind == d_op_real_rpoly)
      {
        assert(n_args > 0);
        if (d_rng.flip_coin())
        {
          std::vector<int32_t> num;
          std::vector<uint32_t> den;
          for (uint32_t i = 0; i < n_args; ++i)
          {
            num.push_back(d_rng.pick<int32_t>(INT32_MIN, INT32_MAX));
            den.push_back(d_rng.pick<uint32_t>());
          }
          yices_res = yices_poly_rational32(
              n_args, num.data(), den.data(), yices_args.data());
        }
        else
        {
          std::vector<int64_t> num;
          std::vector<uint64_t> den;
          for (uint32_t i = 0; i < n_args; ++i)
          {
            num.push_back(d_rng.pick<int64_t>(INT64_MIN, INT64_MAX));
            den.push_back(d_rng.pick<uint64_t>());
          }
          yices_res = yices_poly_rational64(
              n_args, num.data(), den.data(), yices_args.data());
        }
      }
      // catch all
      else
      {
        assert(false);
      }
  }
  assert(is_valid_term(yices_res));
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_res));
  assert(res);
  return res;
}

Sort
YicesSolver::get_sort(Term term, SortKind sort_kind) const
{
  (void) sort_kind;
  return std::shared_ptr<YicesSort>(
      new YicesSort(yices_type_of_term(get_yices_term(term))));
}

void
YicesSolver::assert_formula(const Term& t)
{
  if (!d_context) d_context = yices_new_context(d_config);
  yices_assert_formula(d_context, get_yices_term(t));
}

Solver::Result
YicesSolver::check_sat()
{
  if (!d_context) d_context = yices_new_context(d_config);
  // TODO parameters?
  smt_status_t res = yices_check_context(d_context, nullptr);
  if (res == STATUS_SAT) return Result::SAT;
  if (res == STATUS_UNSAT) return Result::UNSAT;
  return Result::UNKNOWN;
}

Solver::Result
YicesSolver::check_sat_assuming(std::vector<Term>& assumptions)
{
  if (!d_context) d_context = yices_new_context(d_config);
  // TODO parameters?
  std::vector<term_t> yices_assumptions = terms_to_yices_terms(assumptions);
  smt_status_t res                      = yices_check_context_with_assumptions(
      d_context, nullptr, yices_assumptions.size(), yices_assumptions.data());
  if (res == STATUS_SAT) return Result::SAT;
  if (res == STATUS_UNSAT) return Result::UNSAT;
  return Result::UNKNOWN;
}

std::vector<Term>
YicesSolver::get_unsat_assumptions()
{
  if (!d_context) d_context = yices_new_context(d_config);
  term_vector_t yices_res;
  yices_init_term_vector(&yices_res);
  int32_t status = yices_get_unsat_core(d_context, &yices_res);
  assert(status == 0);
  return yices_terms_to_terms(&yices_res);
}

std::vector<Term>
YicesSolver::get_value(std::vector<Term>& terms)
{
  if (!d_context) d_context = yices_new_context(d_config);

  std::vector<Term> res;
  std::vector<term_t> yices_res;
  std::vector<term_t> yices_terms = terms_to_yices_terms(terms);

  if (!d_model)
  {
    d_model = yices_get_model(d_context, 1);
    assert(d_model);
  }
  for (term_t t : yices_terms)
  {
    term_t v = yices_get_value_as_term(d_model, t);
    assert(is_valid_term(v));
    yices_res.push_back(v);
  }
  res = yices_terms_to_terms(yices_res);
  return res;
}

void
YicesSolver::push(uint32_t n_levels)
{
  if (!d_context) d_context = yices_new_context(d_config);
  for (uint32_t i = 0; i < n_levels; ++i)
  {
    yices_push(d_context);
  }
}

void
YicesSolver::pop(uint32_t n_levels)
{
  if (!d_context) d_context = yices_new_context(d_config);
  for (uint32_t i = 0; i < n_levels; ++i)
  {
    yices_pop(d_context);
  }
}

void
YicesSolver::print_model()
{
  if (!d_context) d_context = yices_new_context(d_config);
  if (!d_model)
  {
    d_model = yices_get_model(d_context, 1);
    assert(d_model);
  }
}

void
YicesSolver::reset_assertions()
{
  if (d_context) yices_reset_context(d_context);
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
    assert(is_valid_term(tmp));
    res = tmp;
  }
  assert(is_valid_term(res));
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

term_t
YicesSolver::mk_term_chained(std::vector<term_t>& args,
                             term_t (*fun)(term_t, term_t)) const
{
  assert(args.size() >= 2);
  term_t res, tmp, old;

  res = 0;
  for (uint32_t i = 0, j = 1, n_args = args.size(); j < n_args; ++i, ++j)
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
  assert(res);
  return res;
}

std::vector<type_t>
YicesSolver::sorts_to_yices_sorts(const std::vector<Sort>& sorts) const
{
  std::vector<type_t> res;
  for (const Sort& s : sorts)
  {
    res.push_back(get_yices_sort(s));
  }
  return res;
}

std::vector<Term>
YicesSolver::yices_terms_to_terms(term_vector_t* terms) const
{
  std::vector<Term> res;
  for (uint32_t i = 0; i < terms->size; ++i)
  {
    res.push_back(std::shared_ptr<YicesTerm>(new YicesTerm(terms->data[i])));
  }
  return res;
}

std::vector<Term>
YicesSolver::yices_terms_to_terms(std::vector<term_t>& terms) const
{
  std::vector<Term> res;
  for (term_t t : terms)
  {
    res.push_back(std::shared_ptr<YicesTerm>(new YicesTerm(t)));
  }
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
/* Solver-specific operators, SolverManager configuration.                    */
/* -------------------------------------------------------------------------- */

void
YicesSolver::configure_smgr(SolverManager* smgr) const
{
  OpKindSet ops = get_supported_op_kinds();

  /* BV */
  update_op_kinds_to_str(d_op_bvsquare, "yices-OP_BVSQUARE");
  smgr->add_op_kind(ops, d_op_bvsquare, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  update_op_kinds_to_str(d_op_bvpower, "yices-OP_BVPOWER");
  smgr->add_op_kind(ops, d_op_bvpower, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);

  update_op_kinds_to_str(d_op_redand, "yices-OP_REDAND");
  smgr->add_op_kind(ops, d_op_redand, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  update_op_kinds_to_str(d_op_redor, "yices-OP_REDOR");
  smgr->add_op_kind(ops, d_op_redor, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  update_op_kinds_to_str(d_op_shift_left0, "yices-OP_SHIFT_LEFT0");
  smgr->add_op_kind(ops, d_op_shift_left0, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  update_op_kinds_to_str(d_op_shift_left1, "yices-OP_SHIFT_LEFT1");
  smgr->add_op_kind(ops, d_op_shift_left1, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  update_op_kinds_to_str(d_op_shift_right0, "yices-OP_SHIFT_RIGHT0");
  smgr->add_op_kind(
      ops, d_op_shift_right0, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  update_op_kinds_to_str(d_op_shift_right1, "yices-OP_SHIFT_RIGHT1");
  smgr->add_op_kind(
      ops, d_op_shift_right1, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  update_op_kinds_to_str(d_op_ashift_right, "yices-OP_ASHIFT_RIGHT");
  smgr->add_op_kind(
      ops, d_op_ashift_right, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);

  update_op_kinds_to_str(d_op_bitextract, "yices-OP_BITEXTRACT");
  smgr->add_op_kind(
      ops, d_op_bitextract, 1, 1, SORT_BOOL, {SORT_BV}, THEORY_BV);

  update_op_kinds_to_str(d_op_bvarray, "yices-OP_BVARRAY");
  smgr->add_op_kind(ops,
                    d_op_bvarray,
                    SMTMBT_MK_TERM_N_ARGS,
                    0,
                    SORT_BV,
                    {SORT_BOOL},
                    THEORY_BV);

  /* Ints */
  update_op_kinds_to_str(d_op_int_eq0, "yices-OP_INT_EQ0");
  smgr->add_op_kind(ops, d_op_int_eq0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  update_op_kinds_to_str(d_op_int_neq0, "yices-OP_INT_NEQ0");
  smgr->add_op_kind(
      ops, d_op_int_neq0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  update_op_kinds_to_str(d_op_int_geq0, "yices-OP_INT_GEQ0");
  smgr->add_op_kind(
      ops, d_op_int_geq0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  update_op_kinds_to_str(d_op_int_gt0, "yices-OP_INT_GT0");
  smgr->add_op_kind(ops, d_op_int_gt0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  update_op_kinds_to_str(d_op_int_leq0, "yices-OP_INT_LEQ0");
  smgr->add_op_kind(
      ops, d_op_int_leq0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  update_op_kinds_to_str(d_op_int_lt0, "yices-OP_INT_LT0");
  smgr->add_op_kind(ops, d_op_int_lt0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  update_op_kinds_to_str(d_op_int_power, "yices-OP_INT_POWER");
  smgr->add_op_kind(
      ops, d_op_int_power, 1, 1, SORT_INT, {SORT_INT}, THEORY_INT);
  update_op_kinds_to_str(d_op_int_square, "yices-OP_INT_SQUARE");
  smgr->add_op_kind(
      ops, d_op_int_square, 1, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  update_op_kinds_to_str(d_op_int_ceil, "yices-OP_INT_CEIL");
  smgr->add_op_kind(ops, d_op_int_ceil, 1, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  update_op_kinds_to_str(d_op_int_floor, "yices-OP_INT_FLOOR");
  smgr->add_op_kind(
      ops, d_op_int_floor, 1, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  update_op_kinds_to_str(d_op_int_poly, "yices-OP_INT_POLY");
  smgr->add_op_kind(ops,
                    d_op_int_poly,
                    SMTMBT_MK_TERM_N_ARGS,
                    0,
                    SORT_INT,
                    {SORT_INT},
                    THEORY_INT);
  /* Reals */
  update_op_kinds_to_str(d_op_real_eq0, "yices-OP_REAL_EQ0");
  smgr->add_op_kind(
      ops, d_op_real_eq0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  update_op_kinds_to_str(d_op_real_neq0, "yices-OP_REAL_NEQ0");
  smgr->add_op_kind(
      ops, d_op_real_neq0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  update_op_kinds_to_str(d_op_real_geq0, "yices-OP_REAL_GEQ0");
  smgr->add_op_kind(
      ops, d_op_real_geq0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  update_op_kinds_to_str(d_op_real_gt0, "yices-OP_REAL_GT0");
  smgr->add_op_kind(
      ops, d_op_real_gt0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  update_op_kinds_to_str(d_op_real_leq0, "yices-OP_REAL_LEQ0");
  smgr->add_op_kind(
      ops, d_op_real_leq0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  update_op_kinds_to_str(d_op_real_lt0, "yices-OP_REAL_LT0");
  smgr->add_op_kind(
      ops, d_op_real_lt0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  update_op_kinds_to_str(d_op_real_power, "yices-OP_REAL_POWER");
  smgr->add_op_kind(
      ops, d_op_real_power, 1, 1, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  update_op_kinds_to_str(d_op_real_square, "yices-OP_REAL_SQUARE");
  smgr->add_op_kind(
      ops, d_op_real_square, 1, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  update_op_kinds_to_str(d_op_real_ceil, "yices-OP_REAL_CEIL");
  smgr->add_op_kind(
      ops, d_op_real_ceil, 1, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  update_op_kinds_to_str(d_op_real_floor, "yices-OP_REAL_FLOOR");
  smgr->add_op_kind(
      ops, d_op_real_floor, 1, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  update_op_kinds_to_str(d_op_real_poly, "yices-OP_REAL_POLY");
  smgr->add_op_kind(ops,
                    d_op_real_poly,
                    SMTMBT_MK_TERM_N_ARGS,
                    0,
                    SORT_REAL,
                    {SORT_REAL},
                    THEORY_REAL);
  update_op_kinds_to_str(d_op_real_rpoly, "yices-OP_REAL_RPOLY");
  smgr->add_op_kind(ops,
                    d_op_real_rpoly,
                    SMTMBT_MK_TERM_N_ARGS,
                    0,
                    SORT_REAL,
                    {SORT_REAL},
                    THEORY_REAL);
}

/* -------------------------------------------------------------------------- */
/* Solver-specific actions, FSM configuration.                                */
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
