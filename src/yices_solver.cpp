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
YicesSort::is_rm() const
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
  return {};
}

void
YicesSolver::configure_fsm(FSM* fsm) const
{
  // TODO
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
        if (d_rng.flip_coin())
        {
          yices_res = yices_int32(
              static_cast<int32_t>(strtoul(value.c_str(), nullptr, 10)));
        }
        else
        {
          yices_res = yices_int64(
              static_cast<int64_t>(strtoull(value.c_str(), nullptr, 10)));
        }
      }
      else
      {
        yices_res = yices_parse_rational(value.c_str());
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
  return std::shared_ptr<YicesSort>(new YicesSort(yices_res));
}

Sort
YicesSolver::mk_sort(SortKind kind, uint32_t size)
{
  // TODO
}

Sort
YicesSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  // TODO
}

Term
YicesSolver::mk_term(const OpKind& kind,
                     std::vector<Term>& args,
                     std::vector<uint32_t>& params)
{
  // TODO
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

}  // namespace yices
}  // namespace smtmbt

#endif
