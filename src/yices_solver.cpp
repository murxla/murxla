#ifdef MURXLA_USE_YICES

#include "yices_solver.hpp"

#include "config.hpp"

namespace murxla {
namespace yices {

#define MURXLA_YICES_MAX_DEGREE 10

/* -------------------------------------------------------------------------- */
/* YicesSort                                                                  */
/* -------------------------------------------------------------------------- */

type_t
YicesSort::get_yices_sort(Sort sort)
{
  YicesSort* yices_sort = dynamic_cast<YicesSort*>(sort.get());
  assert(yices_sort);
  return yices_sort->d_sort;
}

std::vector<type_t>
YicesSort::sorts_to_yices_sorts(const std::vector<Sort>& sorts)
{
  std::vector<type_t> res;
  for (const Sort& s : sorts)
  {
    res.push_back(YicesSort::get_yices_sort(s));
  }
  return res;
}

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

std::string
YicesSort::to_string() const
{
  char* s = yices_type_to_string(d_sort, 80, 80, 0);
  std::string res(s);
  yices_free_string(s);
  return res;
}

bool
YicesSort::is_array() const
{
  return yices_type_is_function(d_sort) && yices_type_num_children(d_sort) == 2;
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
YicesSort::is_fun() const
{
  return yices_type_is_function(d_sort);
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
  assert(!res || yices_type_is_int(d_sort) || yices_type_is_real(d_sort));
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
/* YicesTerm                                                                  */
/* -------------------------------------------------------------------------- */

term_t
YicesTerm::get_yices_term(Term term)
{
  YicesTerm* yices_term = dynamic_cast<YicesTerm*>(term.get());
  assert(yices_term);
  return yices_term->d_term;
}

std::vector<Term>
YicesTerm::yices_terms_to_terms(term_vector_t* terms)
{
  std::vector<Term> res;
  for (uint32_t i = 0; i < terms->size; ++i)
  {
    res.push_back(std::shared_ptr<YicesTerm>(new YicesTerm(terms->data[i])));
  }
  return res;
}

std::vector<Term>
YicesTerm::yices_terms_to_terms(const std::vector<term_t>& terms)
{
  std::vector<Term> res;
  for (term_t t : terms)
  {
    res.push_back(std::shared_ptr<YicesTerm>(new YicesTerm(t)));
  }
  return res;
}

std::vector<term_t>
YicesTerm::terms_to_yices_terms(const std::vector<Term>& terms)
{
  std::vector<term_t> res;
  for (auto& t : terms)
  {
    res.push_back(YicesTerm::get_yices_term(t));
  }
  return res;
}

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

std::string
YicesTerm::to_string() const
{
  char* s = yices_term_to_string(d_term, 80, 80, 0);
  std::string res(s);
  yices_free_string(s);
  return res;
}

bool
YicesTerm::is_array() const
{
  return yices_term_is_function(d_term) && get_sort()->is_array();
}

bool
YicesTerm::is_bool() const
{
  return yices_term_is_bool(d_term);
}

bool
YicesTerm::is_bv() const
{
  return yices_term_is_bitvector(d_term);
}

bool
YicesTerm::is_fp() const
{
  return false;
}

bool
YicesTerm::is_fun() const
{
  return yices_term_is_function(d_term);
}

bool
YicesTerm::is_int() const
{
  bool res = yices_term_is_int(d_term);
  assert(!res || yices_term_is_arithmetic(d_term));
  return res;
}

bool
YicesTerm::is_real() const
{
  bool res = yices_term_is_arithmetic(d_term);
  assert(!res || yices_term_is_int(d_term) || yices_term_is_real(d_term));
  return res;
}

bool
YicesTerm::is_reglan() const
{
  return false;
}

bool
YicesTerm::is_rm() const
{
  return false;
}

bool
YicesTerm::is_string() const
{
  return false;
}

uint32_t
YicesTerm::get_bv_size() const
{
  assert(is_bv());
  type_t yices_type = yices_type_of_term(d_term);
  uint32_t res      = yices_bvtype_size(yices_type);
  assert(res);
  return res;
}

/* -------------------------------------------------------------------------- */
/* YicesSolver                                                                */
/* -------------------------------------------------------------------------- */

YicesSolver::~YicesSolver()
{
  if (d_context)
  {
    yices_free_context(d_context);
    d_context = nullptr;
  }
  if (d_model)
  {
    yices_free_model(d_model);
    d_model = nullptr;
  }
  if (d_config)
  {
    yices_free_config(d_config);
    d_config = nullptr;
    yices_exit();
  }
}

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
  if (d_context)
  {
    yices_free_context(d_context);
    d_context = nullptr;
  }
  if (d_model)
  {
    yices_free_model(d_model);
    d_model = nullptr;
  }
  yices_free_config(d_config);
  d_config = nullptr;
  yices_exit();
}

bool
YicesSolver::is_initialized() const
{
  return d_is_initialized;
}

const std::string
YicesSolver::get_name() const
{
  return "Yices";
}

TheoryIdVector
YicesSolver::get_supported_theories() const
{
  return {
      THEORY_ARRAY, THEORY_BV, THEORY_BOOL, THEORY_INT, THEORY_REAL, THEORY_UF};
}

SortKindSet
YicesSolver::get_unsupported_array_index_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
}

SortKindSet
YicesSolver::get_unsupported_array_element_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
}

SortKindSet
YicesSolver::get_unsupported_fun_domain_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
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
  if (opt == "produce-models" || opt == "produce-unsat-assumptions"
      || opt == "produce-unsat-cores")
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
YicesSolver::is_unsat_assumption(const Term& t) const
{
  assert(is_valid_term(YicesTerm::get_yices_term(t)));
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

std::string
YicesSolver::get_option_name_unsat_cores() const
{
  /* always enabled in Yices, can not be configured via set_opt */
  return "produce-unsat-cores";
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
YicesSolver::option_unsat_cores_enabled() const
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

bool
YicesSolver::check_bits(uint32_t bw, term_t term, std::string& expected) const
{
  assert(!expected.empty());
  assert(expected.size() == bw);
  std::vector<int32_t> exp = bin_str_to_int_array(expected);
  std::vector<int32_t> bits(bw);
  // LSB is at index 0
  int32_t r = yices_bv_const_value(term, &bits[0]);
  if (r < 0) return false;
  for (size_t i = 0; i < bw; ++i)
  {
    if (exp[i] != bits[bw - 1 - i]) return false;
  }
  return true;
}

Term
YicesSolver::mk_var(Sort sort, const std::string& name)
{
  term_t yices_term = yices_new_variable(YicesSort::get_yices_sort(sort));
  assert(is_valid_term(yices_term));
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_term));
  assert(res);
  return res;
}

Term
YicesSolver::mk_const(Sort sort, const std::string& name)
{
  term_t yices_term =
      yices_new_uninterpreted_term(YicesSort::get_yices_sort(sort));
  assert(is_valid_term(yices_term));
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_term));
  assert(res);
  return res;
}

Term
YicesSolver::mk_value(Sort sort, bool value)
{
  MURXLA_CHECK_CONFIG(sort->is_bool())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to YicesSolver::mk_value, expected Boolean sort";

  term_t yices_term = value ? yices_true() : yices_false();
  assert(is_valid_term(yices_term));
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_term));
  assert(res);
  return res;
}

Term
YicesSolver::mk_value(Sort sort, std::string value)
{
  term_t yices_res = -1;

  switch (sort->get_kind())
  {
    case SORT_INT:
    case SORT_REAL:
    {
      assert(sort->get_kind() != SORT_INT || sort->is_int());
      assert(sort->is_real());
      if (value.find('.') == std::string::npos && d_rng.flip_coin())
      {
        int32_t val32 = 0;
        int64_t val64 = 0;
        bool fits32 = true, fits64 = true;
        try
        {
          val32 = std::stoi(value);
        }
        catch (std::out_of_range& e)
        {
          fits32 = false;
        }
        try
        {
          val64 = std::stoll(value);
        }
        catch (std::out_of_range& e)
        {
          fits64 = false;
        }

        if (fits32 && val32 == 0 && d_rng.flip_coin())
        {
          yices_res = yices_zero();
        }
        else
        {
          if (fits32 && d_rng.flip_coin())
          {
            assert(fits64);
            if (d_rng.flip_coin())
            {
              yices_res = yices_int32(val32);
            }
            else
            {
              yices_res = yices_int64(val64);
            }
          }
          else
          {
            if (fits64 && d_rng.flip_coin())
            {
              yices_res = yices_int64(val64);
            }
            else
            {
              yices_res = yices_parse_rational(value.c_str());
            }
          }
        }
      }
      else
      {
        yices_res = yices_parse_float(value.c_str());
      }
    }
    break;

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unexpected sort of kind '" << sort->get_kind()
          << "' as argument to YicesSolver::mk_value, expected Integer or Real "
             "sort";
  }
  assert(is_valid_term(yices_res));
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_res));
  assert(res);
  return res;
}

Term
YicesSolver::mk_value(Sort sort, std::string num, std::string den)
{
  MURXLA_CHECK_CONFIG(sort->is_real())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to YicesSolver::mk_value, expected Real "
         "sort";

  term_t yices_res;

  int32_t num32 = 0, den32 = 0;
  int64_t num64 = 0, den64 = 0;
  bool nfits32 = true, dfits32 = true, nfits64 = true, dfits64 = true;
  try
  {
    num32 = std::stoi(num);
  }
  catch (std::out_of_range& e)
  {
    nfits32 = false;
  }
  try
  {
    num64 = std::stoll(num);
  }
  catch (std::out_of_range& e)
  {
    nfits64 = false;
  }
  try
  {
    den32 = std::stoi(den);
  }
  catch (std::out_of_range& e)
  {
    dfits32 = false;
  }
  try
  {
    den64 = std::stoll(den);
  }
  catch (std::out_of_range& e)
  {
    dfits64 = false;
  }
  assert(nfits64 && dfits64);

  if (nfits32 && dfits32 && d_rng.flip_coin())
  {
    yices_res = yices_rational32(num32, den32);
  }
  else
  {
    yices_res = yices_rational64(num64, den64);
  }
  assert(is_valid_term(yices_res));
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_res));
  assert(res);
  return res;
}

std::vector<int32_t>
YicesSolver::bin_str_to_int_array(std::string s) const
{
  std::vector<int32_t> res;
  for (char c : s)
  {
    assert(c == '0' || c == '1');
    res.push_back(c == '0' ? 0 : 1);
  }
  return res;
}

Term
YicesSolver::mk_value(Sort sort, std::string value, Base base)
{
  assert(sort->is_bv());

  term_t yices_res;
  int32_t ibase;
  uint32_t val32 = 0;
  uint64_t val64 = 0;
  uint32_t bw    = sort->get_bv_size();
  bool fits32 = true, fits64 = true;
  bool chkbits = bw <= 64 && d_rng.pick_with_prob(10);
  std::string str;

  if (base == DEC)
  {
    ibase = 10;
  }
  else if (base == HEX)
  {
    ibase = 16;
  }
  else
  {
    assert(base == BIN);
    ibase = 2;
  }

  try
  {
    uint64_t tmp = std::stoul(value, nullptr, ibase);
    if (tmp > UINT64_MAX)
    {
      fits32 = false;
    }
    else
    {
      val32 = tmp;
    }
  }
  catch (std::out_of_range& e)
  {
    fits32 = false;
  }

  try
  {
    val64 = std::stoull(value, nullptr, ibase);
  }
  catch (std::out_of_range& e)
  {
    fits64 = false;
  }
  bool use_int = d_rng.flip_coin();
  if (fits32 && d_rng.flip_coin())
  {
    if (use_int)
    {
      yices_res = yices_bvconst_int32(bw, static_cast<int32_t>(val32));
      if (chkbits)
      {
        str = std::bitset<64>(static_cast<int32_t>(val32))
                  .to_string()
                  .substr(64 - bw, bw);
      }
    }
    else
    {
      yices_res = yices_bvconst_uint32(bw, val32);
      if (chkbits)
      {
        str = std::bitset<64>(val32).to_string().substr(64 - bw, bw);
      }
    }
    assert(is_valid_term(yices_res));
    assert(!chkbits || check_bits(bw, yices_res, str));
  }
  else if (fits64 && d_rng.flip_coin())
  {
    if (use_int)
    {
      yices_res = yices_bvconst_int64(bw, static_cast<int64_t>(val64));
      if (chkbits)
      {
        str = std::bitset<64>(static_cast<int64_t>(val64))
                  .to_string()
                  .substr(64 - bw, bw);
      }
    }
    else
    {
      yices_res = yices_bvconst_uint64(bw, val64);
      if (chkbits)
      {
        str = std::bitset<64>(val64).to_string().substr(64 - bw, bw);
      }
    }
    assert(is_valid_term(yices_res));
    assert(!chkbits || check_bits(bw, yices_res, str));
  }
  else
  {
    if (base == DEC)
    {
      std::string value_bin = str_dec_to_bin(value);
      if (value_bin.size() < bw)
      {
        std::stringstream ss;
        ss << std::string(bw - value_bin.size(), '0') << value_bin;
        assert(ss.str().size() == bw);
        value_bin = ss.str();
      }
      yices_res = yices_parse_bvbin(value_bin.c_str());
    }
    else if (base == HEX)
    {
      yices_res = yices_parse_bvhex(value.c_str());
    }
    else
    {
      if (d_rng.flip_coin())
      {
        yices_res = yices_parse_bvbin(value.c_str());
      }
      else
      {
        std::vector<int32_t> a = bin_str_to_int_array(value);
        yices_res              = yices_bvconst_from_array(bw, &a[0]);
      }
    }
    assert(is_valid_term(yices_res));
  }
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_res));
  assert(res);
  return res;
}

Term
YicesSolver::mk_special_value(Sort sort, const SpecialValueKind& value)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to YicesSolver::mk_special_value, expected bit-vector "
         "sort";

  term_t yices_res;
  uint32_t bw  = sort->get_bv_size();
  bool chkbits = bw <= 64 && d_rng.pick_with_prob(10);
  std::string str;

  if (value == SPECIAL_VALUE_BV_ZERO)
  {
    yices_res = yices_bvconst_zero(bw);
    if (chkbits)
    {
      str = bv_special_value_zero_str(bw);
    }
  }
  else if (value == SPECIAL_VALUE_BV_ONE)
  {
    yices_res = yices_bvconst_one(bw);
    if (chkbits)
    {
      str = bv_special_value_one_str(bw);
    }
  }
  else if (value == SPECIAL_VALUE_BV_ONES)
  {
    yices_res = yices_bvconst_minus_one(bw);
    if (chkbits) str = bv_special_value_ones_str(bw);
  }
  else if (value == SPECIAL_VALUE_BV_MIN_SIGNED)
  {
    yices_res = yices_parse_bvbin(bv_special_value_min_signed_str(bw).c_str());
    if (chkbits) str = bv_special_value_min_signed_str(bw);
  }
  else
  {
    assert(value == SPECIAL_VALUE_BV_MAX_SIGNED);
    yices_res = yices_parse_bvbin(bv_special_value_max_signed_str(bw).c_str());
    if (chkbits) str = bv_special_value_max_signed_str(bw);
  }
  assert(is_valid_term(yices_res));
  assert(!chkbits || check_bits(bw, yices_res, str));
  std::shared_ptr<YicesTerm> res(new YicesTerm(yices_res));
  assert(res);
  return res;
}

Sort
YicesSolver::mk_sort(SortKind kind)
{
  type_t yices_res = -1;
  switch (kind)
  {
    case SORT_BOOL: yices_res = yices_bool_type(); break;
    case SORT_INT: yices_res = yices_int_type(); break;
    case SORT_REAL: yices_res = yices_real_type(); break;

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unsupported sort kind '" << kind
          << "' as argument to YicesSolver::mk_sort, expected '" << SORT_BOOL
          << "', '" << SORT_INT << "', '" << SORT_REAL << "'";
  }
  assert(is_valid_sort(yices_res));
  std::shared_ptr<YicesSort> res(new YicesSort(yices_res));
  assert(res);
  return res;
}

Sort
YicesSolver::mk_sort(SortKind kind, uint32_t size)
{
  MURXLA_CHECK_CONFIG(kind == SORT_BV)
      << "unsupported sort kind '" << kind
      << "' as argument to YicesSolver::mk_sort, expected '" << SORT_BV << "'";

  type_t yices_res = yices_bv_type(size);
  assert(is_valid_sort(yices_res));
  std::shared_ptr<YicesSort> res(new YicesSort(yices_res));
  assert(res);
  return res;
}

Sort
YicesSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  type_t yices_res                = -1;
  std::vector<type_t> yices_sorts = YicesSort::sorts_to_yices_sorts(sorts);

  switch (kind)
  {
    case SORT_FUN:
    case SORT_ARRAY:
    {
      assert(kind != SORT_ARRAY || sorts.size() == 2);
      type_t yices_range = yices_sorts.back();
      yices_sorts.pop_back();
      if (d_rng.flip_coin() || kind != SORT_ARRAY)
      {
        yices_res = yices_function_type(
            yices_sorts.size(), yices_sorts.data(), yices_range);
      }
      else
      {
        yices_res = yices_function_type1(yices_sorts[0], yices_range);
      }
    }
    break;

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unsupported sort kind '" << kind
          << "' as argument to YicesSolver::mk_sort, expected '" << SORT_ARRAY
          << "' or '" << SORT_FUN << "'";
  }
  assert(is_valid_sort(yices_res));
  std::shared_ptr<YicesSort> res(new YicesSort(yices_res));
  assert(res);
  return res;
}

//////
////
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
YicesSolver::mk_term(const std::string& kind,
                     const std::vector<Term>& args,
                     const std::vector<uint32_t>& params)
{
  term_t yices_res               = -1;
  size_t n_args                  = args.size();
  size_t n_params                = params.size();
  std::vector<term_t> yices_args = YicesTerm::terms_to_yices_terms(args);
  std::vector<term_t> vars;

  if (kind == Op::DISTINCT)
  {
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
  }
  else if (kind == Op::EQUAL)
  {
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
  }
  else if (kind == Op::ITE)
  {
    assert(n_args == 3);
    yices_res = yices_ite(yices_args[0], yices_args[1], yices_args[2]);
  }
  /* Arrays */
  else if (kind == Op::ARRAY_SELECT)
  {
    assert(n_args == 2);
    yices_res = yices_application1(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::ARRAY_STORE)
  {
    assert(n_args == 3);
    yices_res = yices_update1(yices_args[0], yices_args[1], yices_args[2]);
  }
  /* Boolean */
  else if (kind == Op::AND)
  {
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
  }
  else if (kind == Op::IFF)
  {
    assert(n_args == 2);
    yices_res = yices_iff(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::IMPLIES)
  {
    assert(n_args > 1);
    yices_res = mk_term_right_assoc(yices_args, yices_implies);
  }
  else if (kind == Op::NOT)
  {
    assert(n_args == 1);
    yices_res = yices_not(yices_args[0]);
  }
  else if (kind == Op::OR)
  {
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
        yices_res = yices_or2(YicesTerm::get_yices_term(args[0]),
                              YicesTerm::get_yices_term(args[1]));
      }
      else
      {
        yices_res = yices_or(n_args, yices_args.data());
      }
    }
  }
  else if (kind == Op::XOR)
  {
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
  }
  /* BV */
  else if (kind == Op::BV_EXTRACT)
  {
    assert(n_args == 1);
    assert(n_params == 2);
    yices_res = yices_bvextract(yices_args[0], params[1], params[0]);
  }
  else if (kind == Op::BV_REPEAT)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    yices_res = yices_bvrepeat(yices_args[0], params[0]);
  }
  else if (kind == Op::BV_ROTATE_LEFT)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    yices_res = yices_rotate_left(yices_args[0], params[0]);
  }
  else if (kind == Op::BV_ROTATE_RIGHT)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    yices_res = yices_rotate_right(yices_args[0], params[0]);
  }
  else if (kind == Op::BV_SIGN_EXTEND)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    yices_res = yices_sign_extend(yices_args[0], params[0]);
  }
  else if (kind == Op::BV_ZERO_EXTEND)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    yices_res = yices_zero_extend(yices_args[0], params[0]);
  }
  else if (kind == Op::BV_ADD)
  {
    assert(n_args > 1);
    if (d_rng.flip_coin())
    {
      yices_res = yices_bvsum(n_args, yices_args.data());
    }
    else
    {
      yices_res = mk_term_left_assoc(yices_args, yices_bvadd);
    }
  }
  else if (kind == Op::BV_AND)
  {
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
          yices_res = yices_bvand3(yices_args[0], yices_args[1], yices_args[2]);
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
  }
  else if (kind == Op::BV_ASHR)
  {
    assert(n_args == 2);
    yices_res = yices_bvashr(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_COMP)
  {
    assert(n_args == 2);
    yices_res = yices_redcomp(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_CONCAT)
  {
    assert(n_args > 1);
    if (d_rng.flip_coin())
    {
      yices_res = yices_bvconcat(n_args, yices_args.data());
    }
    else
    {
      yices_res = mk_term_left_assoc(yices_args, yices_bvconcat2);
    }
  }
  else if (kind == Op::BV_LSHR)
  {
    assert(n_args == 2);
    yices_res = yices_bvlshr(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_MULT)
  {
    assert(n_args > 1);
    if (d_rng.flip_coin())
    {
      yices_res = yices_bvproduct(n_args, yices_args.data());
    }
    else
    {
      yices_res = mk_term_left_assoc(yices_args, yices_bvmul);
    }
  }
  else if (kind == Op::BV_NAND)
  {
    assert(n_args == 2);
    yices_res = yices_bvnand(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_NEG)
  {
    assert(n_args == 1);
    yices_res = yices_bvneg(yices_args[0]);
  }
  else if (kind == Op::BV_NOR)
  {
    assert(n_args == 2);
    yices_res = yices_bvnor(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_NOT)
  {
    assert(n_args == 1);
    yices_res = yices_bvnot(yices_args[0]);
  }
  else if (kind == Op::BV_OR)
  {
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
          yices_res = yices_bvor3(yices_args[0], yices_args[1], yices_args[2]);
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
  }
  else if (kind == Op::BV_SDIV)
  {
    assert(n_args == 2);
    yices_res = yices_bvsdiv(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_SGE)
  {
    assert(n_args == 2);
    yices_res = yices_bvsge_atom(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_SGT)
  {
    assert(n_args == 2);
    yices_res = yices_bvsgt_atom(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_SHL)
  {
    assert(n_args == 2);
    yices_res = yices_bvshl(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_SLE)
  {
    assert(n_args == 2);
    yices_res = yices_bvsle_atom(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_SLT)
  {
    assert(n_args == 2);
    yices_res = yices_bvslt_atom(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_SMOD)
  {
    assert(n_args == 2);
    yices_res = yices_bvsmod(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_SREM)
  {
    assert(n_args == 2);
    yices_res = yices_bvsrem(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_SUB)
  {
    assert(n_args == 2);
    yices_res = yices_bvsub(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_UDIV)
  {
    assert(n_args == 2);
    yices_res = yices_bvdiv(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_UGE)
  {
    assert(n_args == 2);
    yices_res = yices_bvge_atom(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_UGT)
  {
    assert(n_args == 2);
    yices_res = yices_bvgt_atom(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_ULE)
  {
    assert(n_args == 2);
    yices_res = yices_bvle_atom(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_ULT)
  {
    assert(n_args == 2);
    yices_res = yices_bvlt_atom(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_UREM)
  {
    assert(n_args == 2);
    yices_res = yices_bvrem(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_XNOR)
  {
    assert(n_args == 2);
    yices_res = yices_bvxnor(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::BV_XOR)
  {
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
          yices_res = yices_bvor3(yices_args[0], yices_args[1], yices_args[2]);
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
  }
  /* Ints, Reals */
  else if (kind == Op::INT_IS_INT || kind == Op::REAL_IS_INT)
  {
    assert(n_args == 1);
    yices_res = yices_is_int_atom(yices_args[0]);
  }
  else if (kind == Op::INT_NEG || kind == Op::REAL_NEG)
  {
    assert(n_args == 1);
    yices_res = yices_neg(yices_args[0]);
  }
  else if (kind == Op::INT_SUB || kind == Op::REAL_SUB)
  {
    assert(n_args > 1);
    yices_res = mk_term_left_assoc(yices_args, yices_sub);
  }
  else if (kind == Op::INT_ADD || kind == Op::REAL_ADD)
  {
    assert(n_args > 1);
    if (d_rng.flip_coin())
    {
      yices_res = yices_sum(n_args, yices_args.data());
    }
    else
    {
      yices_res = mk_term_left_assoc(yices_args, yices_add);
    }
  }
  else if (kind == Op::INT_MUL || kind == Op::REAL_MUL)
  {
    assert(n_args > 1);
    if (d_rng.flip_coin())
    {
      yices_res = yices_product(n_args, yices_args.data());
    }
    else
    {
      yices_res = mk_term_left_assoc(yices_args, yices_mul);
    }
  }
  else if (kind == Op::INT_LT || kind == Op::REAL_LT)
  {
    assert(n_args > 1);
    yices_res = mk_term_chained(yices_args, yices_arith_lt_atom);
  }
  else if (kind == Op::INT_LTE || kind == Op::REAL_LTE)
  {
    assert(n_args > 1);
    yices_res = mk_term_chained(yices_args, yices_arith_leq_atom);
  }
  else if (kind == Op::INT_GT || kind == Op::REAL_GT)
  {
    assert(n_args > 1);
    yices_res = mk_term_chained(yices_args, yices_arith_gt_atom);
  }
  else if (kind == Op::INT_GTE || kind == Op::REAL_GTE)
  {
    assert(n_args > 1);
    yices_res = mk_term_chained(yices_args, yices_arith_geq_atom);
  }
  /* Ints */
  else if (kind == Op::INT_IS_DIV)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    std::stringstream ss;
    ss << params[0];
    term_t c = yices_parse_rational(ss.str().c_str());
    assert(is_valid_term(c));
    yices_res = yices_divides_atom(c, yices_args[0]);
  }
  else if (kind == Op::INT_DIV)
  {
    assert(n_args > 1);
    yices_res = mk_term_left_assoc(yices_args, yices_idiv);
  }
  else if (kind == Op::INT_MOD)
  {
    assert(n_args == 2);
    yices_res = yices_imod(yices_args[0], yices_args[1]);
  }
  else if (kind == Op::INT_ABS)
  {
    assert(n_args == 1);
    yices_res = yices_abs(yices_args[0]);
  }
  /* Reals */
  else if (kind == Op::REAL_DIV)
  {
    assert(n_args > 1);
    yices_res = mk_term_left_assoc(yices_args, yices_division);
  }
  /* Quantifiers */
  else if (kind == Op::FORALL || kind == Op::EXISTS)
  {
    uint32_t n = yices_args.size() - 1;
    for (uint32_t i = 0; i < n; ++i)
    {
      vars.push_back(yices_args[i]);
    }
    if (kind == Op::EXISTS)
    {
      yices_res = yices_exists(n, vars.data(), yices_args.back());
    }
    else
    {
      yices_res = yices_forall(n, vars.data(), yices_args.back());
    }
  }
  /* UF */
  else if (kind == Op::UF_APPLY)
  {
    assert(n_args > 1);
    if (n_args == 2 && d_rng.flip_coin())
    {
      yices_res = yices_application1(yices_args[0], yices_args[1]);
    }
    else if (n_args == 3 && d_rng.flip_coin())
    {
      yices_res =
          yices_application2(yices_args[0], yices_args[1], yices_args[2]);
    }
    else if (n_args == 4 && d_rng.flip_coin())
    {
      yices_res = yices_application3(
          yices_args[0], yices_args[1], yices_args[2], yices_args[3]);
    }
    else
    {
      yices_res =
          yices_application(yices_args[0], n_args - 1, yices_args.data() + 1);
    }
  }
  else
  {
    /* Solver-specific operators */
    // BV
    if (kind == YicesTerm::OP_REDAND)
    {
      assert(n_args == 1);
      yices_res = yices_redand(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_REDOR)
    {
      assert(n_args == 1);
      yices_res = yices_redor(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_BVSQUARE)
    {
      assert(n_args == 1);
      yices_res = yices_bvsquare(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_BVPOWER)
    {
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res =
          yices_bvpower(yices_args[0],
                        uint32_to_value_in_range(
                            params[0], 0, args[0]->get_sort()->get_bv_size()));
    }
    else if (kind == YicesTerm::OP_SHIFT_LEFT0)
    {
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_shift_left0(
          yices_args[0],
          uint32_to_value_in_range(
              params[0], 0, args[0]->get_sort()->get_bv_size()));
    }
    else if (kind == YicesTerm::OP_SHIFT_LEFT1)
    {
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_shift_left1(
          yices_args[0],
          uint32_to_value_in_range(
              params[0], 0, args[0]->get_sort()->get_bv_size()));
    }
    else if (kind == YicesTerm::OP_SHIFT_RIGHT0)
    {
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_shift_right0(
          yices_args[0],
          uint32_to_value_in_range(
              params[0], 0, args[0]->get_sort()->get_bv_size()));
    }
    else if (kind == YicesTerm::OP_SHIFT_RIGHT1)
    {
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_shift_right1(
          yices_args[0],
          uint32_to_value_in_range(
              params[0], 0, args[0]->get_sort()->get_bv_size()));
    }
    else if (kind == YicesTerm::OP_ASHIFT_RIGHT)
    {
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_ashift_right(
          yices_args[0],
          uint32_to_value_in_range(
              params[0], 0, args[0]->get_sort()->get_bv_size()));
    }
    else if (kind == YicesTerm::OP_BITEXTRACT)
    {
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_bitextract(
          yices_args[0],
          uint32_to_value_in_range(
              params[0], 0, args[0]->get_sort()->get_bv_size() - 1));
    }
    else if (kind == YicesTerm::OP_BVARRAY)
    {
      assert(n_args > 0);
      yices_res = yices_bvarray(n_args, yices_args.data());
    }
    // Arithmetic
    else if (kind == YicesTerm::OP_INT_EQ0 || kind == YicesTerm::OP_REAL_EQ0)
    {
      assert(n_args == 1);
      yices_res = yices_arith_eq0_atom(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_INT_NEQ0 || kind == YicesTerm::OP_REAL_NEQ0)
    {
      assert(n_args == 1);
      yices_res = yices_arith_neq0_atom(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_INT_GEQ0 || kind == YicesTerm::OP_REAL_GEQ0)
    {
      assert(n_args == 1);
      yices_res = yices_arith_geq0_atom(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_INT_LEQ0 || kind == YicesTerm::OP_REAL_LEQ0)
    {
      assert(n_args == 1);
      yices_res = yices_arith_leq0_atom(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_INT_GT0 || kind == YicesTerm::OP_REAL_GT0)
    {
      assert(n_args == 1);
      yices_res = yices_arith_gt0_atom(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_INT_LT0 || kind == YicesTerm::OP_REAL_LT0)
    {
      assert(n_args == 1);
      yices_res = yices_arith_lt0_atom(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_INT_POWER
             || kind == YicesTerm::OP_REAL_POWER)
    {
      assert(n_args == 1);
      assert(n_params == 1);
      yices_res = yices_power(
          yices_args[0],
          uint32_to_value_in_range(params[0], 0, MURXLA_YICES_MAX_DEGREE));
    }
    else if (kind == YicesTerm::OP_INT_SQUARE
             || kind == YicesTerm::OP_REAL_SQUARE)
    {
      assert(n_args == 1);
      yices_res = yices_square(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_INT_CEIL || kind == YicesTerm::OP_REAL_CEIL)
    {
      assert(n_args == 1);
      yices_res = yices_ceil(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_INT_FLOOR
             || kind == YicesTerm::OP_REAL_FLOOR)
    {
      assert(n_args == 1);
      yices_res = yices_floor(yices_args[0]);
    }
    else if (kind == YicesTerm::OP_INT_POLY || kind == YicesTerm::OP_REAL_POLY)
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
    else if (kind == YicesTerm::OP_REAL_RPOLY)
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
    else
    {
      MURXLA_CHECK_CONFIG(false)
          << "YicesSolver: operator kind '" << kind << "' not configured";
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
      new YicesSort(yices_type_of_term(YicesTerm::get_yices_term(term))));
}

void
YicesSolver::assert_formula(const Term& t)
{
  if (!d_context) d_context = yices_new_context(d_config);
  yices_assert_formula(d_context, YicesTerm::get_yices_term(t));
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
  std::vector<term_t> yices_assumptions =
      YicesTerm::terms_to_yices_terms(assumptions);
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
  return YicesTerm::yices_terms_to_terms(&yices_res);
}

std::vector<Term>
YicesSolver::get_unsat_core()
{
  if (!d_context) d_context = yices_new_context(d_config);
  term_vector_t yices_res;
  yices_init_term_vector(&yices_res);
  int32_t status = yices_get_unsat_core(d_context, &yices_res);
  assert(status == 0);
  return YicesTerm::yices_terms_to_terms(&yices_res);
}

std::vector<Term>
YicesSolver::get_value(std::vector<Term>& terms)
{
  if (!d_context) d_context = yices_new_context(d_config);

  std::vector<Term> res;
  std::vector<term_t> yices_res;
  std::vector<term_t> yices_terms = YicesTerm::terms_to_yices_terms(terms);

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
  res = YicesTerm::yices_terms_to_terms(yices_res);
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
YicesSolver::reset()
{
  yices_reset();
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
YicesSolver::mk_term_right_assoc(std::vector<term_t>& args,
                                 term_t (*fun)(term_t, term_t)) const
{
  uint32_t n_args = args.size();
  assert(n_args >= 2);
  term_t res, tmp;
  res = args[n_args - 1];
  for (uint32_t i = 1; i < n_args; ++i)
  {
    tmp = fun(args[n_args - i - 1], res);
    assert(is_valid_term(tmp));
    res = tmp;
  }
  assert(res);
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

/* -------------------------------------------------------------------------- */
/* OpKindManager configuration.                                               */
/* -------------------------------------------------------------------------- */

void
YicesSolver::configure_opmgr(OpKindManager* opmgr) const
{
  /* BV */
  opmgr->add_op_kind(
      YicesTerm::OP_BVSQUARE, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      YicesTerm::OP_BVPOWER, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(YicesTerm::OP_REDAND, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(YicesTerm::OP_REDOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(
      YicesTerm::OP_SHIFT_LEFT0, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      YicesTerm::OP_SHIFT_LEFT1, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      YicesTerm::OP_SHIFT_RIGHT0, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      YicesTerm::OP_SHIFT_RIGHT1, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);
  opmgr->add_op_kind(
      YicesTerm::OP_ASHIFT_RIGHT, 1, 1, SORT_BV, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(
      YicesTerm::OP_BITEXTRACT, 1, 1, SORT_BOOL, {SORT_BV}, THEORY_BV);

  opmgr->add_op_kind(YicesTerm::OP_BVARRAY,
                     MURXLA_MK_TERM_N_ARGS,
                     0,
                     SORT_BV,
                     {SORT_BOOL},
                     THEORY_BV);

  /* Ints */
  opmgr->add_op_kind(
      YicesTerm::OP_INT_EQ0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      YicesTerm::OP_INT_NEQ0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      YicesTerm::OP_INT_GEQ0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      YicesTerm::OP_INT_GT0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      YicesTerm::OP_INT_LEQ0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      YicesTerm::OP_INT_LT0, 1, 0, SORT_BOOL, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      YicesTerm::OP_INT_POWER, 1, 1, SORT_INT, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      YicesTerm::OP_INT_SQUARE, 1, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      YicesTerm::OP_INT_CEIL, 1, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(
      YicesTerm::OP_INT_FLOOR, 1, 0, SORT_INT, {SORT_INT}, THEORY_INT);
  opmgr->add_op_kind(YicesTerm::OP_INT_POLY,
                     MURXLA_MK_TERM_N_ARGS,
                     0,
                     SORT_INT,
                     {SORT_INT},
                     THEORY_INT);
  /* Reals */
  opmgr->add_op_kind(
      YicesTerm::OP_REAL_EQ0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  opmgr->add_op_kind(
      YicesTerm::OP_REAL_NEQ0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  opmgr->add_op_kind(
      YicesTerm::OP_REAL_GEQ0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  opmgr->add_op_kind(
      YicesTerm::OP_REAL_GT0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  opmgr->add_op_kind(
      YicesTerm::OP_REAL_LEQ0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  opmgr->add_op_kind(
      YicesTerm::OP_REAL_LT0, 1, 0, SORT_BOOL, {SORT_REAL}, THEORY_REAL);
  opmgr->add_op_kind(
      YicesTerm::OP_REAL_POWER, 1, 1, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  opmgr->add_op_kind(
      YicesTerm::OP_REAL_SQUARE, 1, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  opmgr->add_op_kind(
      YicesTerm::OP_REAL_CEIL, 1, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  opmgr->add_op_kind(
      YicesTerm::OP_REAL_FLOOR, 1, 0, SORT_REAL, {SORT_REAL}, THEORY_REAL);
  opmgr->add_op_kind(YicesTerm::OP_REAL_POLY,
                     MURXLA_MK_TERM_N_ARGS,
                     0,
                     SORT_REAL,
                     {SORT_REAL},
                     THEORY_REAL);
  opmgr->add_op_kind(YicesTerm::OP_REAL_RPOLY,
                     MURXLA_MK_TERM_N_ARGS,
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
}  // namespace murxla

#endif
