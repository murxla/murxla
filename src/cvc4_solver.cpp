#ifdef MURXLA_USE_CVC5

#include "cvc4_solver.hpp"

#include <cassert>

#include "config.hpp"
#include "theory.hpp"
#include "util.hpp"

namespace murxla {
namespace cvc5 {

#define MURXLA_CVC5_MAX_N_TERMS_CHECK_ENTAILED 5

/* -------------------------------------------------------------------------- */
/* Cvc5Sort                                                                   */
/* -------------------------------------------------------------------------- */

size_t
Cvc5Sort::hash() const
{
  return std::hash<::cvc5::api::Sort>{}(d_sort);
}

bool
Cvc5Sort::equals(const Sort& other) const
{
  Cvc5Sort* cvc5_sort = dynamic_cast<Cvc5Sort*>(other.get());
  if (cvc5_sort)
  {
    return d_sort == cvc5_sort->d_sort;
  }
  return false;
}

bool
Cvc5Sort::is_array() const
{
  return d_sort.isArray();
}

bool
Cvc5Sort::is_bool() const
{
  return d_sort.isBoolean();
}

bool
Cvc5Sort::is_bv() const
{
  return d_sort.isBitVector();
}

bool
Cvc5Sort::is_fp() const
{
  return d_sort.isFloatingPoint();
}

bool
Cvc5Sort::is_fun() const
{
  return d_sort.isFunction();
}

bool
Cvc5Sort::is_int() const
{
  return d_sort.isInteger();
}

bool
Cvc5Sort::is_real() const
{
  return d_sort.isReal();
}

bool
Cvc5Sort::is_rm() const
{
  return d_sort.isRoundingMode();
}

bool
Cvc5Sort::is_string() const
{
  return d_sort.isString();
}

bool
Cvc5Sort::is_reglan() const
{
  return d_sort.isRegExp();
}

uint32_t
Cvc5Sort::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = d_sort.getBVSize();
  assert(res);
  return res;
}

uint32_t
Cvc5Sort::get_fp_exp_size() const
{
  assert(is_fp());
  uint32_t res = d_sort.getFPExponentSize();
  assert(res);
  return res;
}

uint32_t
Cvc5Sort::get_fp_sig_size() const
{
  assert(is_fp());
  uint32_t res = d_sort.getFPSignificandSize();
  assert(res);
  return res;
}

/* -------------------------------------------------------------------------- */
/* Cvc5Term                                                                   */
/* -------------------------------------------------------------------------- */

size_t
Cvc5Term::hash() const
{
  return std::hash<::cvc5::api::Term>{}(d_term);
}

bool
Cvc5Term::equals(const Term& other) const
{
  Cvc5Term* cvc5_term = dynamic_cast<Cvc5Term*>(other.get());
  if (cvc5_term) return d_term == cvc5_term->d_term;
  return false;
}

bool
Cvc5Term::is_array() const
{
  return get_sort()->is_array();
}

bool
Cvc5Term::is_bool() const
{
  return get_sort()->is_bool();
}

bool
Cvc5Term::is_bv() const
{
  return get_sort()->is_bv();
}

bool
Cvc5Term::is_fp() const
{
  return get_sort()->is_fp();
}

bool
Cvc5Term::is_fun() const
{
  return get_sort()->is_fun();
}

bool
Cvc5Term::is_int() const
{
  return get_sort()->is_int();
}

bool
Cvc5Term::is_real() const
{
  return get_sort()->is_real();
}

bool
Cvc5Term::is_rm() const
{
  return get_sort()->is_rm();
}

bool
Cvc5Term::is_string() const
{
  return get_sort()->is_string();
}

bool
Cvc5Term::is_reglan() const
{
  return get_sort()->is_reglan();
}

/* -------------------------------------------------------------------------- */
/* Cvc5Solver                                                                 */
/* -------------------------------------------------------------------------- */

const Solver::SpecialValueKind Cvc5Solver::SPECIAL_VALUE_PI = "cvc5-pi";

OpKindSet
Cvc5Solver::get_unsupported_op_kinds() const
{
  return {Op::IFF};
}

SortKindSet
Cvc5Solver::get_unsupported_array_index_sort_kinds() const
{
  return {SORT_REGLAN};
}

SortKindSet
Cvc5Solver::get_unsupported_array_element_sort_kinds() const
{
  return {SORT_REGLAN};
}

// TODO: check why SORT_REGLAN is not allowed in cvc5
SortKindSet
Cvc5Solver::get_unsupported_fun_domain_sort_kinds() const
{
  return {SORT_REGLAN};
}

Cvc5Solver::~Cvc5Solver()
{
  if (d_solver)
  {
    delete d_solver;
    d_solver = nullptr;
  }
}

void
Cvc5Solver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = new ::cvc5::api::Solver();
  init_op_kinds();
  d_solver->setOption("fp-exp", "true");
  d_solver->setOption("strings-exp", "true");

  add_special_value(SORT_REAL, SPECIAL_VALUE_PI);
}

void
Cvc5Solver::delete_solver()
{
  assert(d_solver != nullptr);
  delete d_solver;
  d_solver = nullptr;
}

::cvc5::api::Solver*
Cvc5Solver::get_solver()
{
  return d_solver;
}

bool
Cvc5Solver::is_initialized() const
{
  return d_solver != nullptr;
}

bool
Cvc5Solver::check_unsat_assumption(const Term& t) const
{
  return !get_cvc5_term(t).isNull();
}

/* -------------------------------------------------------------------------- */

Sort
Cvc5Solver::mk_sort(SortKind kind)
{
  ::cvc5::api::Sort cvc5_res;
  switch (kind)
  {
    case SORT_BOOL: cvc5_res = d_solver->getBooleanSort(); break;
    case SORT_INT: cvc5_res = d_solver->getIntegerSort(); break;
    case SORT_REAL: cvc5_res = d_solver->getRealSort(); break;
    case SORT_RM: cvc5_res = d_solver->getRoundingModeSort(); break;
    case SORT_REGLAN: cvc5_res = d_solver->getRegExpSort(); break;
    case SORT_STRING: cvc5_res = d_solver->getStringSort(); break;

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unsupported sort kind '" << kind
          << "' as argument to Cvc5Solver::mk_sort, expected '" << SORT_BOOL
          << "', '" << SORT_INT << "', '" << SORT_REAL << "', '" << SORT_RM
          << "', '" << SORT_REGLAN << "' or '" << SORT_STRING << "'";
  }
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_solver, cvc5_res));
}

Sort
Cvc5Solver::mk_sort(SortKind kind, uint32_t size)
{
  MURXLA_CHECK_CONFIG(kind == SORT_BV)
      << "unsupported sort kind '" << kind
      << "' as argument to Cvc5Solver::mk_sort, expected '" << SORT_BV << "'";
  ::cvc5::api::Sort cvc5_res = d_solver->mkBitVectorSort(size);
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_solver, cvc5_res));
  assert(res);
  return res;
}

Sort
Cvc5Solver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  MURXLA_CHECK_CONFIG(kind == SORT_FP)
      << "unsupported sort kind '" << kind
      << "' as argument to Cvc5Solver::mk_sort, expected '" << SORT_FP << "'";
  ::cvc5::api::Sort cvc5_res = d_solver->mkFloatingPointSort(esize, ssize);
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_solver, cvc5_res));
  assert(res);
  return res;
}

Sort
Cvc5Solver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  ::cvc5::api::Sort cvc5_res;

  switch (kind)
  {
    case SORT_ARRAY:
      cvc5_res = d_solver->mkArraySort(get_cvc5_sort(sorts[0]),
                                       get_cvc5_sort(sorts[1]));
      break;

    case SORT_FUN:
    {
      std::vector<::cvc5::api::Sort> domain;
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        domain.push_back(get_cvc5_sort(*it));
      }
      ::cvc5::api::Sort codomain = get_cvc5_sort(sorts.back());

      cvc5_res = d_solver->mkFunctionSort(domain, codomain);
      break;
    }

    default:
      MURXLA_CHECK_CONFIG(false) << "unsupported sort kind '" << kind
                                 << "' as argument to Cvc5Solver::mk_sort, "
                                    "expected '"
                                 << SORT_ARRAY << "' or '" << SORT_FUN << "'";
  }
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  std::shared_ptr<Cvc5Sort> res(new Cvc5Sort(d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_const(Sort sort, const std::string& name)
{
  ::cvc5::api::Term cvc5_res = d_solver->mkConst(get_cvc5_sort(sort), name);
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  return std::shared_ptr<Cvc5Term>(new Cvc5Term(d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_var(Sort sort, const std::string& name)
{
  ::cvc5::api::Term cvc5_res = d_solver->mkVar(get_cvc5_sort(sort), name);
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  return std::shared_ptr<Cvc5Term>(new Cvc5Term(d_solver, cvc5_res));
}

Term
Cvc5Solver::mk_value(Sort sort, bool value)
{
  assert(sort->is_bool());
  MURXLA_CHECK_CONFIG(false) << "unexpected sort of kind '" << sort->get_kind()
                             << "' as argument to "
                                "Cvc5Solver::mk_value, expected Boolean sort ";

  ::cvc5::api::Term cvc5_res;

  if (d_rng.flip_coin())
  {
    cvc5_res = value ? d_solver->mkTrue() : d_solver->mkFalse();
  }
  else
  {
    cvc5_res = d_solver->mkBoolean(value);
  }
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  std::shared_ptr<Cvc5Term> res(new Cvc5Term(d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_value(Sort sort, std::string value)
{
  ::cvc5::api::Term cvc5_res;
  ::cvc5::api::Sort cvc5_sort = get_cvc5_sort(sort);
  SortKind sort_kind        = sort->get_kind();

  switch (sort_kind)
  {
    case SORT_INT:
    {
      assert(sort->is_int());
      int64_t val64 = 0;
      bool fits64   = true;
      try
      {
        val64 = std::stoll(value);
      }
      catch (std::out_of_range& e)
      {
        fits64 = false;
      }
      if (fits64 && d_rng.flip_coin())
      {
        cvc5_res = d_solver->mkReal(val64);
      }
      else
      {
        cvc5_res = d_solver->mkReal(value);
      }
    }
    break;

    case SORT_REAL:
      assert(sort->is_real());
      if (value.find('.') != std::string::npos)
      {
        int64_t val64 = 0;
        bool fits64   = true;
        try
        {
          val64 = std::stoll(value);
        }
        catch (std::out_of_range& e)
        {
          fits64 = false;
        }
        if (fits64 && d_rng.flip_coin())
        {
          cvc5_res = d_solver->mkReal(val64);
        }
        else
        {
          cvc5_res = d_solver->mkReal(value);
        }
      }
      else
      {
        cvc5_res = d_solver->mkReal(value);
      }
      break;

    case SORT_REGLAN:
    case SORT_STRING:
      // TODO: test more mkString functions
      cvc5_res = d_solver->mkString(value);
      break;

    default:
      MURXLA_CHECK_CONFIG(false)
          << "unexpected sort of kind '" << sort->get_kind()
          << "' as argument to "
             "Cvc5Solver::mk_value, expected Integer, Real, Reglan or String "
             "sort ";
  }
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  std::shared_ptr<Cvc5Term> res(new Cvc5Term(d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_value(Sort sort, std::string num, std::string den)
{
  assert(sort->is_real());
  MURXLA_CHECK_CONFIG(sort->is_real())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to "
         "Cvc5Solver::mk_value, expected Real sort";
  ::cvc5::api::Term cvc5_res;

  cvc5_res = d_solver->mkReal(
      static_cast<int64_t>(strtoull(num.c_str(), nullptr, 10)),
      static_cast<int64_t>(strtoull(den.c_str(), nullptr, 10)));
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  std::shared_ptr<Cvc5Term> res(new Cvc5Term(d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_value(Sort sort, std::string value, Base base)
{
  MURXLA_CHECK_CONFIG(sort->is_bv())
      << "unexpected sort of kind '" << sort->get_kind()
      << "' as argument to "
         "Cvc5Solver::mk_value, expected bit-vector sort";

  ::cvc5::api::Term cvc5_res;
  ::cvc5::api::Sort cvc5_sort = get_cvc5_sort(sort);
  uint32_t bw               = sort->get_bv_size();

  switch (base)
  {
    case DEC:
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc5_res =
            d_solver->mkBitVector(bw, strtoull(value.c_str(), nullptr, 10));
      }
      else
      {
        cvc5_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bw, value, 10)
                       : d_solver->mkBitVector(bw, value.c_str(), 10);
      }
      break;

    case HEX:
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc5_res =
            d_solver->mkBitVector(bw, strtoull(value.c_str(), nullptr, 16));
      }
      else
      {
        cvc5_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bw, value, 16)
                       : d_solver->mkBitVector(bw, value.c_str(), 16);
      }
      break;

    default:
      assert(base == BIN);
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc5_res =
            d_solver->mkBitVector(bw, strtoull(value.c_str(), nullptr, 2));
      }
      else
      {
        cvc5_res = d_rng.flip_coin() ? d_solver->mkBitVector(value, 2)
                                     : d_solver->mkBitVector(value.c_str(), 2);
      }
  }
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  std::shared_ptr<Cvc5Term> res(new Cvc5Term(d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_special_value(Sort sort, const SpecialValueKind& value)
{
  ::cvc5::api::Term cvc5_res;

  switch (sort->get_kind())
  {
    case SORT_BV:
    {
      uint32_t bw = sort->get_bv_size();
      if (value == SPECIAL_VALUE_BV_ZERO)
      {
        cvc5_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bv_special_value_zero_str(bw), 2)
                       : d_solver->mkBitVector(
                           bv_special_value_zero_str(bw).c_str(), 2);
      }
      else if (value == SPECIAL_VALUE_BV_ONE)
      {
        cvc5_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bv_special_value_one_str(bw), 2)
                       : d_solver->mkBitVector(
                           bv_special_value_one_str(bw).c_str(), 2);
      }
      else if (value == SPECIAL_VALUE_BV_ONES)
      {
        cvc5_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bv_special_value_ones_str(bw), 2)
                       : d_solver->mkBitVector(
                           bv_special_value_ones_str(bw).c_str(), 2);
      }
      else if (value == SPECIAL_VALUE_BV_MIN_SIGNED)
      {
        cvc5_res =
            d_rng.flip_coin()
                ? d_solver->mkBitVector(bv_special_value_min_signed_str(bw), 2)
                : d_solver->mkBitVector(
                    bv_special_value_min_signed_str(bw).c_str(), 2);
      }
      else
      {
        assert(value == SPECIAL_VALUE_BV_MAX_SIGNED);
        cvc5_res =
            d_rng.flip_coin()
                ? d_solver->mkBitVector(bv_special_value_max_signed_str(bw), 2)
                : d_solver->mkBitVector(
                    bv_special_value_max_signed_str(bw).c_str(), 2);
      }
    }
    break;

    case SORT_FP:
    {
      uint32_t ew = sort->get_fp_exp_size();
      uint32_t sw = sort->get_fp_sig_size();
      if (value == SPECIAL_VALUE_FP_POS_INF)
      {
        cvc5_res = d_solver->mkPosInf(ew, sw);
      }
      else if (value == SPECIAL_VALUE_FP_NEG_INF)
      {
        cvc5_res = d_solver->mkNegInf(ew, sw);
      }
      else if (value == SPECIAL_VALUE_FP_POS_ZERO)
      {
        cvc5_res = d_solver->mkPosZero(ew, sw);
      }
      else if (value == SPECIAL_VALUE_FP_NEG_ZERO)
      {
        cvc5_res = d_solver->mkNegZero(ew, sw);
      }
      else
      {
        assert(value == SPECIAL_VALUE_FP_NAN);
        cvc5_res = d_solver->mkNaN(ew, sw);
      }
    }
    break;

    case SORT_RM:
      if (value == SPECIAL_VALUE_RM_RNE)
      {
        cvc5_res = d_solver->mkRoundingMode(
            ::cvc5::api::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
      }
      else if (value == SPECIAL_VALUE_RM_RNA)
      {
        cvc5_res = d_solver->mkRoundingMode(
            ::cvc5::api::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY);
      }
      else if (value == SPECIAL_VALUE_RM_RTN)
      {
        cvc5_res = d_solver->mkRoundingMode(
            ::cvc5::api::RoundingMode::ROUND_TOWARD_NEGATIVE);
      }
      else if (value == SPECIAL_VALUE_RM_RTP)
      {
        cvc5_res = d_solver->mkRoundingMode(
            ::cvc5::api::RoundingMode::ROUND_TOWARD_POSITIVE);
      }
      else
      {
        assert(value == SPECIAL_VALUE_RM_RTZ);
        cvc5_res = d_solver->mkRoundingMode(
            ::cvc5::api::RoundingMode::ROUND_TOWARD_ZERO);
      }
      break;

    case SORT_REAL:
      assert(value == SPECIAL_VALUE_PI);
      cvc5_res = d_solver->mkPi();
      break;

    case SORT_REGLAN:
      if (value == SPECIAL_VALUE_RE_NONE)
      {
        cvc5_res = d_solver->mkRegexpEmpty();
      }
      else if (value == SPECIAL_VALUE_RE_ALL)
      {
        cvc5_res = d_solver->mkTerm(::cvc5::api::REGEXP_STAR,
                                    d_solver->mkRegexpSigma());
      }
      else
      {
        assert(value == SPECIAL_VALUE_RE_ALLCHAR);
        cvc5_res = d_solver->mkRegexpSigma();
      }
      break;

    default:
      MURXLA_CHECK_CONFIG(sort->is_bv())
          << "unexpected sort of kind '" << sort->get_kind()
          << "' as argument to "
             "Cvc5Solver::mk_special_value, expected bit-vector, "
             "floating-point, "
             "RoundingMode, Real or Reglan sort";
  }
  std::shared_ptr<Cvc5Term> res(new Cvc5Term(d_solver, cvc5_res));
  assert(res);
  return res;
}

Term
Cvc5Solver::mk_term(const OpKind& kind,
                    std::vector<Term>& args,
                    std::vector<uint32_t>& params)
{
  MURXLA_CHECK_CONFIG(d_op_kinds.find(kind) != d_op_kinds.end())
      << "Cvc5Solver: operator kind '" << kind << "' not configured";

  ::cvc5::api::Term cvc5_res;
  ::cvc5::api::Kind cvc5_kind = d_op_kinds.at(kind);
  ::cvc5::api::Op cvc5_opterm;

  int32_t n_args    = args.size();
  uint32_t n_params = params.size();

  if (kind == Op::FORALL || kind == Op::EXISTS)
  {
    assert(args.size() >= 2);
    std::vector<::cvc5::api::Term> vars;
    for (size_t i = 0; i < args.size() - 1; ++i)
    {
      vars.push_back(get_cvc5_term(args[i]));
    }
    ::cvc5::api::Term bvl =
        d_solver->mkTerm(::cvc5::api::Kind::BOUND_VAR_LIST, vars);
    ::cvc5::api::Term body = get_cvc5_term(args.back());
    cvc5_res               = d_solver->mkTerm(cvc5_kind, bvl, body);
    goto DONE;
  }

  /* create Op for indexed operators */
  switch (n_params)
  {
    case 1:
    {
      cvc5_opterm = d_solver->mkOp(cvc5_kind, params[0]);
      assert(!cvc5_opterm.isNull());
      assert(!d_rng.pick_with_prob(1) || cvc5_opterm == cvc5_opterm);
      assert(!d_rng.pick_with_prob(1) || !(cvc5_opterm != cvc5_opterm));
      assert(cvc5_opterm.isIndexed());
      assert(cvc5_opterm.getKind() == cvc5_kind);
      uint32_t idx;
      if (kind == Op::INT_IS_DIV)
      {
        std::string sidx = cvc5_opterm.getIndices<std::string>();
        /* we only generate 32 bit indices, so this shouldn't throw */
        idx = str_to_uint32(sidx);
      }
      else
      {
        idx = cvc5_opterm.getIndices<uint32_t>();
      }
      assert(idx == params[0]);
      break;
    }
    case 2:
    {
      cvc5_opterm = d_solver->mkOp(cvc5_kind, params[0], params[1]);
      assert(!cvc5_opterm.isNull());
      assert(!d_rng.pick_with_prob(1) || cvc5_opterm == cvc5_opterm);
      assert(!d_rng.pick_with_prob(1) || !(cvc5_opterm != cvc5_opterm));
      assert(cvc5_opterm.isIndexed());
      assert(cvc5_opterm.getKind() == cvc5_kind);
      std::pair<uint32_t, uint32_t> indices =
          cvc5_opterm.getIndices<std::pair<uint32_t, uint32_t>>();
      assert(indices.first == params[0]);
      assert(indices.second == params[1]);
      break;
    }
    default: assert(n_params == 0);
  }

  /* use vector with 50% probability */
  if (d_rng.flip_coin()) n_args = MURXLA_MK_TERM_N_ARGS_BIN;

  /* create term */
  switch (n_args)
  {
    case 0:
      cvc5_res = n_params ? d_solver->mkTerm(cvc5_opterm)
                          : d_solver->mkTerm(cvc5_kind);
      break;

    case 1:
      if (kind == Op::NOT && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc5_res = get_cvc5_term(args[0]).notTerm();
      }
      else
      {
        cvc5_res = n_params
                       ? d_solver->mkTerm(cvc5_opterm, get_cvc5_term(args[0]))
                       : d_solver->mkTerm(cvc5_kind, get_cvc5_term(args[0]));
      }
      break;

    case 2:
      if (kind == Op::AND && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc5_res = get_cvc5_term(args[0]).andTerm(get_cvc5_term(args[1]));
      }
      else if (kind == Op::OR && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc5_res = get_cvc5_term(args[0]).orTerm(get_cvc5_term(args[1]));
      }
      else if (kind == Op::XOR && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc5_res = get_cvc5_term(args[0]).xorTerm(get_cvc5_term(args[1]));
      }
      else if (kind == Op::EQUAL && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc5_res = get_cvc5_term(args[0]).eqTerm(get_cvc5_term(args[1]));
      }
      else if (kind == Op::IMPLIES && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc5_res = get_cvc5_term(args[0]).impTerm(get_cvc5_term(args[1]));
      }
      else
      {
        cvc5_res =
            n_params
                ? d_solver->mkTerm(
                    cvc5_opterm, get_cvc5_term(args[0]), get_cvc5_term(args[1]))
                : d_solver->mkTerm(
                    cvc5_kind, get_cvc5_term(args[0]), get_cvc5_term(args[1]));
      }
      break;

    case 3:
      if (kind == Op::ITE && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc5_res = get_cvc5_term(args[0]).iteTerm(get_cvc5_term(args[1]),
                                                  get_cvc5_term(args[2]));
      }
      else
      {
        cvc5_res = n_params ? d_solver->mkTerm(cvc5_opterm,
                                               get_cvc5_term(args[0]),
                                               get_cvc5_term(args[1]),
                                               get_cvc5_term(args[2]))
                            : d_solver->mkTerm(cvc5_kind,
                                               get_cvc5_term(args[0]),
                                               get_cvc5_term(args[1]),
                                               get_cvc5_term(args[2]));
      }
      break;

    default:
      assert(n_args == MURXLA_MK_TERM_N_ARGS_BIN || n_args > 3);
      std::vector<::cvc5::api::Term> cvc5_args;
      cvc5_args = terms_to_cvc5_terms(args);
      cvc5_res  = n_params ? d_solver->mkTerm(cvc5_opterm, cvc5_args)
                           : d_solver->mkTerm(cvc5_kind, cvc5_args);
  }
DONE:
  assert(!cvc5_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc5_res == cvc5_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc5_res != cvc5_res));
  assert(cvc5_kind == cvc5_res.getKind()
         || (cvc5_res.getSort().isBoolean()
             && cvc5_res.getKind() == ::cvc5::api::Kind::AND));
  return std::shared_ptr<Cvc5Term>(new Cvc5Term(d_solver, cvc5_res));
}

Sort
Cvc5Solver::get_sort(Term term, SortKind sort_kind) const
{
  (void) sort_kind;
  ::cvc5::api::Term cvc5_term = get_cvc5_term(term);
  return std::shared_ptr<Cvc5Sort>(new Cvc5Sort(d_solver, cvc5_term.getSort()));
}

void
Cvc5Solver::assert_formula(const Term& t)
{
  d_solver->assertFormula(get_cvc5_term(t));
}

Solver::Result
Cvc5Solver::check_sat()
{
  ::cvc5::api::Result res = d_solver->checkSat();
  assert(res != ::cvc5::api::Result());
  assert(!d_rng.pick_with_prob(1) || res == res);
  if (res.isSat()) return Result::SAT;
  if (res.isUnsat()) return Result::UNSAT;
  assert(res.isSatUnknown());
  if (d_rng.pick_with_prob(1))
  {
    (void) res.getUnknownExplanation();
  }
  return Result::UNKNOWN;
}

Solver::Result
Cvc5Solver::check_sat_assuming(std::vector<Term>& assumptions)
{
  ::cvc5::api::Result res;
  std::vector<::cvc5::api::Term> cvc5_assumptions =
      terms_to_cvc5_terms(assumptions);

  assert(assumptions.size() == cvc5_assumptions.size());

  res = cvc5_assumptions.size() == 1 && d_rng.flip_coin()
            ? d_solver->checkSatAssuming(cvc5_assumptions[0])
            : d_solver->checkSatAssuming(cvc5_assumptions);
  assert(!d_rng.pick_with_prob(1) || res == res);
  assert(res != ::cvc5::api::Result());
  assert(!res.isEntailed());
  assert(!res.isNotEntailed());
  assert(!res.isEntailmentUnknown());
  if (res.isSat()) return Result::SAT;
  if (res.isUnsat()) return Result::UNSAT;
  assert(res.isSatUnknown());
  if (d_rng.pick_with_prob(1))
  {
    (void) res.getUnknownExplanation();
  }
  return Result::UNKNOWN;
}

std::vector<Term>
Cvc5Solver::get_unsat_assumptions()
{
  std::vector<Term> res;
  std::vector<::cvc5::api::Term> cvc5_res = d_solver->getUnsatAssumptions();
  return cvc5_terms_to_terms(cvc5_res);
}

std::vector<Term>
Cvc5Solver::get_value(std::vector<Term>& terms)
{
  std::vector<Term> res;
  std::vector<::cvc5::api::Term> cvc5_res;
  std::vector<::cvc5::api::Term> cvc5_terms = terms_to_cvc5_terms(terms);

  if (d_rng.flip_coin())
  {
    cvc5_res = d_solver->getValue(cvc5_terms);
  }
  else
  {
    for (::cvc5::api::Term& t : cvc5_terms)
    {
      cvc5_res.push_back(d_solver->getValue(t));
    }
  }
  return cvc5_terms_to_terms(cvc5_res);
}

void
Cvc5Solver::push(uint32_t n_levels)
{
  d_solver->push(n_levels);
}

void
Cvc5Solver::pop(uint32_t n_levels)
{
  d_solver->pop(n_levels);
}

void
Cvc5Solver::print_model()
{
  /* no direct support in the API */
}

void
Cvc5Solver::reset_assertions()
{
  d_solver->resetAssertions();
}

void
Cvc5Solver::set_opt(const std::string& opt, const std::string& value)
{
  d_solver->setOption(opt, value);
}

/* -------------------------------------------------------------------------- */

std::string
Cvc5Solver::get_option_name_incremental() const
{
  return "incremental";
}

std::string
Cvc5Solver::get_option_name_model_gen() const
{
  return "produce-models";
}

std::string
Cvc5Solver::get_option_name_unsat_assumptions() const
{
  return "produce-unsat-assumptions";
}

bool
Cvc5Solver::option_incremental_enabled() const
{
  return d_solver->getOption("incremental") == "true";
}

bool
Cvc5Solver::option_model_gen_enabled() const
{
  return d_solver->getOption("produce-models") == "true";
}

bool
Cvc5Solver::option_unsat_assumptions_enabled() const
{
  return d_solver->getOption("produce-unsat-assumptions") == "true";
}

std::vector<Term>
Cvc5Solver::cvc5_terms_to_terms(std::vector<::cvc5::api::Term>& terms) const
{
  std::vector<Term> res;
  for (::cvc5::api::Term& t : terms)
  {
    res.push_back(std::shared_ptr<Cvc5Term>(new Cvc5Term(d_solver, t)));
  }
  return res;
}

std::vector<::cvc5::api::Term>
Cvc5Solver::terms_to_cvc5_terms(std::vector<Term>& terms) const
{
  std::vector<::cvc5::api::Term> res;
  for (Term& t : terms)
  {
    res.push_back(get_cvc5_term(t));
  }
  return res;
}

/* -------------------------------------------------------------------------- */

// ##### TODO OPS

//  ABSTRACT_VALUE,
//  LAMBDA,
//  WITNESS,
//  CARDINALITY_CONSTRAINT,
//  CARDINALITY_VALUE,
//  HO_APPLY,

//  ## Ints
//  IAND,

//  ## Arithmetic
//  POW,
//  EXPONENTIAL,
//  TO_INTEGER,
//  TO_REAL,

// ## Arithmetic transcendental
//  SINE,
//  COSINE,
//  TANGENT,
//  COSECANT,
//  SECANT,
//  COTANGENT,
//  ARCSINE,
//  ARCCOSINE,
//  ARCTANGENT,
//  ARCCOSECANT,
//  ARCSECANT,
//  ARCCOTANGENT,
//  SQRT,

//  ## Bit-Vectors
//  BITVECTOR_ULTBV,
//  BITVECTOR_SLTBV,
//  BITVECTOR_ITE,
//  INT_TO_BITVECTOR,
//  BITVECTOR_TO_NAT,

//  ## Floating-Points
//  FLOATINGPOINT_TO_FP_GENERIC,

// ## Arrays
//  EQ_RANGE,

//  ## Datatypes
//  APPLY_CONSTRUCTOR,
//  APPLY_SELECTOR,
//  APPLY_TESTER,
//  TUPLE_UPDATE,
//  RECORD_UPDATE,
//  MATCH,
//  MATCH_CASE,
//  MATCH_BIND_CASE,
//  DT_SIZE,

//  ## Separation Logic
//  SEP_NIL,
//  SEP_EMP,
//  SEP_PTO,
//  SEP_STAR,
//  SEP_WAND,

//  ## Sets
//  EMPTYSET,
//  UNION,
//  INTERSECTION,
//  SETMINUS,
//  SUBSET,
//  MEMBER,
//  SINGLETON,
//  INSERT,
//  CARD,
//  COMPLEMENT,
//  UNIVERSE_SET,
//  JOIN,
//  PRODUCT,
//  TRANSPOSE,
//  TCLOSURE,
//  JOIN_IMAGE,
//  IDEN,
//  COMPREHENSION,
//  CHOOSE,
//  IS_SINGLETON,

//  ## Sequences
//  SEQ_CONCAT,
//  SEQ_LENGTH,
//  SEQ_EXTRACT,
//  SEQ_UPDATE,
//  SEQ_AT,
//  SEQ_CONTAINS,
//  SEQ_INDEXOF,
//  SEQ_REPLACE,
//  SEQ_REPLACE_ALL,
//  SEQ_REV,
//  SEQ_PREFIX,
//  SEQ_SUFFIX,
//  SEQ_UNIT,
//  SEQ_NTH,

//  ## Quantifiers
//  INST_CLOSURE,
//  INST_PATTERN,
//  INST_NO_PATTERN,
//  INST_ATTRIBUTE,
//  INST_PATTERN_LIST,

void
Cvc5Solver::init_op_kinds()
{
  d_op_kinds = {
      /* Special Cases */
      {Op::UNDEFINED, ::cvc5::api::Kind::UNDEFINED_KIND},
      {Op::DISTINCT, ::cvc5::api::Kind::DISTINCT},
      {Op::EQUAL, ::cvc5::api::Kind::EQUAL},
      {Op::ITE, ::cvc5::api::Kind::ITE},

      /* Bool */
      {Op::AND, ::cvc5::api::Kind::AND},
      {Op::OR, ::cvc5::api::Kind::OR},
      {Op::NOT, ::cvc5::api::Kind::NOT},
      {Op::XOR, ::cvc5::api::Kind::XOR},
      {Op::IMPLIES, ::cvc5::api::Kind::IMPLIES},

      /* Arrays */
      {Op::ARRAY_SELECT, ::cvc5::api::Kind::SELECT},
      {Op::ARRAY_STORE, ::cvc5::api::Kind::STORE},

      /* BV */
      {Op::BV_EXTRACT, ::cvc5::api::Kind::BITVECTOR_EXTRACT},
      {Op::BV_REPEAT, ::cvc5::api::Kind::BITVECTOR_REPEAT},
      {Op::BV_ROTATE_LEFT, ::cvc5::api::Kind::BITVECTOR_ROTATE_LEFT},
      {Op::BV_ROTATE_RIGHT, ::cvc5::api::Kind::BITVECTOR_ROTATE_RIGHT},
      {Op::BV_SIGN_EXTEND, ::cvc5::api::Kind::BITVECTOR_SIGN_EXTEND},
      {Op::BV_ZERO_EXTEND, ::cvc5::api::Kind::BITVECTOR_ZERO_EXTEND},

      {Op::BV_CONCAT, ::cvc5::api::Kind::BITVECTOR_CONCAT},
      {Op::BV_AND, ::cvc5::api::Kind::BITVECTOR_AND},
      {Op::BV_OR, ::cvc5::api::Kind::BITVECTOR_OR},
      {Op::BV_XOR, ::cvc5::api::Kind::BITVECTOR_XOR},
      {Op::BV_MULT, ::cvc5::api::Kind::BITVECTOR_MULT},
      {Op::BV_ADD, ::cvc5::api::Kind::BITVECTOR_ADD},
      {Op::BV_NOT, ::cvc5::api::Kind::BITVECTOR_NOT},
      {Op::BV_NEG, ::cvc5::api::Kind::BITVECTOR_NEG},
      {Op::BV_NAND, ::cvc5::api::Kind::BITVECTOR_NAND},
      {Op::BV_NOR, ::cvc5::api::Kind::BITVECTOR_NOR},
      {Op::BV_XNOR, ::cvc5::api::Kind::BITVECTOR_XNOR},
      {Op::BV_COMP, ::cvc5::api::Kind::BITVECTOR_COMP},
      {Op::BV_SUB, ::cvc5::api::Kind::BITVECTOR_SUB},
      {Op::BV_UDIV, ::cvc5::api::Kind::BITVECTOR_UDIV},
      {Op::BV_UREM, ::cvc5::api::Kind::BITVECTOR_UREM},
      {Op::BV_UREM, ::cvc5::api::Kind::BITVECTOR_UREM},
      {Op::BV_SDIV, ::cvc5::api::Kind::BITVECTOR_SDIV},
      {Op::BV_SREM, ::cvc5::api::Kind::BITVECTOR_SREM},
      {Op::BV_SMOD, ::cvc5::api::Kind::BITVECTOR_SMOD},
      {Op::BV_SHL, ::cvc5::api::Kind::BITVECTOR_SHL},
      {Op::BV_LSHR, ::cvc5::api::Kind::BITVECTOR_LSHR},
      {Op::BV_ASHR, ::cvc5::api::Kind::BITVECTOR_ASHR},
      {Op::BV_ULT, ::cvc5::api::Kind::BITVECTOR_ULT},
      {Op::BV_ULE, ::cvc5::api::Kind::BITVECTOR_ULE},
      {Op::BV_UGT, ::cvc5::api::Kind::BITVECTOR_UGT},
      {Op::BV_UGE, ::cvc5::api::Kind::BITVECTOR_UGE},
      {Op::BV_SLT, ::cvc5::api::Kind::BITVECTOR_SLT},
      {Op::BV_SLE, ::cvc5::api::Kind::BITVECTOR_SLE},
      {Op::BV_SGT, ::cvc5::api::Kind::BITVECTOR_SGT},
      {Op::BV_SGE, ::cvc5::api::Kind::BITVECTOR_SGE},

      /* FP */
      {Op::FP_ABS, ::cvc5::api::Kind::FLOATINGPOINT_ABS},
      {Op::FP_ADD, ::cvc5::api::Kind::FLOATINGPOINT_ADD},
      {Op::FP_DIV, ::cvc5::api::Kind::FLOATINGPOINT_DIV},
      {Op::FP_EQ, ::cvc5::api::Kind::FLOATINGPOINT_EQ},
      {Op::FP_FMA, ::cvc5::api::Kind::FLOATINGPOINT_FMA},
      {Op::FP_FP, ::cvc5::api::Kind::FLOATINGPOINT_FP},
      {Op::FP_IS_NORMAL, ::cvc5::api::Kind::FLOATINGPOINT_ISN},
      {Op::FP_IS_SUBNORMAL, ::cvc5::api::Kind::FLOATINGPOINT_ISSN},
      {Op::FP_IS_INF, ::cvc5::api::Kind::FLOATINGPOINT_ISINF},
      {Op::FP_IS_NAN, ::cvc5::api::Kind::FLOATINGPOINT_ISNAN},
      {Op::FP_IS_NEG, ::cvc5::api::Kind::FLOATINGPOINT_ISNEG},
      {Op::FP_IS_POS, ::cvc5::api::Kind::FLOATINGPOINT_ISPOS},
      {Op::FP_IS_ZERO, ::cvc5::api::Kind::FLOATINGPOINT_ISZ},
      {Op::FP_LT, ::cvc5::api::Kind::FLOATINGPOINT_LT},
      {Op::FP_LEQ, ::cvc5::api::Kind::FLOATINGPOINT_LEQ},
      {Op::FP_GT, ::cvc5::api::Kind::FLOATINGPOINT_GT},
      {Op::FP_GEQ, ::cvc5::api::Kind::FLOATINGPOINT_GEQ},
      {Op::FP_MAX, ::cvc5::api::Kind::FLOATINGPOINT_MAX},
      {Op::FP_MIN, ::cvc5::api::Kind::FLOATINGPOINT_MIN},
      {Op::FP_MUL, ::cvc5::api::Kind::FLOATINGPOINT_MULT},
      {Op::FP_NEG, ::cvc5::api::Kind::FLOATINGPOINT_NEG},
      {Op::FP_REM, ::cvc5::api::Kind::FLOATINGPOINT_REM},
      {Op::FP_RTI, ::cvc5::api::Kind::FLOATINGPOINT_RTI},
      {Op::FP_SQRT, ::cvc5::api::Kind::FLOATINGPOINT_SQRT},
      {Op::FP_SUB, ::cvc5::api::Kind::FLOATINGPOINT_SUB},
      {Op::FP_TO_FP_FROM_BV,
       ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR},
      {Op::FP_TO_FP_FROM_SBV,
       ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
      {Op::FP_TO_FP_FROM_FP,
       ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT},
      {Op::FP_TO_FP_FROM_UBV,
       ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
      {Op::FP_TO_FP_FROM_REAL, ::cvc5::api::Kind::FLOATINGPOINT_TO_FP_REAL},
      {Op::FP_TO_REAL, ::cvc5::api::Kind::FLOATINGPOINT_TO_REAL},
      {Op::FP_TO_SBV, ::cvc5::api::Kind::FLOATINGPOINT_TO_SBV},
      {Op::FP_TO_UBV, ::cvc5::api::Kind::FLOATINGPOINT_TO_UBV},

      /* Ints */
      {Op::INT_IS_DIV, ::cvc5::api::Kind::DIVISIBLE},
      {Op::INT_NEG, ::cvc5::api::Kind::UMINUS},
      {Op::INT_SUB, ::cvc5::api::Kind::MINUS},
      {Op::INT_ADD, ::cvc5::api::Kind::PLUS},
      {Op::INT_MUL, ::cvc5::api::Kind::MULT},
      {Op::INT_DIV, ::cvc5::api::Kind::INTS_DIVISION},
      {Op::INT_MOD, ::cvc5::api::Kind::INTS_MODULUS},
      {Op::INT_ABS, ::cvc5::api::Kind::ABS},
      {Op::INT_LT, ::cvc5::api::Kind::LT},
      {Op::INT_LTE, ::cvc5::api::Kind::LEQ},
      {Op::INT_GT, ::cvc5::api::Kind::GT},
      {Op::INT_GTE, ::cvc5::api::Kind::GEQ},
      {Op::INT_IS_INT, ::cvc5::api::Kind::IS_INTEGER},

      /* Reals */
      {Op::REAL_NEG, ::cvc5::api::Kind::UMINUS},
      {Op::REAL_SUB, ::cvc5::api::Kind::MINUS},
      {Op::REAL_ADD, ::cvc5::api::Kind::PLUS},
      {Op::REAL_MUL, ::cvc5::api::Kind::MULT},
      {Op::REAL_DIV, ::cvc5::api::Kind::DIVISION},
      {Op::REAL_LT, ::cvc5::api::Kind::LT},
      {Op::REAL_LTE, ::cvc5::api::Kind::LEQ},
      {Op::REAL_GT, ::cvc5::api::Kind::GT},
      {Op::REAL_GTE, ::cvc5::api::Kind::GEQ},
      {Op::REAL_IS_INT, ::cvc5::api::Kind::IS_INTEGER},

      /* Quantifiers */
      {Op::FORALL, ::cvc5::api::Kind::FORALL},
      {Op::EXISTS, ::cvc5::api::Kind::EXISTS},

      /* Strings */
      {Op::STR_CONCAT, ::cvc5::api::Kind::STRING_CONCAT},
      {Op::STR_LEN, ::cvc5::api::Kind::STRING_LENGTH},
      {Op::STR_LT, ::cvc5::api::Kind::STRING_LT},
      {Op::STR_TO_RE, ::cvc5::api::Kind::STRING_TO_REGEXP},
      {Op::STR_IN_RE, ::cvc5::api::Kind::STRING_IN_REGEXP},
      {Op::RE_CONCAT, ::cvc5::api::Kind::REGEXP_CONCAT},
      {Op::RE_UNION, ::cvc5::api::Kind::REGEXP_UNION},
      {Op::RE_INTER, ::cvc5::api::Kind::REGEXP_INTER},
      {Op::RE_STAR, ::cvc5::api::Kind::REGEXP_STAR},
      {Op::STR_LE, ::cvc5::api::Kind::STRING_LEQ},
      {Op::STR_AT, ::cvc5::api::Kind::STRING_CHARAT},
      {Op::STR_SUBSTR, ::cvc5::api::Kind::STRING_SUBSTR},
      {Op::STR_PREFIXOF, ::cvc5::api::Kind::STRING_PREFIX},
      {Op::STR_SUFFIXOF, ::cvc5::api::Kind::STRING_SUFFIX},
      {Op::STR_CONTAINS, ::cvc5::api::Kind::STRING_CONTAINS},
      {Op::STR_INDEXOF, ::cvc5::api::Kind::STRING_INDEXOF},
      {Op::STR_REPLACE, ::cvc5::api::Kind::STRING_REPLACE},
      {Op::STR_REPLACE_ALL, ::cvc5::api::Kind::STRING_REPLACE_ALL},
      {Op::STR_REPLACE_RE, ::cvc5::api::Kind::STRING_REPLACE_RE},
      {Op::STR_REPLACE_RE_ALL, ::cvc5::api::Kind::STRING_REPLACE_RE_ALL},
      {Op::RE_COMP, ::cvc5::api::Kind::REGEXP_COMPLEMENT},
      {Op::RE_DIFF, ::cvc5::api::Kind::REGEXP_DIFF},
      {Op::RE_PLUS, ::cvc5::api::Kind::REGEXP_PLUS},
      {Op::RE_OPT, ::cvc5::api::Kind::REGEXP_OPT},
      {Op::RE_RANGE, ::cvc5::api::Kind::REGEXP_RANGE},
      {Op::RE_POW, ::cvc5::api::Kind::REGEXP_REPEAT},
      {Op::RE_LOOP, ::cvc5::api::Kind::REGEXP_LOOP},
      {Op::STR_IS_DIGIT, ::cvc5::api::Kind::STRING_IS_DIGIT},
      {Op::STR_TO_CODE, ::cvc5::api::Kind::STRING_TO_CODE},
      {Op::STR_FROM_CODE, ::cvc5::api::Kind::STRING_FROM_CODE},
      {Op::STR_TO_INT, ::cvc5::api::Kind::STRING_TO_INT},
      {Op::STR_FROM_INT, ::cvc5::api::Kind::STRING_FROM_INT},

      /* UF */
      {Op::UF_APPLY, ::cvc5::api::Kind::APPLY_UF},

      /* Solver-specific operators */
      {OP_BV_REDOR, ::cvc5::api::Kind::BITVECTOR_REDOR},
      {OP_BV_REDAND, ::cvc5::api::Kind::BITVECTOR_REDAND},
      {OP_STRING_UPDATE, ::cvc5::api::Kind::STRING_UPDATE},
      {OP_STRING_TOLOWER, ::cvc5::api::Kind::STRING_TOLOWER},
      {OP_STRING_TOUPPER, ::cvc5::api::Kind::STRING_TOUPPER},
      {OP_STRING_REV, ::cvc5::api::Kind::STRING_REV},
  };
}

::cvc5::api::Sort&
Cvc5Solver::get_cvc5_sort(Sort sort) const
{
  return static_cast<Cvc5Sort*>(sort.get())->d_sort;
}

::cvc5::api::Term&
Cvc5Solver::get_cvc5_term(Term term) const
{
  return static_cast<Cvc5Term*>(term.get())->d_term;
}

/* -------------------------------------------------------------------------- */
/* Solver-specific operators, SolverManager configuration.                    */
/* -------------------------------------------------------------------------- */

const OpKind Cvc5Solver::OP_BV_REDAND      = "cvc5-OP_BV_REDAND";
const OpKind Cvc5Solver::OP_BV_REDOR       = "cvc5-OP_BV_REDOR";
const OpKind Cvc5Solver::OP_STRING_UPDATE  = "cvc5-OP_STRING_UPDATE";
const OpKind Cvc5Solver::OP_STRING_TOLOWER = "cvc5-OP_STRING_TOLOWER";
const OpKind Cvc5Solver::OP_STRING_TOUPPER = "cvc5-OP_STRING_TOUPPER";
const OpKind Cvc5Solver::OP_STRING_REV     = "cvc5-OP_STRING_REV";

void
Cvc5Solver::configure_smgr(SolverManager* smgr) const
{
  smgr->add_op_kind(OP_BV_REDAND, 1, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_BV_REDOR, 1, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);

  smgr->add_op_kind(OP_STRING_UPDATE,
                    3,
                    0,
                    SORT_STRING,
                    {SORT_STRING, SORT_INT, SORT_STRING},
                    THEORY_STRING);
  smgr->add_op_kind(
      OP_STRING_TOLOWER, 1, 0, SORT_STRING, {SORT_STRING}, THEORY_STRING);
  smgr->add_op_kind(
      OP_STRING_TOUPPER, 1, 0, SORT_STRING, {SORT_STRING}, THEORY_STRING);
  smgr->add_op_kind(
      OP_STRING_REV, 1, 0, SORT_STRING, {SORT_STRING}, THEORY_STRING);
}

/* -------------------------------------------------------------------------- */
/* Solver-specific actions, FSM configuration. */
/* -------------------------------------------------------------------------- */

const ActionKind Cvc5Solver::ACTION_CHECK_ENTAILED = "cvc5-check-entailed";
const ActionKind Cvc5Solver::ACTION_SIMPLIFY       = "cvc5-simplify";

class Cvc5ActionCheckEntailed : public Action
{
 public:
  Cvc5ActionCheckEntailed(SolverManager& smgr)
      : Action(smgr, Cvc5Solver::ACTION_CHECK_ENTAILED, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term(SORT_BOOL, 0)) return false;

    if (d_rng.flip_coin())
    {
      Term term = d_smgr.pick_term(SORT_BOOL, 0);
      _run(term);
    }
    else
    {
      uint32_t n_terms =
          d_rng.pick<uint32_t>(1, MURXLA_CVC5_MAX_N_TERMS_CHECK_ENTAILED);
      std::vector<Term> terms;
      for (uint32_t i = 0; i < n_terms; ++i)
      {
        Term t = d_smgr.pick_term(SORT_BOOL, 0);
        assert(t->get_sort()->get_kind() == SORT_BOOL);
        terms.push_back(t);
      }
      _run(terms);
    }
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS_MIN(1, "", tokens.size());
    if (tokens.size() == 1)
    {
      Term term = d_smgr.get_term(str_to_uint32(tokens[0]));
      MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
      _run(term);
    }
    else
    {
      std::vector<Term> terms;
      uint32_t n_terms = str_to_uint32(tokens[0]);
      for (uint32_t i = 0, idx = 1; i < n_terms; ++i, ++idx)
      {
        uint32_t id = str_to_uint32(tokens[idx]);
        Term term   = d_smgr.get_term(id);
        MURXLA_CHECK_TRACE_TERM(term, id);
        terms.push_back(term);
      }
      _run(terms);
    }
    return 0;
  }

 private:
  void _run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    d_smgr.reset_sat();
    Cvc5Solver& solver          = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::api::Solver* cvc5   = solver.get_solver();
    ::cvc5::api::Term cvc5_term = solver.get_cvc5_term(term);
    assert(!cvc5_term.isNull());
    ::cvc5::api::Result res = cvc5->checkEntailed(cvc5_term);
    assert(!d_rng.pick_with_prob(1) || res == res);
    assert(res != ::cvc5::api::Result());
    assert(!res.isSat());
    assert(!res.isUnsat());
    assert(!res.isSatUnknown());
    if (res.isEntailmentUnknown())
    {
      if (d_rng.pick_with_prob(1))
      {
        (void) res.getUnknownExplanation();
      }
      d_smgr.d_sat_result = Solver::Result::UNKNOWN;
    }
    else if (res.isEntailed())
    {
      d_smgr.d_sat_result = Solver::Result::UNSAT;
    }
    else
    {
      assert(res.isNotEntailed());
      d_smgr.d_sat_result = Solver::Result::SAT;
    }
    d_smgr.d_sat_called = true;
  }

  void _run(std::vector<Term> terms)
  {
    MURXLA_TRACE << get_kind() << " " << terms.size() << terms;
    d_smgr.reset_sat();
    Cvc5Solver& solver        = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::api::Solver* cvc5 = solver.get_solver();
    std::vector<::cvc5::api::Term> cvc5_terms =
        solver.terms_to_cvc5_terms(terms);
    ::cvc5::api::Result res = cvc5->checkEntailed(cvc5_terms);
    assert(!d_rng.pick_with_prob(1) || res == res);
    assert(res != ::cvc5::api::Result());
    assert(!res.isSat());
    assert(!res.isUnsat());
    assert(!res.isSatUnknown());
    if (res.isEntailmentUnknown())
    {
      if (d_rng.pick_with_prob(1))
      {
        (void) res.getUnknownExplanation();
      }
      d_smgr.d_sat_result = Solver::Result::UNKNOWN;
    }
    else if (res.isEntailed())
    {
      d_smgr.d_sat_result = Solver::Result::UNSAT;
    }
    else
    {
      assert(res.isNotEntailed());
      d_smgr.d_sat_result = Solver::Result::SAT;
    }
    d_smgr.d_sat_called = true;
  }
};

class Cvc5ActionSimplify : public Action
{
 public:
  Cvc5ActionSimplify(SolverManager& smgr)
      : Action(smgr, Cvc5Solver::ACTION_SIMPLIFY, true)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    if (!d_smgr.has_term()) return false;
    Term term = d_smgr.pick_term();
    _run(term);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    MURXLA_CHECK_TRACE_NTOKENS(1, tokens.size());
    Term term = d_smgr.get_term(str_to_uint32(tokens[0]));
    MURXLA_CHECK_TRACE_TERM(term, tokens[0]);
    return _run(term);
  }

 private:
  uint64_t _run(Term term)
  {
    MURXLA_TRACE << get_kind() << " " << term;
    d_smgr.reset_sat();
    Cvc5Solver& solver         = static_cast<Cvc5Solver&>(d_smgr.get_solver());
    ::cvc5::api::Solver* cvc5  = solver.get_solver();
    ::cvc5::api::Term cvc5_res = cvc5->simplify(solver.get_cvc5_term(term));
    assert(!cvc5_res.isNull());
    Term res  = std::make_shared<Cvc5Term>(cvc5, cvc5_res);
    Sort sort = term->get_sort();
    assert (sort != nullptr);
    /* Note: The simplified term 'res' may or may not be already in the term
     * DB. However, we assume the same level for 'res' as the original term
     * since we can't always compute the exact level. */
    if (res->get_levels().empty())
    {
      res->set_levels(term->get_levels());
    }
    d_smgr.add_term(res, sort->get_kind());
    MURXLA_TRACE_RETURN << res;
    return res->get_id();
  }
};

/* -------------------------------------------------------------------------- */

void
Cvc5Solver::configure_fsm(FSM* fsm) const
{
  State* s_sat = fsm->get_state(State::CHECK_SAT);

  // Solver::simplify(const Term& term)
  auto a_simplify = fsm->new_action<Cvc5ActionSimplify>();
  fsm->add_action_to_all_states(a_simplify, 100, {State::NEW, State::DELETE});

  // Solver::checkEntailed(Term term)
  // Solver::checkEntailed(std::vector<Term> terms)
  auto a_check_entailed = fsm->new_action<Cvc5ActionCheckEntailed>();
  s_sat->add_action(a_check_entailed, 1);
}
}  // namespace cvc5
}  // namespace murxla

#endif
