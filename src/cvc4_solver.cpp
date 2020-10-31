#ifdef SMTMBT_USE_CVC4

#include "cvc4_solver.hpp"

#include <cassert>

#include "config.hpp"
#include "cvc4/api/cvc4cpp.h"
#include "theory.hpp"
#include "util.hpp"

using namespace CVC4;

namespace smtmbt {
namespace cvc4 {

#define SMTMBT_CVC4_MAX_N_TERMS_CHECK_ENTAILED 5

/* -------------------------------------------------------------------------- */
/* CVC4Sort                                                                   */
/* -------------------------------------------------------------------------- */

size_t
CVC4Sort::hash() const
{
  return CVC4::api::SortHashFunction()(d_sort);
}

bool
CVC4Sort::equals(const Sort& other) const
{
  CVC4Sort* cvc4_sort = dynamic_cast<CVC4Sort*>(other.get());
  if (cvc4_sort)
  {
    return d_sort == cvc4_sort->d_sort;
  }
  return false;
}

bool
CVC4Sort::is_array() const
{
  return d_sort.isArray();
}

bool
CVC4Sort::is_bool() const
{
  return d_sort.isBoolean();
}

bool
CVC4Sort::is_bv() const
{
  return d_sort.isBitVector();
}

bool
CVC4Sort::is_fp() const
{
  return d_sort.isFloatingPoint();
}

bool
CVC4Sort::is_fun() const
{
  return d_sort.isFunction();
}

bool
CVC4Sort::is_int() const
{
  return d_sort.isInteger();
}

bool
CVC4Sort::is_real() const
{
  return d_sort.isReal();
}

bool
CVC4Sort::is_rm() const
{
  return d_sort.isRoundingMode();
}

bool
CVC4Sort::is_string() const
{
  return d_sort.isString();
}

bool
CVC4Sort::is_reglan() const
{
  return d_sort.isRegExp();
}

uint32_t
CVC4Sort::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = d_sort.getBVSize();
  assert(res);
  return res;
}

uint32_t
CVC4Sort::get_fp_exp_size() const
{
  assert(is_fp());
  uint32_t res = d_sort.getFPExponentSize();
  assert(res);
  return res;
}

uint32_t
CVC4Sort::get_fp_sig_size() const
{
  assert(is_fp());
  uint32_t res = d_sort.getFPSignificandSize();
  assert(res);
  return res;
}

/* -------------------------------------------------------------------------- */
/* CVC4Term                                                                   */
/* -------------------------------------------------------------------------- */

size_t
CVC4Term::hash() const
{
  return CVC4::api::TermHashFunction()(d_term);
}

bool
CVC4Term::equals(const Term& other) const
{
  CVC4Term* cvc4_term = dynamic_cast<CVC4Term*>(other.get());
  if (cvc4_term) return d_term == cvc4_term->d_term;
  return false;
}

bool
CVC4Term::is_array() const
{
  return get_sort()->is_array();
}

bool
CVC4Term::is_bool() const
{
  return get_sort()->is_bool();
}

bool
CVC4Term::is_bv() const
{
  return get_sort()->is_bv();
}

bool
CVC4Term::is_fp() const
{
  return get_sort()->is_fp();
}

bool
CVC4Term::is_fun() const
{
  return get_sort()->is_fun();
}

bool
CVC4Term::is_int() const
{
  return get_sort()->is_int();
}

bool
CVC4Term::is_real() const
{
  return get_sort()->is_real();
}

bool
CVC4Term::is_rm() const
{
  return get_sort()->is_rm();
}

bool
CVC4Term::is_string() const
{
  return get_sort()->is_string();
}

bool
CVC4Term::is_reglan() const
{
  return get_sort()->is_reglan();
}

/* -------------------------------------------------------------------------- */
/* CVC4Solver                                                                 */
/* -------------------------------------------------------------------------- */

const Solver::SpecialValueKind CVC4Solver::SPECIAL_VALUE_PI = "cvc4-pi";

OpKindSet
CVC4Solver::get_unsupported_op_kinds() const
{
  return {
      Op::IFF,
  };
}

void
CVC4Solver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = new api::Solver();
  init_op_kinds();
  d_solver->setOption("fp-exp", "true");
  d_solver->setOption("strings-exp", "true");

  add_special_value(SORT_REAL, SPECIAL_VALUE_PI);
}

void
CVC4Solver::delete_solver()
{
  assert(d_solver != nullptr);
  delete d_solver;
  d_solver = nullptr;
}

CVC4::api::Solver*
CVC4Solver::get_solver()
{
  return d_solver;
}

bool
CVC4Solver::is_initialized() const
{
  return d_solver != nullptr;
}

bool
CVC4Solver::check_unsat_assumption(const Term& t) const
{
  return !get_cvc4_term(t).isNull();
}

/* -------------------------------------------------------------------------- */

Sort
CVC4Solver::mk_sort(SortKind kind)
{
  CVC4::api::Sort cvc4_res;
  switch (kind)
  {
    case SORT_BOOL: cvc4_res = d_solver->getBooleanSort(); break;
    case SORT_INT: cvc4_res = d_solver->getIntegerSort(); break;
    case SORT_REAL: cvc4_res = d_solver->getRealSort(); break;
    case SORT_RM: cvc4_res = d_solver->getRoundingModeSort(); break;
    case SORT_STRING: cvc4_res = d_solver->getStringSort(); break;
    case SORT_REGLAN: cvc4_res = d_solver->getRegExpSort(); break;

    default: assert(false);
  }
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  return std::shared_ptr<CVC4Sort>(new CVC4Sort(d_solver, cvc4_res));
}

Sort
CVC4Solver::mk_sort(SortKind kind, uint32_t size)
{
  CVC4::api::Sort cvc4_res;
  switch (kind)
  {
    case SORT_BV: cvc4_res = d_solver->mkBitVectorSort(size); break;

    default: assert(false);
  }
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  std::shared_ptr<CVC4Sort> res(new CVC4Sort(d_solver, cvc4_res));
  assert(res);
  return res;
}

Sort
CVC4Solver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  CVC4::api::Sort cvc4_res;
  switch (kind)
  {
    case SORT_FP: cvc4_res = d_solver->mkFloatingPointSort(esize, ssize); break;

    default: assert(false);
  }
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  std::shared_ptr<CVC4Sort> res(new CVC4Sort(d_solver, cvc4_res));
  assert(res);
  return res;
}

Sort
CVC4Solver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  CVC4::api::Sort cvc4_res;

  switch (kind)
  {
    case SORT_ARRAY:
      cvc4_res = d_solver->mkArraySort(get_cvc4_sort(sorts[0]),
                                       get_cvc4_sort(sorts[1]));
      break;

    case SORT_FUN:
    {
      std::vector<CVC4::api::Sort> domain;
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        domain.push_back(get_cvc4_sort(*it));
      }
      CVC4::api::Sort codomain = get_cvc4_sort(sorts.back());

      cvc4_res = d_solver->mkFunctionSort(domain, codomain);
      break;
    }

    default: assert(false);
  }
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  std::shared_ptr<CVC4Sort> res(new CVC4Sort(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_const(Sort sort, const std::string& name)
{
  CVC4::api::Term cvc4_res = d_solver->mkConst(get_cvc4_sort(sort), name);
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  return std::shared_ptr<CVC4Term>(new CVC4Term(d_solver, cvc4_res));
}

Term
CVC4Solver::mk_var(Sort sort, const std::string& name)
{
  CVC4::api::Term cvc4_res = d_solver->mkVar(get_cvc4_sort(sort), name);
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  return std::shared_ptr<CVC4Term>(new CVC4Term(d_solver, cvc4_res));
}

Term
CVC4Solver::mk_value(Sort sort, bool value)
{
  assert(sort->is_bool());

  CVC4::api::Term cvc4_res;

  if (d_rng.flip_coin())
  {
    cvc4_res = value ? d_solver->mkTrue() : d_solver->mkFalse();
  }
  else
  {
    cvc4_res = d_solver->mkBoolean(value);
  }
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  std::shared_ptr<CVC4Term> res(new CVC4Term(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_value(Sort sort, std::string value)
{
  CVC4::api::Term cvc4_res;
  CVC4::api::Sort cvc4_sort = get_cvc4_sort(sort);
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
        cvc4_res = d_solver->mkReal(val64);
      }
      else
      {
        cvc4_res = d_solver->mkReal(value);
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
          cvc4_res = d_solver->mkReal(val64);
        }
        else
        {
          cvc4_res = d_solver->mkReal(value);
        }
      }
      else
      {
        cvc4_res = d_solver->mkReal(value);
      }
      break;

    case SORT_REGLAN:
    case SORT_STRING:
      // TODO: test more mkString functions
      cvc4_res = d_solver->mkString(value);
      break;

    default: assert(false);
  }
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  std::shared_ptr<CVC4Term> res(new CVC4Term(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_value(Sort sort, std::string num, std::string den)
{
  assert(sort->is_real());
  CVC4::api::Term cvc4_res;

  cvc4_res = d_solver->mkReal(
      static_cast<int64_t>(strtoull(num.c_str(), nullptr, 10)),
      static_cast<int64_t>(strtoull(den.c_str(), nullptr, 10)));
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  std::shared_ptr<CVC4Term> res(new CVC4Term(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_value(Sort sort, std::string value, Base base)
{
  assert(sort->is_bv());

  CVC4::api::Term cvc4_res;
  CVC4::api::Sort cvc4_sort = get_cvc4_sort(sort);
  uint32_t bw               = sort->get_bv_size();

  switch (base)
  {
    case DEC:
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc4_res =
            d_solver->mkBitVector(bw, strtoull(value.c_str(), nullptr, 10));
      }
      else
      {
        cvc4_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bw, value, 10)
                       : d_solver->mkBitVector(bw, value.c_str(), 10);
      }
      break;

    case HEX:
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc4_res =
            d_solver->mkBitVector(bw, strtoull(value.c_str(), nullptr, 16));
      }
      else
      {
        cvc4_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bw, value, 16)
                       : d_solver->mkBitVector(bw, value.c_str(), 16);
      }
      break;

    default:
      assert(base == BIN);
      if (bw <= 64 && d_rng.flip_coin())
      {
        cvc4_res =
            d_solver->mkBitVector(bw, strtoull(value.c_str(), nullptr, 2));
      }
      else
      {
        cvc4_res = d_rng.flip_coin() ? d_solver->mkBitVector(value, 2)
                                     : d_solver->mkBitVector(value.c_str(), 2);
      }
  }
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  std::shared_ptr<CVC4Term> res(new CVC4Term(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_special_value(Sort sort, const SpecialValueKind& value)
{
  CVC4::api::Term cvc4_res;

  switch (sort->get_kind())
  {
    case SORT_BV:
    {
      uint32_t bw = sort->get_bv_size();
      if (value == SPECIAL_VALUE_BV_ZERO)
      {
        cvc4_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bv_special_value_zero_str(bw), 2)
                       : d_solver->mkBitVector(
                           bv_special_value_zero_str(bw).c_str(), 2);
      }
      else if (value == SPECIAL_VALUE_BV_ONE)
      {
        cvc4_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bv_special_value_one_str(bw), 2)
                       : d_solver->mkBitVector(
                           bv_special_value_one_str(bw).c_str(), 2);
      }
      else if (value == SPECIAL_VALUE_BV_ONES)
      {
        cvc4_res = d_rng.flip_coin()
                       ? d_solver->mkBitVector(bv_special_value_ones_str(bw), 2)
                       : d_solver->mkBitVector(
                           bv_special_value_ones_str(bw).c_str(), 2);
      }
      else if (value == SPECIAL_VALUE_BV_MIN_SIGNED)
      {
        cvc4_res =
            d_rng.flip_coin()
                ? d_solver->mkBitVector(bv_special_value_min_signed_str(bw), 2)
                : d_solver->mkBitVector(
                    bv_special_value_min_signed_str(bw).c_str(), 2);
      }
      else
      {
        assert(value == SPECIAL_VALUE_BV_MAX_SIGNED);
        cvc4_res =
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
        cvc4_res = d_solver->mkPosInf(ew, sw);
      }
      else if (value == SPECIAL_VALUE_FP_NEG_INF)
      {
        cvc4_res = d_solver->mkNegInf(ew, sw);
      }
      else if (value == SPECIAL_VALUE_FP_POS_ZERO)
      {
        cvc4_res = d_solver->mkPosZero(ew, sw);
      }
      else if (value == SPECIAL_VALUE_FP_NEG_ZERO)
      {
        cvc4_res = d_solver->mkNegZero(ew, sw);
      }
      else
      {
        assert(value == SPECIAL_VALUE_FP_NAN);
        cvc4_res = d_solver->mkNaN(ew, sw);
      }
    }
    break;

    case SORT_RM:
      if (value == SPECIAL_VALUE_RM_RNE)
      {
        cvc4_res = d_solver->mkRoundingMode(
            CVC4::api::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
      }
      else if (value == SPECIAL_VALUE_RM_RNA)
      {
        cvc4_res = d_solver->mkRoundingMode(
            CVC4::api::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY);
      }
      else if (value == SPECIAL_VALUE_RM_RTN)
      {
        cvc4_res = d_solver->mkRoundingMode(
            CVC4::api::RoundingMode::ROUND_TOWARD_NEGATIVE);
      }
      else if (value == SPECIAL_VALUE_RM_RTP)
      {
        cvc4_res = d_solver->mkRoundingMode(
            CVC4::api::RoundingMode::ROUND_TOWARD_POSITIVE);
      }
      else
      {
        assert(value == SPECIAL_VALUE_RM_RTZ);
        cvc4_res = d_solver->mkRoundingMode(
            CVC4::api::RoundingMode::ROUND_TOWARD_ZERO);
      }
      break;

    case SORT_REAL:
      assert(value == SPECIAL_VALUE_PI);
      cvc4_res = d_solver->mkPi();
      break;

    case SORT_REGLAN:
      if (value == SPECIAL_VALUE_RE_NONE)
      {
        cvc4_res = d_solver->mkRegexpEmpty();
      }
      else if (value == SPECIAL_VALUE_RE_ALL)
      {
        cvc4_res =
            d_solver->mkTerm(api::REGEXP_STAR, d_solver->mkRegexpSigma());
      }
      else
      {
        assert(value == SPECIAL_VALUE_RE_ALLCHAR);
        cvc4_res = d_solver->mkRegexpSigma();
      }
      break;

    default: assert(false);
  }
  std::shared_ptr<CVC4Term> res(new CVC4Term(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_term(const OpKind& kind,
                    std::vector<Term>& args,
                    std::vector<uint32_t>& params)
{
  assert(d_kinds.find(kind) != d_kinds.end());

  CVC4::api::Term cvc4_res;
  CVC4::api::Kind cvc4_kind = d_kinds.at(kind);
  CVC4::api::Op cvc4_opterm;

  int32_t n_args    = args.size();
  uint32_t n_params = params.size();

  if (kind == Op::FORALL || kind == Op::EXISTS)
  {
    assert(args.size() >= 2);
    std::vector<api::Term> vars;
    for (size_t i = 0; i < args.size() - 1; ++i)
    {
      vars.push_back(get_cvc4_term(args[i]));
    }
    api::Term bvl  = d_solver->mkTerm(api::Kind::BOUND_VAR_LIST, vars);
    api::Term body = get_cvc4_term(args.back());
    cvc4_res       = d_solver->mkTerm(cvc4_kind, bvl, body);
    goto DONE;
  }

  /* create Op for indexed operators */
  switch (n_params)
  {
    case 1:
    {
      cvc4_opterm = d_solver->mkOp(cvc4_kind, params[0]);
      assert(!cvc4_opterm.isNull());
      assert(!d_rng.pick_with_prob(1) || cvc4_opterm == cvc4_opterm);
      assert(!d_rng.pick_with_prob(1) || !(cvc4_opterm != cvc4_opterm));
      assert(cvc4_opterm.isIndexed());
      assert(cvc4_opterm.getKind() == cvc4_kind);
      uint32_t idx;
      if (kind == Op::INT_IS_DIV)
      {
        std::string sidx = cvc4_opterm.getIndices<std::string>();
        /* we only generate 32 bit indices, so this shouldn't throw */
        idx = str_to_uint32(sidx);
      }
      else
      {
        idx = cvc4_opterm.getIndices<uint32_t>();
      }
      assert(idx == params[0]);
      break;
    }
    case 2:
    {
      cvc4_opterm = d_solver->mkOp(cvc4_kind, params[0], params[1]);
      assert(!cvc4_opterm.isNull());
      assert(!d_rng.pick_with_prob(1) || cvc4_opterm == cvc4_opterm);
      assert(!d_rng.pick_with_prob(1) || !(cvc4_opterm != cvc4_opterm));
      assert(cvc4_opterm.isIndexed());
      assert(cvc4_opterm.getKind() == cvc4_kind);
      std::pair<uint32_t, uint32_t> indices =
          cvc4_opterm.getIndices<std::pair<uint32_t, uint32_t>>();
      assert(indices.first == params[0]);
      assert(indices.second == params[1]);
      break;
    }
    default: assert(n_params == 0);
  }

  /* use vector with 50% probability */
  if (d_rng.flip_coin()) n_args = SMTMBT_MK_TERM_N_ARGS_BIN;

  /* create term */
  switch (n_args)
  {
    case 0:
      cvc4_res = n_params ? d_solver->mkTerm(cvc4_opterm)
                          : d_solver->mkTerm(cvc4_kind);
      break;

    case 1:
      if (kind == Op::NOT && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).notTerm();
      }
      else
      {
        cvc4_res = n_params
                       ? d_solver->mkTerm(cvc4_opterm, get_cvc4_term(args[0]))
                       : d_solver->mkTerm(cvc4_kind, get_cvc4_term(args[0]));
      }
      break;

    case 2:
      if (kind == Op::AND && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).andTerm(get_cvc4_term(args[1]));
      }
      else if (kind == Op::OR && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).orTerm(get_cvc4_term(args[1]));
      }
      else if (kind == Op::XOR && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).xorTerm(get_cvc4_term(args[1]));
      }
      else if (kind == Op::EQUAL && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).eqTerm(get_cvc4_term(args[1]));
      }
      else if (kind == Op::IMPLIES && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).impTerm(get_cvc4_term(args[1]));
      }
      else
      {
        cvc4_res =
            n_params
                ? d_solver->mkTerm(
                    cvc4_opterm, get_cvc4_term(args[0]), get_cvc4_term(args[1]))
                : d_solver->mkTerm(
                    cvc4_kind, get_cvc4_term(args[0]), get_cvc4_term(args[1]));
      }
      break;

    case 3:
      if (kind == Op::ITE && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).iteTerm(get_cvc4_term(args[1]),
                                                  get_cvc4_term(args[2]));
      }
      else
      {
        cvc4_res = n_params ? d_solver->mkTerm(cvc4_opterm,
                                               get_cvc4_term(args[0]),
                                               get_cvc4_term(args[1]),
                                               get_cvc4_term(args[2]))
                            : d_solver->mkTerm(cvc4_kind,
                                               get_cvc4_term(args[0]),
                                               get_cvc4_term(args[1]),
                                               get_cvc4_term(args[2]));
      }
      break;

    default:
      assert(n_args == SMTMBT_MK_TERM_N_ARGS_BIN || n_args > 3);
      std::vector<CVC4::api::Term> cvc4_args;
      cvc4_args = terms_to_cvc4_terms(args);
      cvc4_res = n_params ? d_solver->mkTerm(cvc4_opterm, cvc4_args)
                          : d_solver->mkTerm(cvc4_kind, cvc4_args);
  }
DONE:
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  assert(cvc4_kind == cvc4_res.getKind()
         || (cvc4_res.getSort().isBoolean()
             && cvc4_res.getKind() == CVC4::api::Kind::AND));
  return std::shared_ptr<CVC4Term>(new CVC4Term(d_solver, cvc4_res));
}

Sort
CVC4Solver::get_sort(Term term, SortKind sort_kind) const
{
  (void) sort_kind;
  CVC4::api::Term cvc4_term = get_cvc4_term(term);
  return std::shared_ptr<CVC4Sort>(new CVC4Sort(d_solver, cvc4_term.getSort()));
}

void
CVC4Solver::assert_formula(const Term& t)
{
  d_solver->assertFormula(get_cvc4_term(t));
}

Solver::Result
CVC4Solver::check_sat()
{
  CVC4::api::Result res = d_solver->checkSat();
  assert(res != CVC4::api::Result());
  assert(!d_rng.pick_with_prob(1) || res == res);
  if (res.isSat()) return Result::SAT;
  if (res.isUnsat()) return Result::UNSAT;
  assert(res.isSatUnknown());
  if (d_rng.pick_with_prob(1))
  {
    std::string expl = res.getUnknownExplanation();
  }
  return Result::UNKNOWN;
}

Solver::Result
CVC4Solver::check_sat_assuming(std::vector<Term>& assumptions)
{
  CVC4::api::Result res;
  std::vector<CVC4::api::Term> cvc4_assumptions =
      terms_to_cvc4_terms(assumptions);

  assert(assumptions.size() == cvc4_assumptions.size());

  res = cvc4_assumptions.size() == 1 && d_rng.flip_coin()
            ? d_solver->checkSatAssuming(cvc4_assumptions[0])
            : d_solver->checkSatAssuming(cvc4_assumptions);
  assert(!d_rng.pick_with_prob(1) || res == res);
  assert(res != CVC4::api::Result());
  assert(!res.isEntailed());
  assert(!res.isNotEntailed());
  assert(!res.isEntailmentUnknown());
  if (res.isSat()) return Result::SAT;
  if (res.isUnsat()) return Result::UNSAT;
  assert(res.isSatUnknown());
  if (d_rng.pick_with_prob(1))
  {
    std::string expl = res.getUnknownExplanation();
  }
  return Result::UNKNOWN;
}

std::vector<Term>
CVC4Solver::get_unsat_assumptions()
{
  std::vector<Term> res;
  std::vector<CVC4::api::Term> cvc4_res = d_solver->getUnsatAssumptions();
  return cvc4_terms_to_terms(cvc4_res);
}

std::vector<Term>
CVC4Solver::get_value(std::vector<Term>& terms)
{
  std::vector<Term> res;
  std::vector<CVC4::api::Term> cvc4_res;
  std::vector<CVC4::api::Term> cvc4_terms = terms_to_cvc4_terms(terms);

  if (d_rng.flip_coin())
  {
    cvc4_res = d_solver->getValue(cvc4_terms);
  }
  else
  {
    for (CVC4::api::Term& t : cvc4_terms)
    {
      cvc4_res.push_back(d_solver->getValue(t));
    }
  }
  return cvc4_terms_to_terms(cvc4_res);
}

void
CVC4Solver::push(uint32_t n_levels)
{
  d_solver->push(n_levels);
}

void
CVC4Solver::pop(uint32_t n_levels)
{
  d_solver->pop(n_levels);
}

void
CVC4Solver::print_model()
{
  d_solver->printModel(std::cout);
}

void
CVC4Solver::reset_assertions()
{
  d_solver->resetAssertions();
}

void
CVC4Solver::set_opt(const std::string& opt, const std::string& value)
{
  d_solver->setOption(opt, value);
}

/* -------------------------------------------------------------------------- */

std::string
CVC4Solver::get_option_name_incremental() const
{
  return "incremental";
}

std::string
CVC4Solver::get_option_name_model_gen() const
{
  return "produce-models";
}

std::string
CVC4Solver::get_option_name_unsat_assumptions() const
{
  return "produce-unsat-assumptions";
}

bool
CVC4Solver::option_incremental_enabled() const
{
  return d_solver->getOption("incremental") == "true";
}

bool
CVC4Solver::option_model_gen_enabled() const
{
  return d_solver->getOption("produce-models") == "true";
}

bool
CVC4Solver::option_unsat_assumptions_enabled() const
{
  return d_solver->getOption("produce-unsat-assumptions") == "true";
}

std::vector<Term>
CVC4Solver::cvc4_terms_to_terms(std::vector<CVC4::api::Term>& terms) const
{
  std::vector<Term> res;
  for (CVC4::api::Term& t : terms)
  {
    res.push_back(std::shared_ptr<CVC4Term>(new CVC4Term(d_solver, t)));
  }
  return res;
}

std::vector<CVC4::api::Term>
CVC4Solver::terms_to_cvc4_terms(std::vector<Term>& terms) const
{
  std::vector<CVC4::api::Term> res;
  for (Term& t : terms)
  {
    res.push_back(get_cvc4_term(t));
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
CVC4Solver::init_op_kinds()
{
  d_kinds = {
      /* Special Cases */
      {Op::UNDEFINED, CVC4::api::Kind::UNDEFINED_KIND},
      {Op::DISTINCT, CVC4::api::Kind::DISTINCT},
      {Op::EQUAL, CVC4::api::Kind::EQUAL},
      {Op::ITE, CVC4::api::Kind::ITE},

      /* Bool */
      {Op::AND, CVC4::api::Kind::AND},
      {Op::OR, CVC4::api::Kind::OR},
      {Op::NOT, CVC4::api::Kind::NOT},
      {Op::XOR, CVC4::api::Kind::XOR},
      {Op::IMPLIES, CVC4::api::Kind::IMPLIES},

      /* Arrays */
      {Op::ARRAY_SELECT, CVC4::api::Kind::SELECT},
      {Op::ARRAY_STORE, CVC4::api::Kind::STORE},

      /* BV */
      {Op::BV_EXTRACT, CVC4::api::Kind::BITVECTOR_EXTRACT},
      {Op::BV_REPEAT, CVC4::api::Kind::BITVECTOR_REPEAT},
      {Op::BV_ROTATE_LEFT, CVC4::api::Kind::BITVECTOR_ROTATE_LEFT},
      {Op::BV_ROTATE_RIGHT, CVC4::api::Kind::BITVECTOR_ROTATE_RIGHT},
      {Op::BV_SIGN_EXTEND, CVC4::api::Kind::BITVECTOR_SIGN_EXTEND},
      {Op::BV_ZERO_EXTEND, CVC4::api::Kind::BITVECTOR_ZERO_EXTEND},

      {Op::BV_CONCAT, CVC4::api::Kind::BITVECTOR_CONCAT},
      {Op::BV_AND, CVC4::api::Kind::BITVECTOR_AND},
      {Op::BV_OR, CVC4::api::Kind::BITVECTOR_OR},
      {Op::BV_XOR, CVC4::api::Kind::BITVECTOR_XOR},
      {Op::BV_MULT, CVC4::api::Kind::BITVECTOR_MULT},
      {Op::BV_ADD, CVC4::api::Kind::BITVECTOR_PLUS},
      {Op::BV_NOT, CVC4::api::Kind::BITVECTOR_NOT},
      {Op::BV_NEG, CVC4::api::Kind::BITVECTOR_NEG},
      {Op::BV_NAND, CVC4::api::Kind::BITVECTOR_NAND},
      {Op::BV_NOR, CVC4::api::Kind::BITVECTOR_NOR},
      {Op::BV_XNOR, CVC4::api::Kind::BITVECTOR_XNOR},
      {Op::BV_COMP, CVC4::api::Kind::BITVECTOR_COMP},
      {Op::BV_SUB, CVC4::api::Kind::BITVECTOR_SUB},
      {Op::BV_UDIV, CVC4::api::Kind::BITVECTOR_UDIV},
      {Op::BV_UREM, CVC4::api::Kind::BITVECTOR_UREM},
      {Op::BV_UREM, CVC4::api::Kind::BITVECTOR_UREM},
      {Op::BV_SDIV, CVC4::api::Kind::BITVECTOR_SDIV},
      {Op::BV_SREM, CVC4::api::Kind::BITVECTOR_SREM},
      {Op::BV_SMOD, CVC4::api::Kind::BITVECTOR_SMOD},
      {Op::BV_SHL, CVC4::api::Kind::BITVECTOR_SHL},
      {Op::BV_LSHR, CVC4::api::Kind::BITVECTOR_LSHR},
      {Op::BV_ASHR, CVC4::api::Kind::BITVECTOR_ASHR},
      {Op::BV_ULT, CVC4::api::Kind::BITVECTOR_ULT},
      {Op::BV_ULE, CVC4::api::Kind::BITVECTOR_ULE},
      {Op::BV_UGT, CVC4::api::Kind::BITVECTOR_UGT},
      {Op::BV_UGE, CVC4::api::Kind::BITVECTOR_UGE},
      {Op::BV_SLT, CVC4::api::Kind::BITVECTOR_SLT},
      {Op::BV_SLE, CVC4::api::Kind::BITVECTOR_SLE},
      {Op::BV_SGT, CVC4::api::Kind::BITVECTOR_SGT},
      {Op::BV_SGE, CVC4::api::Kind::BITVECTOR_SGE},

      /* FP */
      {Op::FP_ABS, CVC4::api::Kind::FLOATINGPOINT_ABS},
      {Op::FP_ADD, CVC4::api::Kind::FLOATINGPOINT_PLUS},
      {Op::FP_DIV, CVC4::api::Kind::FLOATINGPOINT_DIV},
      {Op::FP_EQ, CVC4::api::Kind::FLOATINGPOINT_EQ},
      {Op::FP_FMA, CVC4::api::Kind::FLOATINGPOINT_FMA},
      {Op::FP_FP, CVC4::api::Kind::FLOATINGPOINT_FP},
      {Op::FP_IS_NORMAL, CVC4::api::Kind::FLOATINGPOINT_ISN},
      {Op::FP_IS_SUBNORMAL, CVC4::api::Kind::FLOATINGPOINT_ISSN},
      {Op::FP_IS_INF, CVC4::api::Kind::FLOATINGPOINT_ISINF},
      {Op::FP_IS_NAN, CVC4::api::Kind::FLOATINGPOINT_ISNAN},
      {Op::FP_IS_NEG, CVC4::api::Kind::FLOATINGPOINT_ISNEG},
      {Op::FP_IS_POS, CVC4::api::Kind::FLOATINGPOINT_ISPOS},
      {Op::FP_IS_ZERO, CVC4::api::Kind::FLOATINGPOINT_ISZ},
      {Op::FP_LT, CVC4::api::Kind::FLOATINGPOINT_LT},
      {Op::FP_LEQ, CVC4::api::Kind::FLOATINGPOINT_LEQ},
      {Op::FP_GT, CVC4::api::Kind::FLOATINGPOINT_GT},
      {Op::FP_GEQ, CVC4::api::Kind::FLOATINGPOINT_GEQ},
      {Op::FP_MAX, CVC4::api::Kind::FLOATINGPOINT_MAX},
      {Op::FP_MIN, CVC4::api::Kind::FLOATINGPOINT_MIN},
      {Op::FP_MUL, CVC4::api::Kind::FLOATINGPOINT_MULT},
      {Op::FP_NEG, CVC4::api::Kind::FLOATINGPOINT_NEG},
      {Op::FP_REM, CVC4::api::Kind::FLOATINGPOINT_REM},
      {Op::FP_RTI, CVC4::api::Kind::FLOATINGPOINT_RTI},
      {Op::FP_SQRT, CVC4::api::Kind::FLOATINGPOINT_SQRT},
      {Op::FP_SUB, CVC4::api::Kind::FLOATINGPOINT_SUB},
      {Op::FP_TO_FP_FROM_BV,
       CVC4::api::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR},
      {Op::FP_TO_FP_FROM_INT_BV,
       CVC4::api::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
      {Op::FP_TO_FP_FROM_FP,
       CVC4::api::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT},
      {Op::FP_TO_FP_FROM_UINT_BV,
       CVC4::api::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
      {Op::FP_TO_FP_FROM_REAL, CVC4::api::Kind::FLOATINGPOINT_TO_FP_REAL},
      {Op::FP_TO_REAL, CVC4::api::Kind::FLOATINGPOINT_TO_REAL},
      {Op::FP_TO_SBV, CVC4::api::Kind::FLOATINGPOINT_TO_SBV},
      {Op::FP_TO_UBV, CVC4::api::Kind::FLOATINGPOINT_TO_UBV},

      /* Ints */
      {Op::INT_IS_DIV, CVC4::api::Kind::DIVISIBLE},
      {Op::INT_NEG, CVC4::api::Kind::UMINUS},
      {Op::INT_SUB, CVC4::api::Kind::MINUS},
      {Op::INT_ADD, CVC4::api::Kind::PLUS},
      {Op::INT_MUL, CVC4::api::Kind::MULT},
      {Op::INT_DIV, CVC4::api::Kind::INTS_DIVISION},
      {Op::INT_MOD, CVC4::api::Kind::INTS_MODULUS},
      {Op::INT_ABS, CVC4::api::Kind::ABS},
      {Op::INT_LT, CVC4::api::Kind::LT},
      {Op::INT_LTE, CVC4::api::Kind::LEQ},
      {Op::INT_GT, CVC4::api::Kind::GT},
      {Op::INT_GTE, CVC4::api::Kind::GEQ},
      {Op::INT_IS_INT, CVC4::api::Kind::IS_INTEGER},

      /* Reals */
      {Op::REAL_NEG, CVC4::api::Kind::UMINUS},
      {Op::REAL_SUB, CVC4::api::Kind::MINUS},
      {Op::REAL_ADD, CVC4::api::Kind::PLUS},
      {Op::REAL_MUL, CVC4::api::Kind::MULT},
      {Op::REAL_DIV, CVC4::api::Kind::DIVISION},
      {Op::REAL_LT, CVC4::api::Kind::LT},
      {Op::REAL_LTE, CVC4::api::Kind::LEQ},
      {Op::REAL_GT, CVC4::api::Kind::GT},
      {Op::REAL_GTE, CVC4::api::Kind::GEQ},
      {Op::REAL_IS_INT, CVC4::api::Kind::IS_INTEGER},

      /* Quantifiers */
      {Op::FORALL, CVC4::api::Kind::FORALL},
      {Op::EXISTS, CVC4::api::Kind::EXISTS},

      /* Strings */
      {Op::STR_CONCAT, CVC4::api::Kind::STRING_CONCAT},
      {Op::STR_LEN, CVC4::api::Kind::STRING_LENGTH},
      {Op::STR_LT, CVC4::api::Kind::STRING_LT},
      {Op::STR_TO_RE, CVC4::api::Kind::STRING_TO_REGEXP},
      {Op::STR_IN_RE, CVC4::api::Kind::STRING_IN_REGEXP},
      {Op::RE_CONCAT, CVC4::api::Kind::REGEXP_CONCAT},
      {Op::RE_UNION, CVC4::api::Kind::REGEXP_UNION},
      {Op::RE_INTER, CVC4::api::Kind::REGEXP_INTER},
      {Op::RE_STAR, CVC4::api::Kind::REGEXP_STAR},
      {Op::STR_LE, CVC4::api::Kind::STRING_LEQ},
      {Op::STR_AT, CVC4::api::Kind::STRING_CHARAT},
      {Op::STR_SUBSTR, CVC4::api::Kind::STRING_SUBSTR},
      {Op::STR_PREFIXOF, CVC4::api::Kind::STRING_PREFIX},
      {Op::STR_SUFFIXOF, CVC4::api::Kind::STRING_SUFFIX},
      {Op::STR_CONTAINS, CVC4::api::Kind::STRING_CONTAINS},
      {Op::STR_INDEXOF, CVC4::api::Kind::STRING_INDEXOF},
      {Op::STR_REPLACE, CVC4::api::Kind::STRING_REPLACE},
      {Op::STR_REPLACE_ALL, CVC4::api::Kind::STRING_REPLACE_ALL},
      {Op::STR_REPLACE_RE, CVC4::api::Kind::STRING_REPLACE_RE},
      {Op::STR_REPLACE_RE_ALL, CVC4::api::Kind::STRING_REPLACE_RE_ALL},
      {Op::RE_COMP, CVC4::api::Kind::REGEXP_COMPLEMENT},
      {Op::RE_DIFF, CVC4::api::Kind::REGEXP_DIFF},
      {Op::RE_PLUS, CVC4::api::Kind::REGEXP_PLUS},
      {Op::RE_OPT, CVC4::api::Kind::REGEXP_OPT},
      {Op::RE_RANGE, CVC4::api::Kind::REGEXP_RANGE},
      {Op::RE_POW, CVC4::api::Kind::REGEXP_REPEAT},
      {Op::RE_LOOP, CVC4::api::Kind::REGEXP_LOOP},
      {Op::STR_IS_DIGIT, CVC4::api::Kind::STRING_IS_DIGIT},
      {Op::STR_TO_CODE, CVC4::api::Kind::STRING_TO_CODE},
      {Op::STR_FROM_CODE, CVC4::api::Kind::STRING_FROM_CODE},
      {Op::STR_TO_INT, CVC4::api::Kind::STRING_TO_INT},
      {Op::STR_FROM_INT, CVC4::api::Kind::STRING_FROM_INT},

      /* UF */
      {Op::UF_APPLY, CVC4::api::Kind::APPLY_UF},

      /* Solver-specific operators */
      {OP_REDOR, CVC4::api::Kind::BITVECTOR_REDOR},
      {OP_REDAND, CVC4::api::Kind::BITVECTOR_REDAND},
      {OP_STRING_UPDATE, CVC4::api::Kind::STRING_UPDATE},
      {OP_STRING_TOLOWER, CVC4::api::Kind::STRING_TOLOWER},
      {OP_STRING_TOUPPER, CVC4::api::Kind::STRING_TOUPPER},
      {OP_STRING_REV, CVC4::api::Kind::STRING_REV},
  };
}

CVC4::api::Sort&
CVC4Solver::get_cvc4_sort(Sort sort) const
{
  return static_cast<CVC4Sort*>(sort.get())->d_sort;
}

CVC4::api::Term&
CVC4Solver::get_cvc4_term(Term term) const
{
  return static_cast<CVC4Term*>(term.get())->d_term;
}

/* -------------------------------------------------------------------------- */
/* Solver-specific operators, SolverManager configuration.                    */
/* -------------------------------------------------------------------------- */

const OpKind CVC4Solver::OP_REDAND = "cvc4-OP_REDAND";
const OpKind CVC4Solver::OP_REDOR  = "cvc4-OP_REDOR";
const OpKind CVC4Solver::OP_STRING_UPDATE  = "cvc4-OP_STRING_UPDATE";
const OpKind CVC4Solver::OP_STRING_TOLOWER = "cvc4-OP_STRING_TOLOWER";
const OpKind CVC4Solver::OP_STRING_TOUPPER = "cvc4-OP_STRING_TOUPPER";
const OpKind CVC4Solver::OP_STRING_REV     = "cvc4-OP_STRING_REV";

void
CVC4Solver::configure_smgr(SolverManager* smgr) const
{
  smgr->add_op_kind(OP_REDAND, 1, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_REDOR, 1, 0, SORT_BOOL, {SORT_BV}, THEORY_BV);

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

const ActionKind CVC4Solver::ACTION_CHECK_ENTAILED = "cvc4-check-entailed";
const ActionKind CVC4Solver::ACTION_SIMPLIFY       = "cvc4-simplify";

class CVC4ActionCheckEntailed : public Action
{
 public:
  CVC4ActionCheckEntailed(SolverManager& smgr)
      : Action(smgr, CVC4Solver::ACTION_CHECK_ENTAILED, false)
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
          d_rng.pick<uint32_t>(1, SMTMBT_CVC4_MAX_N_TERMS_CHECK_ENTAILED);
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
    assert(tokens.size() >= 1);
    if (tokens.size() == 1)
    {
      Term term = d_smgr.get_term(str_to_uint32(tokens[0]));
      assert(term != nullptr);
      _run(term);
    }
    else
    {
      std::vector<Term> terms;
      uint32_t n_terms = str_to_uint32(tokens[0]);
      for (uint32_t i = 0, idx = 1; i < n_terms; ++i, ++idx)
      {
        uint32_t id = str_to_uint32(tokens[idx]);
        Term t      = d_smgr.get_term(id);
        assert(t != nullptr);
        terms.push_back(t);
      }
      _run(terms);
    }
    return 0;
  }

 private:
  void _run(Term term)
  {
    SMTMBT_TRACE << get_kind() << " " << term;
    d_smgr.reset_sat();
    CVC4Solver& solver        = static_cast<CVC4Solver&>(d_smgr.get_solver());
    CVC4::api::Solver* cvc4   = solver.get_solver();
    CVC4::api::Term cvc4_term = solver.get_cvc4_term(term);
    assert(!cvc4_term.isNull());
    CVC4::api::Result res = cvc4->checkEntailed(cvc4_term);
    assert(!d_rng.pick_with_prob(1) || res == res);
    assert(res != CVC4::api::Result());
    assert(!res.isSat());
    assert(!res.isUnsat());
    assert(!res.isSatUnknown());
    if (res.isEntailmentUnknown())
    {
      if (d_rng.pick_with_prob(1))
      {
        std::string expl = res.getUnknownExplanation();
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
    SMTMBT_TRACE << get_kind() << " " << terms.size() << terms;
    d_smgr.reset_sat();
    CVC4Solver& solver      = static_cast<CVC4Solver&>(d_smgr.get_solver());
    CVC4::api::Solver* cvc4 = solver.get_solver();
    std::vector<CVC4::api::Term> cvc4_terms = solver.terms_to_cvc4_terms(terms);
    CVC4::api::Result res                   = cvc4->checkEntailed(cvc4_terms);
    assert(!d_rng.pick_with_prob(1) || res == res);
    assert(res != CVC4::api::Result());
    assert(!res.isSat());
    assert(!res.isUnsat());
    assert(!res.isSatUnknown());
    if (res.isEntailmentUnknown())
    {
      if (d_rng.pick_with_prob(1))
      {
        std::string expl = res.getUnknownExplanation();
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

class CVC4ActionSimplify : public Action
{
 public:
  CVC4ActionSimplify(SolverManager& smgr)
      : Action(smgr, CVC4Solver::ACTION_SIMPLIFY, true)
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
    assert(tokens.size() == 1);
    Term term = d_smgr.get_term(str_to_uint32(tokens[0]));
    assert(term != nullptr);
    return _run(term);
  }

 private:
  uint64_t _run(Term term)
  {
    SMTMBT_TRACE << get_kind() << " " << term;
    d_smgr.reset_sat();
    CVC4Solver& solver       = static_cast<CVC4Solver&>(d_smgr.get_solver());
    CVC4::api::Solver* cvc4  = solver.get_solver();
    CVC4::api::Term cvc4_res = cvc4->simplify(solver.get_cvc4_term(term));
    assert (!cvc4_res.isNull());
    Term res  = std::make_shared<CVC4Term>(cvc4, cvc4_res);
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
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }
};

/* -------------------------------------------------------------------------- */

void
CVC4Solver::configure_fsm(FSM* fsm) const
{
  State* s_sat = fsm->get_state(State::CHECK_SAT);

  // Solver::simplify(const Term& term)
  auto a_simplify = fsm->new_action<CVC4ActionSimplify>();
  fsm->add_action_to_all_states(a_simplify, 100, {State::NEW, State::DELETE});

  // Solver::checkEntailed(Term term)
  // Solver::checkEntailed(std::vector<Term> terms)
  auto a_check_entailed = fsm->new_action<CVC4ActionCheckEntailed>();
  s_sat->add_action(a_check_entailed, 1);
}
}  // namespace btor
}  // namespace smtmbt

#endif
