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

CVC4Sort::CVC4Sort(CVC4::api::Solver* cvc4, CVC4::api::Sort sort)
    : d_solver(cvc4), d_sort(sort)
{
}

CVC4Sort::~CVC4Sort()
{
}

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
    assert(d_kind == cvc4_sort->d_kind);
    assert(d_sort.isNull() == cvc4_sort->d_sort.isNull());
    return d_sort == cvc4_sort->d_sort;
  }
  return false;
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
CVC4Sort::is_rm() const
{
  return d_sort.isRoundingMode();
}

uint32_t
CVC4Sort::get_bv_size() const
{
  return d_sort.getBVSize();
}

uint32_t
CVC4Sort::get_fp_exp_size() const
{
  return d_sort.getFPExponentSize();
}

uint32_t
CVC4Sort::get_fp_sig_size() const
{
  return d_sort.getFPSignificandSize();
}

/* -------------------------------------------------------------------------- */
/* CVC4Term                                                                   */
/* -------------------------------------------------------------------------- */

CVC4Term::CVC4Term(CVC4::api::Solver* cvc4, CVC4::api::Term term)
    : d_solver(cvc4), d_term(term)
{
}

CVC4Term::~CVC4Term()
{
}

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

/* -------------------------------------------------------------------------- */
/* CVC4Solver                                                                 */
/* -------------------------------------------------------------------------- */

OpKindSet
CVC4Solver::get_unsupported_op_kinds() const
{
  return {
      OP_IFF,
      OP_BV_DEC,
      OP_BV_INC,
      OP_BV_REDXOR,
      OP_BV_SADDO,
      OP_BV_SDIVO,
      OP_BV_SMULO,
      OP_BV_SSUBO,
      OP_BV_UADDO,
      OP_BV_UMULO,
      OP_BV_USUBO,
  };
}

void
CVC4Solver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = new api::Solver();
  init_op_kinds();
  d_solver->setOption("fp-exp", "true");
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
CVC4Solver::check_failed_assumption(const Term& t) const
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
    case SORT_RM: cvc4_res = d_solver->getRoundingmodeSort(); break;

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
CVC4Solver::mk_const(Sort sort, const std::string name)
{
  CVC4::api::Term cvc4_res = d_solver->mkConst(get_cvc4_sort(sort), name);
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  return std::shared_ptr<CVC4Term>(new CVC4Term(d_solver, cvc4_res));
}

Term
CVC4Solver::mk_var(Sort sort, const std::string name)
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
CVC4Solver::mk_value(Sort sort, uint64_t value)
{
  CVC4::api::Term cvc4_res;
  CVC4::api::Sort cvc4_sort = get_cvc4_sort(sort);
  SortKind sort_kind        = sort->get_kind();

  switch (sort_kind)
  {
    case SORT_BV:
      assert(sort->is_bv());
      cvc4_res = d_solver->mkBitVector(sort->get_bv_size(), value);
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
CVC4Solver::mk_value(Sort sort, std::string value, Base base)
{
  assert(sort->is_bv());

  CVC4::api::Term cvc4_res;
  CVC4::api::Sort cvc4_sort = get_cvc4_sort(sort);
  uint32_t bw               = sort->get_bv_size();

  switch (base)
  {
    case DEC:
      cvc4_res = d_rng.flip_coin()
                     ? d_solver->mkBitVector(bw, value, 10)
                     : d_solver->mkBitVector(bw, value.c_str(), 10);
      break;

    case HEX:
      cvc4_res = d_rng.flip_coin()
                     ? d_solver->mkBitVector(bw, value, 16)
                     : d_solver->mkBitVector(bw, value.c_str(), 16);
      break;

    default:
      assert(base == BIN);
      cvc4_res = d_rng.flip_coin() ? d_solver->mkBitVector(value, 2)
                                   : d_solver->mkBitVector(value.c_str(), 2);
  }
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  std::shared_ptr<CVC4Term> res(new CVC4Term(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_value(Sort sort, SpecialValueFP value)
{
  assert(sort->is_fp());
  CVC4::api::Term cvc4_res;

  switch (value)
  {
    case Solver::SpecialValueFP::SMTMBT_FP_POS_INF:
      cvc4_res =
          d_solver->mkPosInf(sort->get_fp_exp_size(), sort->get_fp_sig_size());
      break;
    case Solver::SpecialValueFP::SMTMBT_FP_NEG_INF:
      cvc4_res =
          d_solver->mkNegInf(sort->get_fp_exp_size(), sort->get_fp_sig_size());
      break;
    case Solver::SpecialValueFP::SMTMBT_FP_POS_ZERO:
      cvc4_res =
          d_solver->mkPosZero(sort->get_fp_exp_size(), sort->get_fp_sig_size());
      break;
    case Solver::SpecialValueFP::SMTMBT_FP_NEG_ZERO:
      cvc4_res =
          d_solver->mkNegZero(sort->get_fp_exp_size(), sort->get_fp_sig_size());
      break;
    default:
      assert(value == Solver::SpecialValueFP::SMTMBT_FP_NAN);
      cvc4_res =
          d_solver->mkNaN(sort->get_fp_exp_size(), sort->get_fp_sig_size());
  }
  std::shared_ptr<CVC4Term> res(new CVC4Term(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_value(Sort sort, SpecialValueRM value)
{
  assert(sort->is_rm());
  CVC4::api::Term cvc4_res;

  switch (value)
  {
    case Solver::SpecialValueRM::SMTMBT_FP_RNE:
      cvc4_res = d_solver->mkRoundingMode(
          CVC4::api::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
      break;
    case Solver::SpecialValueRM::SMTMBT_FP_RNA:
      cvc4_res = d_solver->mkRoundingMode(
          CVC4::api::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY);
      break;
    case Solver::SpecialValueRM::SMTMBT_FP_RTN:
      cvc4_res = d_solver->mkRoundingMode(
          CVC4::api::RoundingMode::ROUND_TOWARD_NEGATIVE);
      break;
    case Solver::SpecialValueRM::SMTMBT_FP_RTP:
      cvc4_res = d_solver->mkRoundingMode(
          CVC4::api::RoundingMode::ROUND_TOWARD_POSITIVE);
      break;
    default:
      assert(value == Solver::SpecialValueRM::SMTMBT_FP_RTZ);
      cvc4_res =
          d_solver->mkRoundingMode(CVC4::api::RoundingMode::ROUND_TOWARD_ZERO);
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

  if (kind == OP_FORALL || kind == OP_EXISTS)
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
      uint32_t idx = cvc4_opterm.getIndices<uint32_t>();
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
  if (d_rng.flip_coin()) n_args = SMTMBT_MK_TERM_N_ARGS;

  /* create term */
  switch (n_args)
  {
    case 0:
      cvc4_res = n_params ? d_solver->mkTerm(cvc4_opterm)
                          : d_solver->mkTerm(cvc4_kind);
      break;

    case 1:
      if (kind == OP_NOT && d_rng.flip_coin())
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
      if (kind == OP_AND && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).andTerm(get_cvc4_term(args[1]));
      }
      else if (kind == OP_OR && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).orTerm(get_cvc4_term(args[1]));
      }
      else if (kind == OP_XOR && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).xorTerm(get_cvc4_term(args[1]));
      }
      else if (kind == OP_EQUAL && d_rng.flip_coin())
      {
        assert(!n_params);
        cvc4_res = get_cvc4_term(args[0]).eqTerm(get_cvc4_term(args[1]));
      }
      else if (kind == OP_IMPLIES && d_rng.flip_coin())
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
      if (kind == OP_ITE && d_rng.flip_coin())
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
      assert(n_args == SMTMBT_MK_TERM_N_ARGS || n_args > 3);
      std::vector<CVC4::api::Term> cvc4_args;
      cvc4_args = terms_to_cvc4_terms(args);
      cvc4_res = n_params ? d_solver->mkTerm(cvc4_opterm, cvc4_args)
                          : d_solver->mkTerm(cvc4_kind, cvc4_args);
  }
DONE:
  assert(!cvc4_res.isNull());
  assert(!d_rng.pick_with_prob(1) || cvc4_res == cvc4_res);
  assert(!d_rng.pick_with_prob(1) || !(cvc4_res != cvc4_res));
  assert(cvc4_kind == cvc4_res.getKind());
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
CVC4Solver::assert_formula(const Term& t) const
{
  d_solver->assertFormula(get_cvc4_term(t));
}

Solver::Result
CVC4Solver::check_sat() const
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
CVC4Solver::check_sat_assuming(std::vector<Term>& assumptions) const
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
CVC4Solver::get_unsat_assumptions() const
{
  std::vector<Term> res;
  std::vector<CVC4::api::Term> cvc4_res = d_solver->getUnsatAssumptions();
  return cvc4_terms_to_terms(cvc4_res);
}

std::vector<Term>
CVC4Solver::get_value(std::vector<Term>& terms) const
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
CVC4Solver::push(uint32_t n_levels) const
{
  d_solver->push(n_levels);
}

void
CVC4Solver::pop(uint32_t n_levels) const
{
  d_solver->pop(n_levels);
}

void
CVC4Solver::print_model() const
{
  d_solver->printModel(std::cout);
}

void
CVC4Solver::reset_assertions() const
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

void
CVC4Solver::init_op_kinds()
{
  d_kinds = {
      {OP_UNDEFINED, CVC4::api::Kind::UNDEFINED_KIND},
      {OP_DISTINCT, CVC4::api::Kind::DISTINCT},
      {OP_EQUAL, CVC4::api::Kind::EQUAL},
      {OP_ITE, CVC4::api::Kind::ITE},

      {OP_AND, CVC4::api::Kind::AND},
      {OP_OR, CVC4::api::Kind::OR},
      {OP_NOT, CVC4::api::Kind::NOT},
      {OP_XOR, CVC4::api::Kind::XOR},
      {OP_IMPLIES, CVC4::api::Kind::IMPLIES},

      {OP_ARRAY_SELECT, CVC4::api::Kind::SELECT},
      {OP_ARRAY_STORE, CVC4::api::Kind::STORE},

      {OP_BV_EXTRACT, CVC4::api::Kind::BITVECTOR_EXTRACT},
      {OP_BV_REPEAT, CVC4::api::Kind::BITVECTOR_REPEAT},
      {OP_BV_ROTATE_LEFT, CVC4::api::Kind::BITVECTOR_ROTATE_LEFT},
      {OP_BV_ROTATE_RIGHT, CVC4::api::Kind::BITVECTOR_ROTATE_RIGHT},
      {OP_BV_SIGN_EXTEND, CVC4::api::Kind::BITVECTOR_SIGN_EXTEND},
      {OP_BV_ZERO_EXTEND, CVC4::api::Kind::BITVECTOR_ZERO_EXTEND},

      {OP_BV_CONCAT, CVC4::api::Kind::BITVECTOR_CONCAT},
      {OP_BV_AND, CVC4::api::Kind::BITVECTOR_AND},
      {OP_BV_OR, CVC4::api::Kind::BITVECTOR_OR},
      {OP_BV_XOR, CVC4::api::Kind::BITVECTOR_XOR},
      {OP_BV_MULT, CVC4::api::Kind::BITVECTOR_MULT},
      {OP_BV_ADD, CVC4::api::Kind::BITVECTOR_PLUS},
      {OP_BV_NOT, CVC4::api::Kind::BITVECTOR_NOT},
      {OP_BV_NEG, CVC4::api::Kind::BITVECTOR_NEG},
      {OP_BV_REDOR, CVC4::api::Kind::BITVECTOR_REDOR},
      {OP_BV_REDAND, CVC4::api::Kind::BITVECTOR_REDAND},
      {OP_BV_NAND, CVC4::api::Kind::BITVECTOR_NAND},
      {OP_BV_NOR, CVC4::api::Kind::BITVECTOR_NOR},
      {OP_BV_XNOR, CVC4::api::Kind::BITVECTOR_XNOR},
      {OP_BV_COMP, CVC4::api::Kind::BITVECTOR_COMP},
      {OP_BV_SUB, CVC4::api::Kind::BITVECTOR_SUB},
      {OP_BV_UDIV, CVC4::api::Kind::BITVECTOR_UDIV},
      {OP_BV_UREM, CVC4::api::Kind::BITVECTOR_UREM},
      {OP_BV_UREM, CVC4::api::Kind::BITVECTOR_UREM},
      {OP_BV_SDIV, CVC4::api::Kind::BITVECTOR_SDIV},
      {OP_BV_SREM, CVC4::api::Kind::BITVECTOR_SREM},
      {OP_BV_SMOD, CVC4::api::Kind::BITVECTOR_SMOD},
      {OP_BV_SHL, CVC4::api::Kind::BITVECTOR_SHL},
      {OP_BV_LSHR, CVC4::api::Kind::BITVECTOR_LSHR},
      {OP_BV_ASHR, CVC4::api::Kind::BITVECTOR_ASHR},
      {OP_BV_ULT, CVC4::api::Kind::BITVECTOR_ULT},
      {OP_BV_ULE, CVC4::api::Kind::BITVECTOR_ULE},
      {OP_BV_UGT, CVC4::api::Kind::BITVECTOR_UGT},
      {OP_BV_UGE, CVC4::api::Kind::BITVECTOR_UGE},
      {OP_BV_SLT, CVC4::api::Kind::BITVECTOR_SLT},
      {OP_BV_SLE, CVC4::api::Kind::BITVECTOR_SLE},
      {OP_BV_SGT, CVC4::api::Kind::BITVECTOR_SGT},
      {OP_BV_SGE, CVC4::api::Kind::BITVECTOR_SGE},

      {OP_FP_ABS, CVC4::api::Kind::FLOATINGPOINT_ABS},
      {OP_FP_ADD, CVC4::api::Kind::FLOATINGPOINT_PLUS},
      {OP_FP_DIV, CVC4::api::Kind::FLOATINGPOINT_DIV},
      {OP_FP_EQ, CVC4::api::Kind::FLOATINGPOINT_EQ},
      {OP_FP_FMA, CVC4::api::Kind::FLOATINGPOINT_FMA},
      {OP_FP_FP, CVC4::api::Kind::FLOATINGPOINT_FP},
      {OP_FP_IS_NORMAL, CVC4::api::Kind::FLOATINGPOINT_ISN},
      {OP_FP_IS_SUBNORMAL, CVC4::api::Kind::FLOATINGPOINT_ISSN},
      {OP_FP_IS_INF, CVC4::api::Kind::FLOATINGPOINT_ISINF},
      {OP_FP_IS_NAN, CVC4::api::Kind::FLOATINGPOINT_ISNAN},
      {OP_FP_IS_NEG, CVC4::api::Kind::FLOATINGPOINT_ISNEG},
      {OP_FP_IS_POS, CVC4::api::Kind::FLOATINGPOINT_ISPOS},
      {OP_FP_IS_ZERO, CVC4::api::Kind::FLOATINGPOINT_ISZ},
      {OP_FP_LT, CVC4::api::Kind::FLOATINGPOINT_LT},
      {OP_FP_LTE, CVC4::api::Kind::FLOATINGPOINT_LEQ},
      {OP_FP_GT, CVC4::api::Kind::FLOATINGPOINT_GT},
      {OP_FP_GTE, CVC4::api::Kind::FLOATINGPOINT_GEQ},
      {OP_FP_MAX, CVC4::api::Kind::FLOATINGPOINT_MAX},
      {OP_FP_MIN, CVC4::api::Kind::FLOATINGPOINT_MIN},
      {OP_FP_MUL, CVC4::api::Kind::FLOATINGPOINT_MULT},
      {OP_FP_NEG, CVC4::api::Kind::FLOATINGPOINT_NEG},
      {OP_FP_REM, CVC4::api::Kind::FLOATINGPOINT_REM},
      {OP_FP_RTI, CVC4::api::Kind::FLOATINGPOINT_RTI},
      {OP_FP_SQRT, CVC4::api::Kind::FLOATINGPOINT_SQRT},
      {OP_FP_SUB, CVC4::api::Kind::FLOATINGPOINT_SUB},
      {OP_FP_TO_FP_FROM_BV,
       CVC4::api::Kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR},
      {OP_FP_TO_FP_FROM_INT_BV,
       CVC4::api::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR},
      {OP_FP_TO_FP_FROM_FP, CVC4::api::Kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT},
      {OP_FP_TO_FP_FROM_UINT_BV,
       CVC4::api::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR},
      {OP_FP_TO_FP_FROM_REAL, CVC4::api::Kind::FLOATINGPOINT_TO_FP_REAL},
      {OP_FP_TO_REAL, CVC4::api::Kind::FLOATINGPOINT_TO_REAL},
      {OP_FP_TO_SBV, CVC4::api::Kind::FLOATINGPOINT_TO_SBV},
      {OP_FP_TO_UBV, CVC4::api::Kind::FLOATINGPOINT_TO_UBV},

      {OP_FORALL, CVC4::api::Kind::FORALL},
      {OP_EXISTS, CVC4::api::Kind::EXISTS},
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
/* Solver-specific actions, FSM configuration. */
/* -------------------------------------------------------------------------- */

class CVC4ActionCheckEntailed : public Action
{
 public:
  CVC4ActionCheckEntailed(SolverManager& smgr)
      : Action(smgr, "cvc4-check-entailed")
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
    SMTMBT_TRACE << get_id() << " " << term;
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
    SMTMBT_TRACE << get_id() << " " << terms.size() << terms;
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
  CVC4ActionSimplify(SolverManager& smgr) : Action(smgr, "cvc4-simplify") {}

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
    SMTMBT_TRACE << get_id() << " " << term;
    CVC4Solver& solver       = static_cast<CVC4Solver&>(d_smgr.get_solver());
    CVC4::api::Solver* cvc4  = solver.get_solver();
    CVC4::api::Term cvc4_res = cvc4->simplify(solver.get_cvc4_term(term));
    assert (!cvc4_res.isNull());
    Term res  = std::make_shared<CVC4Term>(cvc4, cvc4_res);
    Sort sort = term->get_sort();
    assert (sort != nullptr);
    /* Note: The simplified term 'res' may or may not be already in the term
     * DB. However, we assume the same level for 'res' as the original term
     * since can't always compute the exact level. */
    if (res->get_levels().empty())
    {
      res->set_levels(term->get_levels());
    }
    d_smgr.add_term(res, sort, sort->get_kind());
    SMTMBT_TRACE_RETURN << res;
    return res->get_id();
  }
};

/* -------------------------------------------------------------------------- */

void
CVC4Solver::configure_fsm(FSM* fsm) const
{
  State* s_sat = fsm->get_state("check_sat");

  // Solver::simplify(const Term& term)
  auto a_simplify = fsm->new_action<CVC4ActionSimplify>();
  fsm->add_action_to_all_states(a_simplify, 100, {"new", "delete"});

  // Solver::checkEntailed(Term term)
  // Solver::checkEntailed(std::vector<Term> terms)
  auto a_check_entailed = fsm->new_action<CVC4ActionCheckEntailed>();
  s_sat->add_action(a_check_entailed, 1);
}
}  // namespace btor
}  // namespace smtmbt
