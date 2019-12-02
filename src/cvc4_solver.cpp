#include "cvc4_solver.hpp"

#include <cassert>

#include "cvc4/api/cvc4cpp.h"

using namespace CVC4;

namespace smtmbt {
namespace cvc4 {

/* -------------------------------------------------------------------------- */
/* CVC4Sort                                                                   */
/* -------------------------------------------------------------------------- */

CVC4Sort::CVC4Sort(CVC4::api::Solver* cvc4, CVC4::api::Sort sort)
    : d_solver(cvc4), d_sort(sort)
{
}

CVC4Sort::~CVC4Sort()
{
  // TODO: release sort?
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

uint32_t
CVC4Sort::get_bv_size() const
{
  return d_sort.getBVSize();
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
  // TODO: release term?
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

void
CVC4Solver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = new api::Solver();
  init_op_kinds();
}

void
CVC4Solver::delete_solver()
{
  assert(d_solver != nullptr);
  delete d_solver;
  d_solver = nullptr;
}

bool
CVC4Solver::is_initialized() const
{
  return d_solver != nullptr;
}

Sort
CVC4Solver::mk_sort(SortKind kind) const
{
  CVC4::api::Sort cvc4_res;
  switch (kind)
  {
    case SORT_BOOL: cvc4_res = d_solver->getBooleanSort(); break;

    default: assert(false);
  }
  return std::shared_ptr<CVC4Sort>(new CVC4Sort(d_solver, cvc4_res));
}

Sort
CVC4Solver::mk_sort(SortKind kind, uint32_t size) const
{
  CVC4::api::Sort cvc4_res;
  switch (kind)
  {
    case SORT_BV: cvc4_res = d_solver->mkBitVectorSort(size); break;

    default: assert(false);
  }
  std::shared_ptr<CVC4Sort> res(new CVC4Sort(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_const(Sort sort, const std::string name) const
{
  CVC4::api::Term res = d_solver->mkConst(get_cvc4_sort(sort), name);
  return std::shared_ptr<CVC4Term>(new CVC4Term(d_solver, res));
}

Term
CVC4Solver::mk_value(Sort sort, bool value) const
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
  std::shared_ptr<CVC4Term> res(new CVC4Term(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_value(Sort sort, uint64_t value) const
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
  std::shared_ptr<CVC4Term> res(new CVC4Term(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_value(Sort sort, std::string value, Base base) const
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
  std::shared_ptr<CVC4Term> res(new CVC4Term(d_solver, cvc4_res));
  assert(res);
  return res;
}

Term
CVC4Solver::mk_term(const OpKind& kind,
                    std::vector<Term>& args,
                    std::vector<uint32_t>& params) const
{
  assert(d_kinds.find(kind) != d_kinds.end());

  CVC4::api::Term cvc4_res;
  CVC4::api::Kind cvc4_kind = d_kinds.at(kind);
  CVC4::api::OpTerm cvc4_opterm;

  int32_t n_args    = args.size();
  uint32_t n_params = params.size();

  assert(!n_params || d_op_kinds.find(kind) != d_op_kinds.end());
  /* create OpTerm for indexed operators */
  switch (n_params)
  {
    case 1:
      cvc4_opterm = d_solver->mkOpTerm(d_op_kinds.at(kind), params[0]);
      break;
    case 2:
      cvc4_opterm =
          d_solver->mkOpTerm(d_op_kinds.at(kind), params[0], params[1]);
      break;
    default: assert(n_params == 0);
  }

  /* use vector with 50% probability */
  if (d_rng.flip_coin()) n_args = SMTMBT_MK_TERM_N_ARGS;

  /* create term */
  switch (n_args)
  {
    case 0:
      cvc4_res = n_params ? d_solver->mkTerm(cvc4_kind, cvc4_opterm)
                          : d_solver->mkTerm(cvc4_kind);
      break;

    case 1:
      cvc4_res = n_params ? d_solver->mkTerm(
                     cvc4_kind, cvc4_opterm, get_cvc4_term(args[0]))
                          : d_solver->mkTerm(cvc4_kind, get_cvc4_term(args[0]));
      break;

    case 2:
      cvc4_res = n_params ? d_solver->mkTerm(cvc4_kind,
                                             cvc4_opterm,
                                             get_cvc4_term(args[0]),
                                             get_cvc4_term(args[1]))
                          : d_solver->mkTerm(cvc4_kind,
                                             get_cvc4_term(args[0]),
                                             get_cvc4_term(args[1]));
      break;

    case 3:
      cvc4_res = n_params ? d_solver->mkTerm(cvc4_kind,
                                             cvc4_opterm,
                                             get_cvc4_term(args[0]),
                                             get_cvc4_term(args[1]),
                                             get_cvc4_term(args[2]))
                          : d_solver->mkTerm(cvc4_kind,
                                             get_cvc4_term(args[0]),
                                             get_cvc4_term(args[1]),
                                             get_cvc4_term(args[2]));
      break;

    default:
      assert(n_args == SMTMBT_MK_TERM_N_ARGS || n_args > 3);
      std::vector<CVC4::api::Term> cvc4_args;
      for (Term t : args) cvc4_args.push_back(get_cvc4_term(t));
      cvc4_res = n_params ? d_solver->mkTerm(cvc4_kind, cvc4_opterm, cvc4_args)
                          : d_solver->mkTerm(cvc4_kind, cvc4_args);
  }
  return std::shared_ptr<CVC4Term>(new CVC4Term(d_solver, cvc4_res));
}

Sort
CVC4Solver::get_sort(Term term) const
{
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
  bool check_sat = d_rng.flip_coin();
  CVC4::api::Result res =
      check_sat ? d_solver->checkSat() : d_solver->checkValid();
  assert(!res.isSat() || check_sat);
  assert(!res.isUnsat() || check_sat);
  assert(!res.isSatUnknown() || check_sat);
  assert(!res.isValid() || !check_sat);
  assert(!res.isInvalid() || !check_sat);
  assert(!res.isValidUnknown() || !check_sat);
  if (res.isSat() || res.isInvalid()) return Result::SAT;
  if (res.isUnsat() || res.isValid()) return Result::UNSAT;
  assert(res.isSatUnknown() || res.isValidUnknown());
  return Result::UNKNOWN;
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
      // BITVECTOR_UDIV_TOTAL
      {OP_BV_UREM, CVC4::api::Kind::BITVECTOR_UREM},
      // BITVECTOR_UREM_TOTAL
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
  };
  d_op_kinds = {
      {OP_BV_EXTRACT, CVC4::api::Kind::BITVECTOR_EXTRACT_OP},
      {OP_BV_REPEAT, CVC4::api::Kind::BITVECTOR_REPEAT_OP},
      {OP_BV_ROTATE_LEFT, CVC4::api::Kind::BITVECTOR_ROTATE_LEFT_OP},
      {OP_BV_ROTATE_RIGHT, CVC4::api::Kind::BITVECTOR_ROTATE_RIGHT_OP},
      {OP_BV_SIGN_EXTEND, CVC4::api::Kind::BITVECTOR_SIGN_EXTEND_OP},
      {OP_BV_ZERO_EXTEND, CVC4::api::Kind::BITVECTOR_ZERO_EXTEND_OP},
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

}  // namespace btor
}  // namespace smtmbt
