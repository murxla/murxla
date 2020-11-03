#ifdef SMTMBT_USE_BITWUZLA

#include "bzla_solver.hpp"

#include <bitset>
#include <cassert>
#include <cstdlib>

#include "config.hpp"
#include "theory.hpp"
#include "util.hpp"

namespace smtmbt {
namespace bzla {

/* -------------------------------------------------------------------------- */
/* CBzlaSort                                                                   */
/* -------------------------------------------------------------------------- */

CBzlaSort::CBzlaSort(Btor* btor, BitwuzlaSort sort)
    : d_solver(btor), d_sort(sort)
{
}

CBzlaSort::~CBzlaSort() {}

size_t
CBzlaSort::hash() const
{
  return bitwuzla_sort_hash(d_solver, d_sort);
}

bool
CBzlaSort::equals(const Sort& other) const
{
  CBzlaSort* bzla_sort = dynamic_cast<CBzlaSort*>(other.get());
  if (bzla_sort)
  {
    return d_sort == bzla_sort->d_sort;
  }
  return false;
}

bool
CBzlaSort::is_array() const
{
  return bitwuzla_sort_is_array(d_solver, d_sort);
}

bool
CBzlaSort::is_bool() const
{
  BitwuzlaSort s = bitwuzla_mk_bool_sort(d_solver);
  bool res       = s == d_sort;
  return res && d_kind == SORT_BOOL;
}

bool
CBzlaSort::is_bv() const
{
  return bitwuzla_sort_is_bv(d_solver, d_sort);
}

bool
CBzlaSort::is_fp() const
{
  return bitwuzla_sort_is_fp(d_solver, d_sort);
}

bool
CBzlaSort::is_fun() const
{
  return bitwuzla_sort_is_fun(d_solver, d_sort);
}

bool
CBzlaSort::is_int() const
{
  return false;
}

bool
CBzlaSort::is_real() const
{
  return false;
}

bool
CBzlaSort::is_rm() const
{
  return bitwuzla_sort_is_fun(d_solver, d_sort);
}

bool
CBzlaSort::is_string() const
{
  return false;
}

bool
CBzlaSort::is_reglan() const
{
  return false;
}

uint32_t
CBzlaSort::get_bv_size() const
{
  assert(is_bv());
  uint32_t res = bitwuzla_sort_bv_get_size(d_solver, d_sort);
  assert(res);
  return res;
}

uint32_t
CBzlaSort::get_fp_exp_size() const
{
  assert(is_fp());
  uint32_t res = bitwuzla_sort_fp_get_exp_size(d_solver, d_sort);
  assert(res);
  return res;
}

uint32_t
CBzlaSort::get_fp_sig_size() const
{
  assert(is_fp());
  uint32_t res = bitwuzla_sort_fp_get_sig_size(d_solver, d_sort);
  assert(res);
  return res;
}

/* -------------------------------------------------------------------------- */
/* CBzlaTerm                                                                   */
/* -------------------------------------------------------------------------- */

CBzlaTerm::CBzlaTerm(Bitwuzla *bzla, BitwuzlaTerm* term)
    : d_solver(bzla), d_term(term)
{
}

CBzlaTerm::~CBzlaTerm() {}

size_t
CBzlaTerm::hash() const
{
  return bitwuzla_term_hash(d_term);
}

bool
CBzlaTerm::equals(const Term& other) const
{
  CBzlaTerm* bzla_term = dynamic_cast<CBzlaTerm*>(other.get());
  return bitwuzla_term_is_equal_sort(d_term, bzla_term);
}

bool
CBzlaTerm::is_array() const
{
  return bitwuzla_term_is_array(d_term);
}

bool
CBzlaTerm::is_bool() const
{
  return get_sort()->is_bool();
}

bool
CBzlaTerm::is_bv() const
{
  return bitwuzla_term_is_bv(d_term);
}

bool
CBzlaTerm::is_fp() const
{
  return bitwuzla_term_is_fp(d_term);
}

bool
CBzlaTerm::is_fun() const
{
  return bitwuzla_term_is_fun(d_term);
}

bool
CBzlaTerm::is_int() const
{
  return get_sort()->is_int();
}

bool
CBzlaTerm::is_real() const
{
  return get_sort()->is_real();
}

bool
CBzlaTerm::is_rm() const
{
  return bitwuzla_term_is_rm(d_term);
}

bool
CBzlaTerm::is_string() const
{
  return get_sort()->is_string();
}

bool
CBzlaTerm::is_reglan() const
{
  return get_sort()->is_reglan();
}

/* -------------------------------------------------------------------------- */
/* CBzlaSolver                                                                 */
/* -------------------------------------------------------------------------- */

void
CBzlaSolver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = bitwuzla_new();
  init_op_kinds();
  // TODO: initialize options
}

void
CBzlaSolver::delete_solver()
{
  assert(d_solver != nullptr);
  bitwuzla_delete(d_solver);
  d_solver = nullptr;
}

Btor*
CBzlaSolver::get_solver()
{
  return d_solver;
}

bool
CBzlaSolver::is_initialized() const
{
  return d_solver != nullptr;
}

TheoryIdVector
CBzlaSolver::get_supported_theories() const
{
  return {
      THEORY_ARRAY, THEORY_BV, THEORY_BOOL, THEORY_FP, THEORY_QUANT, THEORY_UF};
}

OpKindSet
CBzlaSolver::get_unsupported_op_kinds() const
{
  return {};
}

SortKindSet
CBzlaSolver::get_unsupported_var_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FP};
}

Sort
CBzlaSolver::mk_sort(SortKind kind)
{
  assert(kind == SORT_BOOL || kind == SORT_RM);
  BitwuzlaSort bzla_res;

  res = kind == SORT_BOOL ? bitwuzla_mk_bool_sort(d_solver)
                          : bitwuzla_mk_rm_sort(d_solver);
  assert(bzla_res);
  std::shared_ptr<CBzlaSort> res(new CBzlaSort(d_solver, bzla_res));
  assert(res);
  return res;
}

Sort
CBzlaSolver::mk_sort(SortKind kind, uint32_t size)
{
  assert(kind == SORT_BV);
  BitwuzlaSort bzla_res = bitwuzla_mk_bv_sort(d_solver, size);
  assert(bzla_res);
  std::shared_ptr<CBzlaSort> res(new CBzlaSort(d_solver, bzla_res));
  assert(res);
  return res;
}

Sort
CBzlaSolver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  assert(kind == SORT_FP);
  BitwuzlaSort bzla_res = bitwuzla_mk_fp_sort(d_solver, esize, ssize);
  assert(bzla_res);
  std::shared_ptr<CBzlaSort> res(new CBzlaSort(d_solver, bzla_res));
  assert(res);
  return res;
}

Sort
CBzlaSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  BitwuzlaSort bzla_res;

  switch (kind)
  {
    case SORT_ARRAY:
      bzla_res = bitwuzla_mk_array_sort(
          d_solver, get_bzla_sort(sorts[0]), get_bzla_sort(sorts[1]));
      break;

    case SORT_FUN:
    {
      BitwuzlaSort codomain = get_bzla_sort(sorts.back());
      std::vector<BitwuzlaSort> domain;
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        domain.push_back(get_bzla_sort(*it));
      }
      bzla_res =
          bitwuzla_mk_fun_sort(d_solver, domain.size(), domain.data(), codomain);
      break;
    }

    default: assert(false);
  }
  std::shared_ptr<CBzlaSort> res(new CBzlaSort(d_solver, bzla_res));
  assert(bzla_res);
  assert(res);
  return res;
}

Term
CBzlaSolver::mk_var(Sort sort, const std::string& name)
{
  BitwuzlaTerm* bzla_res;
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

  bzla_res = bitwuzla_mk_var(d_solver, get_bzla_sort(sort), cname);
  assert(bzla_res);
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(d_solver, bzla_res));
  assert(res);
  return res;
}

Term
CBzlaSolver::mk_const(Sort sort, const std::string& name)
{
  BitwuzlaTerm* bzla_res;
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

  bzla_res = bitwuzla_mk_const(d_solver, get_bzla_sort(sort), cname);
  assert(bzla_res);
  if (d_rng.pick_with_prob(1))
  {
    assert(bitwuzla_term_is_equal_sort(bzla_res, bzla_res));
  }
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(d_solver, bzla_res));
  assert(res);
  return res;
}

Term
CBzlaSolver::mk_value(Sort sort, bool value)
{
  assert(sort->is_bool());
  BitwuzlaTerm* bzla_res =
      value ? bitwuzla_mk_true(d_solver) : bitwuzla_mk_false(d_solver);
  assert(bzla_res);
  if (d_rng.pick_with_prob(10))
  {
    if (value)
    {
      check_is_bv_const(Solver::SPECIAL_VALUE_BV_ONE, bzla_res);
    }
    else
    {
      check_is_bv_const(Solver::SPECIAL_VALUE_BV_ZERO, bzla_res);
    }
  }
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(d_solver, bzla_res));
  assert(res);
  return res;
}

BitwuzlaTerm*
CBzlaSolver::mk_value_bv_uint64(Sort sort, uint64_t value)
{
  assert(sort->is_bv());
  BitwuzlaSort bzla_sort = get_bzla_sort(sort);
  BitwuzlaTerm* bzla_res =
      bitwuzla_mk_bv_value_uint64(d_solver, bzla_sort, value);
  assert(bzla_res);
  return bzla_res;
}

Term
CBzlaSolver::mk_value(Sort sort, std::string value, Base base)
{
  assert(sort->is_bv());

  BitwuzlaTerm* bzla_res;
  BitwuzlaSort bzla_sort = get_bzla_sort(sort);
  uint32_t bw            = sort->get_bv_size();
  int32_t ibase;
  BitwuzlaBVBase cbase;

  if (base == DEC)
  {
    ibase = 10;
    cbase = BITWUZLA_BV_BASE_DEC;
  }
  else
    (base == HEX)
    {
      ibase = 16;
      cbase = BITWUZLA_BV_BASE_HEX;
    }
  else
  {
    assert(base == BIN);
    ibase = 2;
    cbase = BITWUZLA_BV_BASE_BIN;
  }

  if (bw <= 64 && d_rng.flip_coin())
  {
    bzla_res =
        mk_value_bv_uint64(sort, strtoull(value.c_str(), nullptr, ibase));
  }
  else
  {
    bzla_res = bitwuzla_mk_bv_value(d_solver, bzla_sort, value.c_str(), cbase);
  }
  assert(bzla_res);
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(d_solver, bzla_res));
  assert(res);
  return res;
}

Term
CBzlaSolver::mk_special_value(Sort sort, const SpecialValueKind& value)
{
  assert(sort->is_bv());
  BitwuzlaTerm* bzla_res = 0;
  BitwuzlaSort bzla_sort = get_bzla_sort(sort);
  uint32_t bw             = sort->get_bv_size();
  bool check              = d_rng.pick_with_prob(10);
  std::string str;

  if (value == SPECIAL_VALUE_BV_ZERO)
  {
    bzla_res = bitwuzla_mk_bv_zero(d_solver, bzla_sort);
    if (check) check_is_bv_const(Solver::SPECIAL_VALUE_BV_ZERO, bzla_res);
  }
  else if (value == SPECIAL_VALUE_BV_ONE)
  {
    bzla_res = bitwuzla_mk_bv_one(d_solver, bzla_sort);
    if (check) check_is_bv_const(Solver::SPECIAL_VALUE_BV_ONE, bzla_res);
  }
  else if (value == SPECIAL_VALUE_BV_ONES)
  {
    bzla_res = bitwuzla_mk_bv_ones(d_solver, bzla_sort);
    if (check) check_is_bv_const(Solver::SPECIAL_VALUE_BV_ONES, bzla_res);
  }
  else if (value == SPECIAL_VALUE_BV_MIN_SIGNED)
  {
    bzla_res = bitwuzla_mk_bv_min_signed(d_solver, bzla_sort);
    if (check) check_is_bv_const(Solver::SPECIAL_VALUE_BV_MIN_SIGNED, bzla_res);
  }
  else
  {
    assert(value == SPECIAL_VALUE_BV_MAX_SIGNED);
    bzla_res = bitwuzla_mk_bv_max_signed(d_solver, bzla_sort);
    if (check) check_is_bv_const(Solver::SPECIAL_VALUE_BV_MAX_SIGNED, bzla_res);
  }
  assert(bzla_res);
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(d_solver, bzla_res));
  assert(res);
  return res;
}

Term
CBzlaSolver::mk_term(const OpKind& kind,
                    std::vector<Term>& args,
                    std::vector<uint32_t>& params)
{
  BitwuzlaTerm* bzla_res = nullptr;
  size_t n_args           = args.size();
  size_t n_params         = params.size();
  std::vector<BitwuzlaTerm*> vars;
  std::vector<BitwuzlaTerm*> btor_args = terms_to_btor_terms(args);

  if (kind == Op::DISTINCT)
  {
    assert(n_args > 1);
    bzla_res = mk_term_pairwise(btor_args, boolector_ne);
  }
  else if (kind == Op::EQUAL)
  {
    assert(n_args > 1);
    bzla_res = mk_term_chained(btor_args, boolector_eq);
  }
  else if (kind == Op::BV_COMP)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_eq);
  }
  else if (kind == Op::IFF)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_iff);
  }
  else if (kind == Op::ITE)
  {
    assert(n_args == 3);
    bzla_res =
        boolector_cond(d_solver, btor_args[0], btor_args[1], btor_args[2]);
  }
  else if (kind == Op::IMPLIES)
  {
    assert(n_args > 1);
    bzla_res = mk_term_left_assoc(btor_args, boolector_implies);
  }
  else if (kind == Op::BV_EXTRACT)
  {
    assert(n_args == 1);
    assert(n_params == 2);
    bzla_res = boolector_slice(d_solver, btor_args[0], params[0], params[1]);
  }
  else if (kind == Op::BV_REPEAT)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    bzla_res = boolector_repeat(d_solver, btor_args[0], params[0]);
  }
  else if (kind == Op::BV_ROTATE_LEFT || kind == Op::BV_ROTATE_RIGHT)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    BitwuzlaTerm* arg = btor_args[0];
    BitwuzlaSort s    = boolector_get_sort(d_solver, arg);
    uint32_t bw        = boolector_bitvec_sort_get_width(d_solver, s);

    /* use boolector_rori vs boolector_ror with 50% probability */
    if (d_rng.flip_coin())
    {
      bzla_res = (kind == Op::BV_ROTATE_LEFT)
                     ? boolector_roli(d_solver, arg, params[0])
                     : boolector_rori(d_solver, arg, params[0]);
    }
    else
    {
      BitwuzlaTerm* tmp;
      /* use same bit-width vs log2 bit-width (if possible) with 50% prob
       */
      if (bw > 1 && is_power_of_2(bw) && d_rng.flip_coin())
      {
        /* arg has bw that is power of 2, nbits argument with log2 bw */
        uint32_t bw2     = static_cast<uint32_t>(log2(bw));
        BitwuzlaSort s2 = boolector_bitvec_sort(d_solver, bw2);
        uint32_t nbits   = params[0] % bw;
        tmp              = boolector_unsigned_int(d_solver, nbits, s2);
        boolector_release_sort(d_solver, s2);
      }
      else
      {
        /* arg and nbits argument with same bw */
        tmp = boolector_unsigned_int(d_solver, params[0], s);
      }
      bzla_res = (kind == Op::BV_ROTATE_LEFT)
                     ? boolector_rol(d_solver, arg, tmp)
                     : boolector_ror(d_solver, arg, tmp);
      boolector_release(d_solver, tmp);
    }
  }
  else if (kind == Op::BV_SIGN_EXTEND)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    bzla_res = boolector_sext(d_solver, btor_args[0], params[0]);
  }
  else if (kind == Op::BV_ZERO_EXTEND)
  {
    assert(n_args == 1);
    assert(n_params == 1);
    bzla_res = boolector_uext(d_solver, btor_args[0], params[0]);
  }
  else if (kind == Op::BV_CONCAT)
  {
    assert(n_args > 1);
    bzla_res = mk_term_left_assoc(btor_args, boolector_concat);
  }
  else if (kind == Op::AND || kind == Op::BV_AND)
  {
    assert(n_args > 1);
    bzla_res = mk_term_left_assoc(btor_args, boolector_and);
  }
  else if (kind == Op::OR || kind == Op::BV_OR)
  {
    assert(n_args > 1);
    bzla_res = mk_term_left_assoc(btor_args, boolector_or);
  }
  else if (kind == Op::XOR || kind == Op::BV_XOR)
  {
    assert(n_args > 1);
    bzla_res = mk_term_left_assoc(btor_args, boolector_xor);
  }
  else if (kind == Op::BV_MULT)
  {
    assert(n_args > 1);
    bzla_res = mk_term_left_assoc(btor_args, boolector_mul);
  }
  else if (kind == Op::BV_ADD)
  {
    assert(n_args > 1);
    bzla_res = mk_term_left_assoc(btor_args, boolector_add);
  }
  else if (kind == Op::NOT || kind == Op::BV_NOT)
  {
    assert(n_args == 1);
    bzla_res = boolector_not(d_solver, btor_args[0]);
  }
  else if (kind == Op::BV_NEG)
  {
    assert(n_args == 1);
    bzla_res = boolector_neg(d_solver, btor_args[0]);
  }
  else if (kind == Op::BV_NAND)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_nand);
  }
  else if (kind == Op::BV_NOR)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_nor);
  }
  else if (kind == Op::BV_XNOR)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_xnor);
  }
  else if (kind == Op::BV_SUB)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_sub);
  }
  else if (kind == Op::BV_UDIV)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_udiv);
  }
  else if (kind == Op::BV_UREM)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_urem);
  }
  else if (kind == Op::BV_SDIV)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_sdiv);
  }
  else if (kind == Op::BV_SREM)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_srem);
  }
  else if (kind == Op::BV_SMOD)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_smod);
  }
  else if (kind == Op::BV_SHL)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_sll);
  }
  else if (kind == Op::BV_LSHR)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_srl);
  }
  else if (kind == Op::BV_ASHR)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_sra);
  }
  else if (kind == Op::BV_UGT)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_ugt);
  }
  else if (kind == Op::BV_UGE)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_ugte);
  }
  else if (kind == Op::BV_ULT)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_ult);
  }
  else if (kind == Op::BV_ULE)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_ulte);
  }
  else if (kind == Op::BV_SGT)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_sgt);
  }
  else if (kind == Op::BV_SGE)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_sgte);
  }
  else if (kind == Op::BV_SLT)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_slt);
  }
  else if (kind == Op::BV_SLE)
  {
    assert(n_args == 2);
    bzla_res = mk_term_left_assoc(btor_args, boolector_slte);
  }
  else if (kind == Op::ARRAY_SELECT)
  {
    assert(n_args == 2);
    bzla_res = boolector_read(d_solver, btor_args[0], btor_args[1]);
  }
  else if (kind == Op::ARRAY_STORE)
  {
    assert(n_args == 3);
    bzla_res =
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
      bzla_res = boolector_exists(
          d_solver, vars.data(), vars.size(), btor_args.back());
    }
    else
    {
      bzla_res = boolector_forall(
          d_solver, vars.data(), vars.size(), btor_args.back());
    }
  }
  else if (kind == Op::UF_APPLY)
  {
    bzla_res = boolector_apply(
        d_solver, btor_args.data() + 1, n_args - 1, btor_args[0]);
  }
  else
  {
    /* solver-specific operators */
    if (kind == CBzlaSolver::OP_REDAND)
    {
      assert(n_args == 1);
      bzla_res = boolector_redand(d_solver, btor_args[0]);
    }
    else if (kind == CBzlaSolver::OP_REDOR)
    {
      assert(n_args == 1);
      bzla_res = boolector_redor(d_solver, btor_args[0]);
    }
    else if (kind == CBzlaSolver::OP_REDXOR)
    {
      assert(n_args == 1);
      bzla_res = boolector_redxor(d_solver, btor_args[0]);
    }
    else if (kind == CBzlaSolver::OP_INC)
    {
      assert(n_args == 1);
      bzla_res = boolector_inc(d_solver, btor_args[0]);
    }
    else if (kind == CBzlaSolver::OP_DEC)
    {
      assert(n_args == 1);
      bzla_res = boolector_dec(d_solver, btor_args[0]);
    }
    else if (kind == CBzlaSolver::OP_UADDO)
    {
      assert(n_args == 2);
      bzla_res = mk_term_left_assoc(btor_args, boolector_uaddo);
    }
    else if (kind == CBzlaSolver::OP_UMULO)
    {
      assert(n_args == 2);
      bzla_res = mk_term_left_assoc(btor_args, boolector_umulo);
    }
    else if (kind == CBzlaSolver::OP_USUBO)
    {
      assert(n_args == 2);
      bzla_res = mk_term_left_assoc(btor_args, boolector_usubo);
    }
    else if (kind == CBzlaSolver::OP_SADDO)
    {
      assert(n_args == 2);
      bzla_res = mk_term_left_assoc(btor_args, boolector_saddo);
    }
    else if (kind == CBzlaSolver::OP_SDIVO)
    {
      assert(n_args == 2);
      bzla_res = mk_term_left_assoc(btor_args, boolector_sdivo);
    }
    else if (kind == CBzlaSolver::OP_SMULO)
    {
      assert(n_args == 2);
      bzla_res = mk_term_left_assoc(btor_args, boolector_smulo);
    }
    else if (kind == CBzlaSolver::OP_SSUBO)
    {
      assert(n_args == 2);
      bzla_res = mk_term_left_assoc(btor_args, boolector_ssubo);
    }
    else
    {
      assert(false);
    }
  }
  assert(bzla_res);
  assert(!d_rng.pick_with_prob(1) || boolector_get_refs(d_solver) > 0);
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(d_solver, bzla_res));
  assert(res);
  boolector_release(d_solver, bzla_res);
  return res;
}

Sort
CBzlaSolver::get_sort(Term term, SortKind sort_kind) const
{
  (void) sort_kind;
  return std::shared_ptr<CBzlaSort>(new CBzlaSort(
      d_solver, boolector_get_sort(d_solver, get_bzla_term(term))));
}

void
CBzlaSolver::assert_formula(const Term& t)
{
  boolector_assert(d_solver, get_bzla_term(t));
}

Solver::Result
CBzlaSolver::check_sat()
{
  int32_t res = boolector_sat(d_solver);
  if (res == BOOLECTOR_SAT) return Result::SAT;
  if (res == BOOLECTOR_UNSAT) return Result::UNSAT;
  assert(res == BOOLECTOR_UNKNOWN);
  return Result::UNKNOWN;
}

Solver::Result
CBzlaSolver::check_sat_assuming(std::vector<Term>& assumptions)
{
  int32_t res;
  for (const Term& t : assumptions)
  {
    boolector_assume(d_solver, get_bzla_term(t));
  }
  res = boolector_sat(d_solver);
  if (res == BOOLECTOR_SAT) return Result::SAT;
  if (res == BOOLECTOR_UNSAT) return Result::UNSAT;
  assert(res == BOOLECTOR_UNKNOWN);
  return Result::UNKNOWN;
}

std::vector<Term>
CBzlaSolver::get_unsat_assumptions()
{
  std::vector<Term> res;
  BitwuzlaTerm** bzla_res = boolector_get_failed_assumptions(d_solver);
  for (uint32_t i = 0; bzla_res[i] != nullptr; ++i)
  {
    res.push_back(
        std::shared_ptr<CBzlaTerm>(new CBzlaTerm(d_solver, bzla_res[i])));
  }
  return res;
}

std::vector<Term>
CBzlaSolver::get_value(std::vector<Term>& terms)
{
  std::vector<Term> res;
  std::vector<BitwuzlaTerm*> bzla_res;
  std::vector<BitwuzlaTerm*> btor_terms = terms_to_btor_terms(terms);

  for (BitwuzlaTerm* t : btor_terms)
  {
    bzla_res.push_back(boolector_get_value(d_solver, t));
  }
  res = btor_terms_to_terms(bzla_res);
  for (BitwuzlaTerm* t : bzla_res)
  {
    boolector_release(d_solver, t);
  }
  return res;
}

void
CBzlaSolver::push(uint32_t n_levels)
{
  boolector_push(d_solver, n_levels);
}

void
CBzlaSolver::pop(uint32_t n_levels)
{
  boolector_pop(d_solver, n_levels);
}

void
CBzlaSolver::print_model()
{
  const char* fmt = d_rng.flip_coin() ? "btor" : "smt2";
  boolector_print_model(d_solver, (char*) fmt, stdout);
}

void
CBzlaSolver::reset_assertions()
{
  /* boolector does not support this yet */
}

/* -------------------------------------------------------------------------- */

std::vector<std::string>
CBzlaSolver::get_supported_sat_solvers()
{
  return {"cadical", "cms", "lingeling", "minisat", "picosat"};
}

bool
CBzlaSolver::check_unsat_assumption(const Term& t) const
{
  return boolector_failed(d_solver, get_bzla_term(t));
}

/* -------------------------------------------------------------------------- */

BitwuzlaSort
CBzlaSolver::get_bzla_sort(Sort sort) const
{
  CBzlaSort* bzla_sort = dynamic_cast<CBzlaSort*>(sort.get());
  assert(bzla_sort);
  return bzla_sort->d_sort;
}

BitwuzlaTerm*
CBzlaSolver::get_bzla_term(Term term) const
{
  CBzlaTerm* btor_term = dynamic_cast<CBzlaTerm*>(term.get());
  assert(btor_term);
  return btor_term->d_term;
}

BitwuzlaTerm*
CBzlaSolver::mk_term_left_assoc(std::vector<BitwuzlaTerm*>& args,
                               BitwuzlaTerm* (*fun)(Btor*,
                                                     BitwuzlaTerm*,
                                                     BitwuzlaTerm*) ) const
{
  assert(args.size() >= 2);
  BitwuzlaTerm *res, *tmp;

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

BitwuzlaTerm*
CBzlaSolver::mk_term_pairwise(std::vector<BitwuzlaTerm*>& args,
                             BitwuzlaTerm* (*fun)(Btor*,
                                                   BitwuzlaTerm*,
                                                   BitwuzlaTerm*) ) const
{
  assert(args.size() >= 2);
  BitwuzlaTerm *res, *tmp, *old;

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

BitwuzlaTerm*
CBzlaSolver::mk_term_chained(std::vector<BitwuzlaTerm*>& args,
                            BitwuzlaTerm* (*fun)(Btor*,
                                                  BitwuzlaTerm*,
                                                  BitwuzlaTerm*) ) const
{
  assert(args.size() >= 2);
  BitwuzlaTerm *res, *tmp, *old;

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
CBzlaSolver::set_opt(const std::string& opt, const std::string& value)
{
  if (opt == "produce-unsat-assumptions")
  {
    /* always enabled in Boolector, can not be configured via set_opt */
    return;
  }

  assert(d_option_name_to_enum.find(opt) != d_option_name_to_enum.end());

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
CBzlaSolver::get_option_name_incremental() const
{
  return boolector_get_opt_lng(d_solver, BTOR_OPT_INCREMENTAL);
}

std::string
CBzlaSolver::get_option_name_model_gen() const
{
  return boolector_get_opt_lng(d_solver, BTOR_OPT_MODEL_GEN);
}

std::string
CBzlaSolver::get_option_name_unsat_assumptions() const
{
  /* always enabled in Boolector, can not be configured via set_opt */
  return "produce-unsat-assumptions";
}

bool
CBzlaSolver::option_incremental_enabled() const
{
  return boolector_get_opt(d_solver, BTOR_OPT_INCREMENTAL) > 0;
}

bool
CBzlaSolver::option_model_gen_enabled() const
{
  return boolector_get_opt(d_solver, BTOR_OPT_MODEL_GEN) > 0;
}

bool
CBzlaSolver::option_unsat_assumptions_enabled() const
{
  /* always enabled in Boolector, can not be configured via set_opt */
  return true;
}

/* -------------------------------------------------------------------------- */

void
CBzlaSolver::init_op_kinds()
{
  d_op_kinds = {
      /* Special Cases */
      {Op::UNDEFINED, BITWUZLA_KIND_NUM_OPS},
      {Op::DISTINCT, BITWUZLA_KIND_DISTINCT},
      {Op::EQUAL, BITWUZLA_KIND_EQUAL},
      {Op::ITE, BITWUZLA_KIND_ITE},

      /* Bool */
      {Op::AND, BITWUZLA_KIND_AND},
      {Op::OR, BITWUZLA_KIND_OR},
      {Op::NOT, BITWUZLA_KIND_NOT},
      {Op::XOR, BITWUZLA_KIND_XOR},
      {Op::IMPLIES, BITWUZLA_KIND_IMPLIES},

      /* Arrays */
      {Op::ARRAY_SELECT, BITWUZLA_KIND_ARRAY_SELECT},
      {Op::ARRAY_STORE, BITWUZLA_KIND_ARRAY_STORE},

      /* BV */
      {Op::BV_EXTRACT, BITWUZLA_KIND_BV_EXTRACT},
      {Op::BV_REPEAT, BITWUZLA_KIND_BV_REPEAT},
      {Op::BV_ROTATE_LEFT, BITWUZLA_KIND_BV_ROLI},
      {Op::BV_ROTATE_RIGHT, BITWUZLA_KIND_BV_RORI},
      {Op::BV_SIGN_EXTEND, BITWUZLA_KIND_BV_SIGN_EXTEND},
      {Op::BV_ZERO_EXTEND, BITWUZLA_KIND_BV_ZERO_EXTEND},

      {Op::BV_CONCAT, BITWUZLA_KIND_BV_CONCAT},
      {Op::BV_AND, BITWUZLA_KIND_BV_AND},
      {Op::BV_OR, BITWUZLA_KIND_BV_OR},
      {Op::BV_XOR, BITWUZLA_KIND_BV_XOR},
      {Op::BV_MULT, BITWUZLA_KIND_BV_MULT},
      {Op::BV_ADD, BITWUZLA_KIND_BV_PLUS},
      {Op::BV_NOT, BITWUZLA_KIND_BV_NOT},
      {Op::BV_NEG, BITWUZLA_KIND_BV_NEG},
      {Op::BV_NAND, BITWUZLA_KIND_BV_NAND},
      {Op::BV_NOR, BITWUZLA_KIND_BV_NOR},
      {Op::BV_XNOR, BITWUZLA_KIND_BV_XNOR},
      {Op::BV_COMP, BITWUZLA_KIND_BV_COMP},
      {Op::BV_SUB, BITWUZLA_KIND_BV_SUB},
      {Op::BV_UDIV, BITWUZLA_KIND_BV_UDIV},
      {Op::BV_UREM, BITWUZLA_KIND_BV_UREM},
      {Op::BV_UREM, BITWUZLA_KIND_BV_UREM},
      {Op::BV_SDIV, BITWUZLA_KIND_BV_SDIV},
      {Op::BV_SREM, BITWUZLA_KIND_BV_SREM},
      {Op::BV_SMOD, BITWUZLA_KIND_BV_SMOD},
      {Op::BV_SHL, BITWUZLA_KIND_BV_SHL},
      {Op::BV_LSHR, BITWUZLA_KIND_BV_LSHR},
      {Op::BV_ASHR, BITWUZLA_KIND_BV_ASHR},
      {Op::BV_ULT, BITWUZLA_KIND_BV_ULT},
      {Op::BV_ULE, BITWUZLA_KIND_BV_ULE},
      {Op::BV_UGT, BITWUZLA_KIND_BV_UGT},
      {Op::BV_UGE, BITWUZLA_KIND_BV_UGE},
      {Op::BV_SLT, BITWUZLA_KIND_BV_SLT},
      {Op::BV_SLE, BITWUZLA_KIND_BV_SLE},
      {Op::BV_SGT, BITWUZLA_KIND_BV_SGT},
      {Op::BV_SGE, BITWUZLA_KIND_BV_SGE},

      /* FP */
      // TODO
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
      {OP_ROL, BITWUZLA_KIND_BV_ROL},
      {OP_ROR, BITWUZLA_KIND_BV_ROR},
      {OP_REDOR, CVC4::api::Kind::BITVECTOR_REDOR},
      {OP_REDAND, CVC4::api::Kind::BITVECTOR_REDAND},
      {OP_STRING_UPDATE, CVC4::api::Kind::STRING_UPDATE},
      {OP_STRING_TOLOWER, CVC4::api::Kind::STRING_TOLOWER},
      {OP_STRING_TOUPPER, CVC4::api::Kind::STRING_TOUPPER},
      {OP_STRING_REV, CVC4::api::Kind::STRING_REV},
  };
}
std::vector<Term>
CBzlaSolver::btor_terms_to_terms(std::vector<BitwuzlaTerm*>& terms) const
{
  std::vector<Term> res;
  for (BitwuzlaTerm* t : terms)
  {
    res.push_back(std::shared_ptr<CBzlaTerm>(new CBzlaTerm(d_solver, t)));
  }
  return res;
}

std::vector<BitwuzlaTerm*>
CBzlaSolver::terms_to_btor_terms(std::vector<Term>& terms) const
{
  std::vector<BitwuzlaTerm*> res;
  for (Term& t : terms)
  {
    res.push_back(get_bzla_term(t));
  }
  return res;
}

CBzlaSolver::BtorFunBoolUnary
CBzlaSolver::pick_fun_bool_unary(BtorFunBoolUnaryVector& funs) const
{
  return d_rng.pick_from_set<BtorFunBoolUnaryVector, BtorFunBoolUnary>(funs);
}

CBzlaSolver::BtorFunBoolUnary
CBzlaSolver::pick_fun_is_bv_const() const
{
  BtorFunBoolUnaryVector funs = {boolector_is_bv_const_zero,
                                 boolector_is_bv_const_one,
                                 boolector_is_bv_const_ones,
                                 boolector_is_bv_const_max_signed,
                                 boolector_is_bv_const_min_signed};
  return pick_fun_bool_unary(funs);
}

void
CBzlaSolver::check_is_bv_const(const Solver::SpecialValueKind& kind,
                              BitwuzlaTerm* node) const
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

const OpKind CBzlaSolver::OP_DEC    = "btor-OP_DEC";
const OpKind CBzlaSolver::OP_INC    = "btor-OP_INC";
const OpKind CBzlaSolver::OP_REDAND = "btor-OP_REDAND";
const OpKind CBzlaSolver::OP_REDOR  = "btor-OP_REDOR";
const OpKind CBzlaSolver::OP_REDXOR = "btor-OP_REDXOR";
const OpKind CBzlaSolver::OP_UADDO  = "btor-OP_UADDO";
const OpKind CBzlaSolver::OP_UMULO  = "btor-OP_UMULO";
const OpKind CBzlaSolver::OP_USUBO  = "btor-OP_USUBO";
const OpKind CBzlaSolver::OP_SADDO  = "btor-OP_SADDO";
const OpKind CBzlaSolver::OP_SDIVO  = "btor-OP_SDIVO";
const OpKind CBzlaSolver::OP_SMULO  = "btor-OP_SMULO";
const OpKind CBzlaSolver::OP_SSUBO  = "btor-OP_SSUBO";

void
CBzlaSolver::configure_smgr(SolverManager* smgr) const
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

const ActionKind CBzlaSolver::ACTION_OPT_ITERATOR  = "btor-opt-iterator";
const ActionKind CBzlaSolver::ACTION_BV_ASSIGNMENT = "btor-bv-assignment";
const ActionKind CBzlaSolver::ACTION_CLONE         = "btor-clone";
const ActionKind CBzlaSolver::ACTION_FAILED        = "btor-failed";
const ActionKind CBzlaSolver::ACTION_FIXATE_ASSUMPTIONS =
    "btor-fixate-assumptions";
const ActionKind CBzlaSolver::ACTION_RESET_ASSUMPTIONS =
    "btor-reset-assumptions";
const ActionKind CBzlaSolver::ACTION_RELEASE_ALL    = "btor-release-all";
const ActionKind CBzlaSolver::ACTION_SIMPLIFY       = "btor-simplify";
const ActionKind CBzlaSolver::ACTION_SET_SAT_SOLVER = "btor-set-sat-solver";
const ActionKind CBzlaSolver::ACTION_SET_SYMBOL     = "btor-set-symbol";

const StateKind CBzlaSolver::STATE_FIX_RESET_ASSUMPTIONS =
    "btor-fix-reset-assumptions";

class BtorActionBvAssignment : public Action
{
 public:
  BtorActionBvAssignment(SolverManager& smgr)
      : Action(smgr, CBzlaSolver::ACTION_BV_ASSIGNMENT, false)
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
    assert(tokens.size() == 0);
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
    CBzlaSolver& btor_solver = static_cast<CBzlaSolver&>(d_smgr.get_solver());
    std::vector<const char*> assignments;
    for (uint64_t i = 0; i < n; ++i)
    {
      Term t                    = d_smgr.pick_term(SORT_BV);
      const char* bv_assignment = boolector_bv_assignment(
          btor_solver.get_solver(), btor_solver.get_bzla_term(t));
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
      : Action(smgr, CBzlaSolver::ACTION_CLONE, false)
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
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    CBzlaSolver& solver = static_cast<CBzlaSolver&>(d_smgr.get_solver());
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
        BitwuzlaTerm *t_btor, *t_clone;
        BitwuzlaSort sort;
        int32_t id;
        const char* s;
        std::string symbol;

        t_btor = solver.get_bzla_term(t);
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
      : Action(smgr, CBzlaSolver::ACTION_FAILED, false)
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
    assert(tokens.size() == 1);
    Term term = d_smgr.get_term(str_to_uint32(tokens[0]));
    assert(term != nullptr);
    _run(term);
    return 0;
  }

 private:
  void _run(Term term)
  {
    SMTMBT_TRACE << get_kind() << " " << term;
    CBzlaSolver& btor_solver = static_cast<CBzlaSolver&>(d_smgr.get_solver());
    (void) boolector_failed(btor_solver.get_solver(),
                            btor_solver.get_bzla_term(term));
  }
};

class BtorActionFixateAssumptions : public Action
{
 public:
  BtorActionFixateAssumptions(SolverManager& smgr)
      : Action(smgr, CBzlaSolver::ACTION_FIXATE_ASSUMPTIONS, false)
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
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    d_smgr.clear();
    boolector_fixate_assumptions(
        static_cast<CBzlaSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionOptIterator : public Action
{
 public:
  BtorActionOptIterator(SolverManager& smgr)
      : Action(smgr, CBzlaSolver::ACTION_OPT_ITERATOR, false)
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
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    Btor* btor = static_cast<CBzlaSolver&>(d_smgr.get_solver()).get_solver();
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
      : Action(smgr, CBzlaSolver::ACTION_RELEASE_ALL, false)
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
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    d_smgr.clear();
    boolector_release_all(
        static_cast<CBzlaSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionResetAssumptions : public Action
{
 public:
  BtorActionResetAssumptions(SolverManager& smgr)
      : Action(smgr, CBzlaSolver::ACTION_RESET_ASSUMPTIONS, false)
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
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    d_smgr.clear();
    boolector_reset_assumptions(
        static_cast<CBzlaSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionSetSatSolver : public Action
{
 public:
  BtorActionSetSatSolver(SolverManager& smgr)
      : Action(smgr, CBzlaSolver::ACTION_SET_SAT_SOLVER, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    CBzlaSolver& solver = static_cast<CBzlaSolver&>(d_smgr.get_solver());
    std::string sat_solver =
        d_rng.pick_from_set<std::vector<std::string>, std::string>(
            solver.get_supported_sat_solvers());
    _run(sat_solver);
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.size() == 1);
    _run(tokens[0]);
    return 0;
  }

 private:
  void _run(std::string sat_solver)
  {
    SMTMBT_TRACE << get_kind() << " " << sat_solver;
    CBzlaSolver& solver = static_cast<CBzlaSolver&>(d_smgr.get_solver());
    boolector_set_sat_solver(solver.get_solver(), sat_solver.c_str());
  }
};

class BtorActionSimplify : public Action
{
 public:
  BtorActionSimplify(SolverManager& smgr)
      : Action(smgr, CBzlaSolver::ACTION_SIMPLIFY, false)
  {
  }

  bool run() override
  {
    assert(d_solver.is_initialized());
    CBzlaSolver& solver = static_cast<CBzlaSolver&>(d_smgr.get_solver());
    if (solver.get_solver() == nullptr) return false;
    _run();
    return true;
  }

  uint64_t untrace(std::vector<std::string>& tokens) override
  {
    assert(tokens.empty());
    _run();
    return 0;
  }

 private:
  void _run()
  {
    SMTMBT_TRACE << get_kind();
    boolector_simplify(
        static_cast<CBzlaSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionSetSymbol : public Action
{
 public:
  BtorActionSetSymbol(SolverManager& smgr)
      : Action(smgr, CBzlaSolver::ACTION_SET_SYMBOL, false)
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
    assert(tokens.size() == 2);
    Term term = d_smgr.get_term(str_to_uint32(tokens[0]));
    assert(term != nullptr);
    std::string symbol = str_to_str(tokens[1]);
    _run(term, symbol);
    return 0;
  }

 private:
  void _run(Term term, std::string symbol)
  {
    SMTMBT_TRACE << get_kind() << " " << term << " \"" << symbol << "\"";
    CBzlaSolver& btor_solver = static_cast<CBzlaSolver&>(d_smgr.get_solver());
    (void) boolector_set_symbol(btor_solver.get_solver(),
                                btor_solver.get_bzla_term(term),
                                symbol.c_str());
  }
};

/* -------------------------------------------------------------------------- */

void
CBzlaSolver::configure_fsm(FSM* fsm) const
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
