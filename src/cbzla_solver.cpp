#ifdef SMTMBT_USE_CBITWUZLA

#include "cbzla_solver.hpp"

#include <bitset>
#include <cassert>
#include <cstdlib>

#include "config.hpp"
#include "except.hpp"
#include "theory.hpp"
#include "util.hpp"

namespace smtmbt {
namespace cbzla {

/* -------------------------------------------------------------------------- */
/* CBzlaSort                                                                   */
/* -------------------------------------------------------------------------- */

CBzlaSort::CBzlaSort(Bitwuzla* cbzla, BitwuzlaSort* sort)
    : d_solver(cbzla), d_sort(sort)
{
}

CBzlaSort::~CBzlaSort() {}

size_t
CBzlaSort::hash() const
{
  return bitwuzla_sort_hash(d_sort);
}

bool
CBzlaSort::equals(const Sort& other) const
{
  CBzlaSort* cbzla_sort = dynamic_cast<CBzlaSort*>(other.get());
  if (cbzla_sort)
  {
    return d_sort == cbzla_sort->d_sort;
  }
  return false;
}

bool
CBzlaSort::is_array() const
{
  return bitwuzla_sort_is_array(d_sort);
}

bool
CBzlaSort::is_bool() const
{
  BitwuzlaSort* s = bitwuzla_mk_bool_sort(d_solver);
  bool res       = s == d_sort;
  return res && d_kind == SORT_BOOL;
}

bool
CBzlaSort::is_bv() const
{
  return bitwuzla_sort_is_bv(d_sort);
}

bool
CBzlaSort::is_fp() const
{
  return bitwuzla_sort_is_fp(d_sort);
}

bool
CBzlaSort::is_fun() const
{
  return bitwuzla_sort_is_fun(d_sort);
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
  return bitwuzla_sort_is_rm(d_sort);
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
  uint32_t res = bitwuzla_sort_bv_get_size(d_sort);
  assert(res);
  return res;
}

uint32_t
CBzlaSort::get_fp_exp_size() const
{
  assert(is_fp());
  uint32_t res = bitwuzla_sort_fp_get_exp_size(d_sort);
  assert(res);
  return res;
}

uint32_t
CBzlaSort::get_fp_sig_size() const
{
  assert(is_fp());
  uint32_t res = bitwuzla_sort_fp_get_sig_size(d_sort);
  assert(res);
  return res;
}

/* -------------------------------------------------------------------------- */
/* CBzlaTerm                                                                   */
/* -------------------------------------------------------------------------- */

CBzlaTerm::CBzlaTerm(BitwuzlaTerm* term) : d_term(term) {}

CBzlaTerm::~CBzlaTerm() {}

size_t
CBzlaTerm::hash() const
{
  return bitwuzla_term_hash(d_term);
}

bool
CBzlaTerm::equals(const Term& other) const
{
  CBzlaTerm* cbzla_term = dynamic_cast<CBzlaTerm*>(other.get());
  return bitwuzla_term_is_equal_sort(d_term, cbzla_term->d_term);
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

CBzlaSolver::~CBzlaSolver()
{
  if (d_solver)
  {
    bitwuzla_delete(d_solver);
    d_solver = nullptr;
  }
}

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

Bitwuzla*
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
  // TODO enable when Mathias' cbitwuzla quantifiers branch is merged back
  return {
      THEORY_ARRAY, THEORY_BV, THEORY_BOOL, THEORY_FP, /*THEORY_QUANT,*/ THEORY_UF};
}

OpKindSet
CBzlaSolver::get_unsupported_op_kinds() const
{
  return {Op::FP_TO_REAL};
}

SortKindSet
CBzlaSolver::get_unsupported_var_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN, SORT_FP};
}

SortKindSet
CBzlaSolver::get_unsupported_array_index_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
}

SortKindSet
CBzlaSolver::get_unsupported_array_element_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
}

SortKindSet
CBzlaSolver::get_unsupported_fun_domain_sort_kinds() const
{
  return {SORT_ARRAY, SORT_FUN};
}

Sort
CBzlaSolver::mk_sort(SortKind kind)
{
  assert(kind == SORT_BOOL || kind == SORT_RM);
  BitwuzlaSort* cbzla_res;

  cbzla_res = kind == SORT_BOOL ? bitwuzla_mk_bool_sort(d_solver)
                                : bitwuzla_mk_rm_sort(d_solver);
  assert(cbzla_res);
  std::shared_ptr<CBzlaSort> res(new CBzlaSort(d_solver, cbzla_res));
  assert(res);
  return res;
}

Sort
CBzlaSolver::mk_sort(SortKind kind, uint32_t size)
{
  assert(kind == SORT_BV);
  BitwuzlaSort* cbzla_res = bitwuzla_mk_bv_sort(d_solver, size);
  assert(cbzla_res);
  std::shared_ptr<CBzlaSort> res(new CBzlaSort(d_solver, cbzla_res));
  assert(res);
  return res;
}

Sort
CBzlaSolver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  assert(kind == SORT_FP);
  BitwuzlaSort* cbzla_res = bitwuzla_mk_fp_sort(d_solver, esize, ssize);
  assert(cbzla_res);
  std::shared_ptr<CBzlaSort> res(new CBzlaSort(d_solver, cbzla_res));
  assert(res);
  return res;
}

Sort
CBzlaSolver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  BitwuzlaSort* cbzla_res;

  switch (kind)
  {
    case SORT_ARRAY:
      cbzla_res = bitwuzla_mk_array_sort(
          d_solver, get_bzla_sort(sorts[0]), get_bzla_sort(sorts[1]));
      break;

    case SORT_FUN:
    {
      BitwuzlaSort* codomain = get_bzla_sort(sorts.back());
      std::vector<BitwuzlaSort*> domain;
      for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
      {
        domain.push_back(get_bzla_sort(*it));
      }
      cbzla_res = bitwuzla_mk_fun_sort(
          d_solver, domain.size(), domain.data(), codomain);
      break;
    }

    default: assert(false);
  }
  std::shared_ptr<CBzlaSort> res(new CBzlaSort(d_solver, cbzla_res));
  assert(cbzla_res);
  assert(res);
  return res;
}

Term
CBzlaSolver::mk_var(Sort sort, const std::string& name)
{
  BitwuzlaTerm* cbzla_res;
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

  cbzla_res = bitwuzla_mk_var(d_solver, get_bzla_sort(sort), cname);
  assert(cbzla_res);
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(cbzla_res));
  assert(res);
  return res;
}

Term
CBzlaSolver::mk_const(Sort sort, const std::string& name)
{
  BitwuzlaTerm* cbzla_res;
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

  cbzla_res = bitwuzla_mk_const(d_solver, get_bzla_sort(sort), cname);
  assert(cbzla_res);
  if (d_rng.pick_with_prob(1))
  {
    assert(bitwuzla_term_is_equal_sort(cbzla_res, cbzla_res));
  }
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(cbzla_res));
  assert(res);
  return res;
}

Term
CBzlaSolver::mk_value(Sort sort, bool value)
{
  assert(sort->is_bool());
  BitwuzlaTerm* cbzla_res =
      value ? bitwuzla_mk_true(d_solver) : bitwuzla_mk_false(d_solver);
  assert(cbzla_res);
  if (d_rng.pick_with_prob(10))
  {
    if (value)
    {
      check_is_bv_value(Solver::SPECIAL_VALUE_BV_ONE, cbzla_res);
    }
    else
    {
      check_is_bv_value(Solver::SPECIAL_VALUE_BV_ZERO, cbzla_res);
    }
  }
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(cbzla_res));
  assert(res);
  return res;
}

BitwuzlaTerm*
CBzlaSolver::mk_value_bv_uint64(Sort sort, uint64_t value)
{
  assert(sort->is_bv());
  BitwuzlaSort* cbzla_sort = get_bzla_sort(sort);
  BitwuzlaTerm* cbzla_res =
      bitwuzla_mk_bv_value_uint64(d_solver, cbzla_sort, value);
  assert(cbzla_res);
  return cbzla_res;
}

Term
CBzlaSolver::mk_value(Sort sort, std::string value, Base base)
{
  assert(sort->is_bv());

  BitwuzlaTerm* cbzla_res;
  BitwuzlaSort* cbzla_sort = get_bzla_sort(sort);
  uint32_t bw            = sort->get_bv_size();
  int32_t ibase;
  BitwuzlaBVBase cbase;

  if (base == DEC)
  {
    ibase = 10;
    cbase = BITWUZLA_BV_BASE_DEC;
  }
  else if (base == HEX)
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
    cbzla_res =
        mk_value_bv_uint64(sort, strtoull(value.c_str(), nullptr, ibase));
  }
  else
  {
    cbzla_res =
        bitwuzla_mk_bv_value(d_solver, cbzla_sort, value.c_str(), cbase);
  }
  assert(cbzla_res);
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(cbzla_res));
  assert(res);
  return res;
}

Term
CBzlaSolver::mk_special_value(Sort sort, const SpecialValueKind& value)
{
  BitwuzlaTerm* cbzla_res  = 0;
  BitwuzlaSort* cbzla_sort = get_bzla_sort(sort);
  bool check               = d_rng.pick_with_prob(10);
  std::string str;

  switch (sort->get_kind())
  {
    case SORT_BV:
      if (value == SPECIAL_VALUE_BV_ZERO)
      {
        cbzla_res = bitwuzla_mk_bv_zero(d_solver, cbzla_sort);
        if (check) check_is_bv_value(Solver::SPECIAL_VALUE_BV_ZERO, cbzla_res);
      }
      else if (value == SPECIAL_VALUE_BV_ONE)
      {
        cbzla_res = bitwuzla_mk_bv_one(d_solver, cbzla_sort);
        if (check) check_is_bv_value(Solver::SPECIAL_VALUE_BV_ONE, cbzla_res);
      }
      else if (value == SPECIAL_VALUE_BV_ONES)
      {
        cbzla_res = bitwuzla_mk_bv_ones(d_solver, cbzla_sort);
        if (check) check_is_bv_value(Solver::SPECIAL_VALUE_BV_ONES, cbzla_res);
      }
      else if (value == SPECIAL_VALUE_BV_MIN_SIGNED)
      {
        cbzla_res = bitwuzla_mk_bv_min_signed(d_solver, cbzla_sort);
        if (check)
          check_is_bv_value(Solver::SPECIAL_VALUE_BV_MIN_SIGNED, cbzla_res);
      }
      else
      {
        assert(value == SPECIAL_VALUE_BV_MAX_SIGNED);
        cbzla_res = bitwuzla_mk_bv_max_signed(d_solver, cbzla_sort);
        if (check)
          check_is_bv_value(Solver::SPECIAL_VALUE_BV_MAX_SIGNED, cbzla_res);
      }
      break;

    case SORT_FP:
    {
      if (value == SPECIAL_VALUE_FP_POS_INF)
      {
        cbzla_res = bitwuzla_mk_fp_pos_inf(d_solver, cbzla_sort);
      }
      else if (value == SPECIAL_VALUE_FP_NEG_INF)
      {
        cbzla_res = bitwuzla_mk_fp_neg_inf(d_solver, cbzla_sort);
      }
      else if (value == SPECIAL_VALUE_FP_POS_ZERO)
      {
        cbzla_res = bitwuzla_mk_fp_pos_zero(d_solver, cbzla_sort);
      }
      else if (value == SPECIAL_VALUE_FP_NEG_ZERO)
      {
        cbzla_res = bitwuzla_mk_fp_neg_zero(d_solver, cbzla_sort);
      }
      else
      {
        assert(value == SPECIAL_VALUE_FP_NAN);
        cbzla_res = bitwuzla_mk_fp_nan(d_solver, cbzla_sort);
      }
    }
    break;

    case SORT_RM:
      if (value == SPECIAL_VALUE_RM_RNA)
      {
        cbzla_res = bitwuzla_mk_rm_value(d_solver, BITWUZLA_RM_RNA);
      }
      else if (value == SPECIAL_VALUE_RM_RNE)
      {
        cbzla_res = bitwuzla_mk_rm_value(d_solver, BITWUZLA_RM_RNE);
      }
      else if (value == SPECIAL_VALUE_RM_RTN)
      {
        cbzla_res = bitwuzla_mk_rm_value(d_solver, BITWUZLA_RM_RTN);
      }
      else if (value == SPECIAL_VALUE_RM_RTP)
      {
        cbzla_res = bitwuzla_mk_rm_value(d_solver, BITWUZLA_RM_RTP);
      }
      else
      {
        assert(value == SPECIAL_VALUE_RM_RTZ);
        cbzla_res = bitwuzla_mk_rm_value(d_solver, BITWUZLA_RM_RTZ);
      }
      break;

    default: assert(false);
  }

  assert(cbzla_res);
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(cbzla_res));
  assert(res);
  return res;
}

Term
CBzlaSolver::mk_term(const OpKind& kind,
                    std::vector<Term>& args,
                    std::vector<uint32_t>& params)
{
  SMTMBT_CHECK_CONFIG(d_op_kinds.find(kind) != d_op_kinds.end())
      << "CBitwuzla: operator kind '" << kind << "' not configured";

  BitwuzlaTerm* cbzla_res = nullptr;
  size_t n_args           = args.size();
  size_t n_params         = params.size();
  BitwuzlaKind cbzla_kind = d_op_kinds.at(kind);
  std::vector<BitwuzlaTerm*> vars;
  std::vector<BitwuzlaTerm*> cbzla_args = terms_to_bzla_terms(args);

  if (n_params)
  {
    cbzla_res = bitwuzla_mk_term_indexed(d_solver,
                                         cbzla_kind,
                                         n_args,
                                         cbzla_args.data(),
                                         n_params,
                                         params.data());
  }
  else
  {
    cbzla_res =
        bitwuzla_mk_term(d_solver, cbzla_kind, n_args, cbzla_args.data());
  }
  assert(cbzla_res);
  std::shared_ptr<CBzlaTerm> res(new CBzlaTerm(cbzla_res));
  assert(res);
  return res;
}

Sort
CBzlaSolver::get_sort(Term term, SortKind sort_kind) const
{
  (void) sort_kind;
  return std::shared_ptr<CBzlaSort>(
      new CBzlaSort(d_solver, bitwuzla_term_get_sort(get_bzla_term(term))));
}

void
CBzlaSolver::assert_formula(const Term& t)
{
  bitwuzla_assert(d_solver, get_bzla_term(t));
}

Solver::Result
CBzlaSolver::check_sat()
{
  BitwuzlaResult res = bitwuzla_check_sat(d_solver);
  if (res == BITWUZLA_SAT) return Result::SAT;
  if (res == BITWUZLA_UNSAT) return Result::UNSAT;
  assert(res == BITWUZLA_UNKNOWN);
  return Result::UNKNOWN;
}

Solver::Result
CBzlaSolver::check_sat_assuming(std::vector<Term>& assumptions)
{
  int32_t res;
  for (const Term& t : assumptions)
  {
    bitwuzla_assume(d_solver, get_bzla_term(t));
  }
  res = bitwuzla_check_sat(d_solver);
  if (res == BITWUZLA_SAT) return Result::SAT;
  if (res == BITWUZLA_UNSAT) return Result::UNSAT;
  assert(res == BITWUZLA_UNKNOWN);
  return Result::UNKNOWN;
}

std::vector<Term>
CBzlaSolver::get_unsat_assumptions()
{
  size_t n_assumptions;
  std::vector<Term> res;
  BitwuzlaTerm** cbzla_res =
      bitwuzla_get_unsat_assumptions(d_solver, &n_assumptions);
  for (uint32_t i = 0; i < n_assumptions; ++i)
  {
    res.push_back(std::shared_ptr<CBzlaTerm>(
        new CBzlaTerm((BitwuzlaTerm*) cbzla_res[i])));
  }
  return res;
}

std::vector<Term>
CBzlaSolver::get_value(std::vector<Term>& terms)
{
  std::vector<Term> res;
  std::vector<BitwuzlaTerm*> cbzla_res;
  std::vector<BitwuzlaTerm*> bzla_terms = terms_to_bzla_terms(terms);

  for (BitwuzlaTerm* t : bzla_terms)
  {
    cbzla_res.push_back(bitwuzla_get_value(d_solver, t));
  }
  return cbzla_terms_to_terms(cbzla_res);
}

void
CBzlaSolver::push(uint32_t n_levels)
{
  bitwuzla_push(d_solver, n_levels);
}

void
CBzlaSolver::pop(uint32_t n_levels)
{
  bitwuzla_pop(d_solver, n_levels);
}

void
CBzlaSolver::print_model()
{
  const char* fmt = d_rng.flip_coin() ? "btor" : "smt2";
  bitwuzla_print_model(d_solver, (char*) fmt, stdout);
}

void
CBzlaSolver::reset_assertions()
{
  /* CBitwuzla does not support this yet */
}

/* -------------------------------------------------------------------------- */

bool
CBzlaSolver::check_unsat_assumption(const Term& t) const
{
  return bitwuzla_is_unsat_assumption(d_solver, get_bzla_term(t));
}

/* -------------------------------------------------------------------------- */

BitwuzlaSort*
CBzlaSolver::get_bzla_sort(Sort sort) const
{
  CBzlaSort* cbzla_sort = dynamic_cast<CBzlaSort*>(sort.get());
  assert(cbzla_sort);
  return cbzla_sort->d_sort;
}

BitwuzlaTerm*
CBzlaSolver::get_bzla_term(Term term) const
{
  CBzlaTerm* bzla_term = dynamic_cast<CBzlaTerm*>(term.get());
  assert(bzla_term);
  return bzla_term->d_term;
}

void
CBzlaSolver::set_opt(const std::string& opt, const std::string& value)
{
  if (opt == "produce-unsat-assumptions")
  {
    /* always enabled in CBitwuzla, can not be configured via set_opt */
    return;
  }

  // TODO reenable after option fuzzing for cbitwuzla is configured
  //assert(d_option_name_to_enum.find(opt) != d_option_name_to_enum.end());

  /* CBitwuzla options are all integer values */
  uint32_t val = 0;
  BitwuzlaOption cbzla_opt;

  value == "true" ? 1 : std::stoul(value);
  // TODO support all options
  if (opt == "produce-models")
  {
    cbzla_opt = BITWUZLA_OPT_PRODUCE_MODELS;
  }
  else if (opt == "incremental")
  {
    cbzla_opt = BITWUZLA_OPT_INCREMENTAL;
  }
  bitwuzla_set_option(d_solver, cbzla_opt, val);
  assert(val == bitwuzla_get_option(d_solver, cbzla_opt));
}

std::string
CBzlaSolver::get_option_name_incremental() const
{
  return "incremental";
}

std::string
CBzlaSolver::get_option_name_model_gen() const
{
  return "produce-models";
}

std::string
CBzlaSolver::get_option_name_unsat_assumptions() const
{
  /* always enabled in CBitwuzla, can not be configured via set_opt */
  return "produce-unsat-assumptions";
}

bool
CBzlaSolver::option_incremental_enabled() const
{
  return bitwuzla_get_option(d_solver, BITWUZLA_OPT_INCREMENTAL) > 0;
}

bool
CBzlaSolver::option_model_gen_enabled() const
{
  return bitwuzla_get_option(d_solver, BITWUZLA_OPT_PRODUCE_MODELS) > 0;
}

bool
CBzlaSolver::option_unsat_assumptions_enabled() const
{
  /* always enabled in CBitwuzla, can not be configured via set_opt */
  return true;
}

/* -------------------------------------------------------------------------- */

void
CBzlaSolver::init_op_kinds()
{
  d_op_kinds = {
      /* Special Cases */
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
      {Op::BV_MULT, BITWUZLA_KIND_BV_MUL},
      {Op::BV_ADD, BITWUZLA_KIND_BV_ADD},
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
      {Op::BV_LSHR, BITWUZLA_KIND_BV_SHR},
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
      {Op::FP_ABS, BITWUZLA_KIND_FP_ABS},
      {Op::FP_ADD, BITWUZLA_KIND_FP_ADD},
      {Op::FP_DIV, BITWUZLA_KIND_FP_DIV},
      {Op::FP_EQ, BITWUZLA_KIND_FP_EQ},
      {Op::FP_FMA, BITWUZLA_KIND_FP_FMA},
      {Op::FP_FP, BITWUZLA_KIND_FP_FP},
      {Op::FP_IS_NORMAL, BITWUZLA_KIND_FP_IS_NORMAL},
      {Op::FP_IS_SUBNORMAL, BITWUZLA_KIND_FP_IS_SUBNORMAL},
      {Op::FP_IS_INF, BITWUZLA_KIND_FP_IS_INF},
      {Op::FP_IS_NAN, BITWUZLA_KIND_FP_IS_NAN},
      {Op::FP_IS_NEG, BITWUZLA_KIND_FP_IS_NEG},
      {Op::FP_IS_POS, BITWUZLA_KIND_FP_IS_POS},
      {Op::FP_IS_ZERO, BITWUZLA_KIND_FP_IS_ZERO},
      {Op::FP_LT, BITWUZLA_KIND_FP_LT},
      {Op::FP_LEQ, BITWUZLA_KIND_FP_LEQ},
      {Op::FP_GT, BITWUZLA_KIND_FP_GT},
      {Op::FP_GEQ, BITWUZLA_KIND_FP_GEQ},
      {Op::FP_MAX, BITWUZLA_KIND_FP_MAX},
      {Op::FP_MIN, BITWUZLA_KIND_FP_MIN},
      {Op::FP_MUL, BITWUZLA_KIND_FP_MUL},
      {Op::FP_NEG, BITWUZLA_KIND_FP_NEG},
      {Op::FP_REM, BITWUZLA_KIND_FP_REM},
      {Op::FP_RTI, BITWUZLA_KIND_FP_RTI},
      {Op::FP_SQRT, BITWUZLA_KIND_FP_SQRT},
      {Op::FP_SUB, BITWUZLA_KIND_FP_SUB},
      {Op::FP_TO_FP_FROM_BV, BITWUZLA_KIND_FP_TO_FP_FROM_BV},
      {Op::FP_TO_FP_FROM_INT_BV, BITWUZLA_KIND_FP_TO_FP_FROM_INT},
      {Op::FP_TO_FP_FROM_FP, BITWUZLA_KIND_FP_TO_FP_FROM_FP},
      {Op::FP_TO_FP_FROM_UINT_BV, BITWUZLA_KIND_FP_TO_FP_FROM_UINT},
      {Op::FP_TO_SBV, BITWUZLA_KIND_FP_TO_SBV},
      {Op::FP_TO_UBV, BITWUZLA_KIND_FP_TO_UBV},

      /* Quantifiers */
      {Op::FORALL, BITWUZLA_KIND_FORALL},
      {Op::EXISTS, BITWUZLA_KIND_EXISTS},

      /* UF */
      {Op::UF_APPLY, BITWUZLA_KIND_APPLY},

      /* Solver-specific operators */
      {OP_BV_DEC, BITWUZLA_KIND_BV_DEC},
      {OP_BV_INC, BITWUZLA_KIND_BV_INC},
      {OP_BV_ROL, BITWUZLA_KIND_BV_ROL},
      {OP_BV_ROR, BITWUZLA_KIND_BV_ROR},
      {OP_BV_REDAND, BITWUZLA_KIND_BV_REDAND},
      {OP_BV_REDOR, BITWUZLA_KIND_BV_REDOR},
      {OP_BV_REDXOR, BITWUZLA_KIND_BV_REDXOR},
      {OP_BV_UADDO, BITWUZLA_KIND_BV_UADD_OVERFLOW},
      {OP_BV_SADDO, BITWUZLA_KIND_BV_SADD_OVERFLOW},
      {OP_BV_UMULO, BITWUZLA_KIND_BV_UMUL_OVERFLOW},
      {OP_BV_SMULO, BITWUZLA_KIND_BV_SMUL_OVERFLOW},
      {OP_BV_USUBO, BITWUZLA_KIND_BV_USUB_OVERFLOW},
      {OP_BV_SSUBO, BITWUZLA_KIND_BV_SSUB_OVERFLOW},
      {OP_BV_SDIVO, BITWUZLA_KIND_BV_SDIV_OVERFLOW},
  };
}

std::vector<Term>
CBzlaSolver::cbzla_terms_to_terms(std::vector<BitwuzlaTerm*>& terms) const
{
  std::vector<Term> res;
  for (BitwuzlaTerm* t : terms)
  {
    res.push_back(std::shared_ptr<CBzlaTerm>(new CBzlaTerm(t)));
  }
  return res;
}

std::vector<BitwuzlaTerm*>
CBzlaSolver::terms_to_bzla_terms(std::vector<Term>& terms) const
{
  std::vector<BitwuzlaTerm*> res;
  for (Term& t : terms)
  {
    res.push_back(get_bzla_term(t));
  }
  return res;
}

CBzlaSolver::CbzlaTermFunBoolUnary
CBzlaSolver::pick_fun_bool_unary(CbzlaTermFunBoolUnaryVector& funs) const
{
  return d_rng
      .pick_from_set<CbzlaTermFunBoolUnaryVector, CbzlaTermFunBoolUnary>(funs);
}

CBzlaSolver::CbzlaTermFunBoolUnary
CBzlaSolver::pick_fun_is_bv_const() const
{
  CbzlaTermFunBoolUnaryVector funs = {bitwuzla_term_is_bv_value_zero,
                                      bitwuzla_term_is_bv_value_one,
                                      bitwuzla_term_is_bv_value_ones,
                                      bitwuzla_term_is_bv_value_max_signed,
                                      bitwuzla_term_is_bv_value_min_signed};
  return pick_fun_bool_unary(funs);
}

void
CBzlaSolver::check_is_bv_value(const Solver::SpecialValueKind& kind,
                               BitwuzlaTerm* node) const
{
  uint32_t bw              = bitwuzla_term_bv_get_size(node);
  RNGenerator::Choice pick = d_rng.pick_one_of_three();

  if (pick == RNGenerator::Choice::FIRST)
  {
    CbzlaTermFunBoolUnaryVector is_funs;
    CbzlaTermFunBoolUnaryVector is_not_funs;
    if (kind == Solver::SPECIAL_VALUE_BV_ONE)
    {
      is_funs.push_back(bitwuzla_term_is_bv_value_one);
      if (bw > 1)
      {
        is_not_funs.push_back(bitwuzla_term_is_bv_value_zero);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_ones);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_min_signed);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_max_signed);
      }
      else
      {
        is_funs.push_back(bitwuzla_term_is_bv_value_ones);
        is_funs.push_back(bitwuzla_term_is_bv_value_min_signed);

        is_not_funs.push_back(bitwuzla_term_is_bv_value_zero);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_max_signed);
      }
    }
    else if (kind == Solver::SPECIAL_VALUE_BV_ONES)
    {
      is_funs.push_back(bitwuzla_term_is_bv_value_ones);
      if (bw > 1)
      {
        is_not_funs.push_back(bitwuzla_term_is_bv_value_one);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_zero);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_min_signed);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_max_signed);
      }
      else
      {
        is_funs.push_back(bitwuzla_term_is_bv_value_one);
        is_funs.push_back(bitwuzla_term_is_bv_value_min_signed);

        is_not_funs.push_back(bitwuzla_term_is_bv_value_zero);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_max_signed);
      }
    }
    else if (kind == Solver::SPECIAL_VALUE_BV_ZERO)
    {
      is_funs.push_back(bitwuzla_term_is_bv_value_zero);
      if (bw > 1)
      {
        is_not_funs.push_back(bitwuzla_term_is_bv_value_one);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_ones);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_min_signed);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_max_signed);
      }
      else
      {
        is_funs.push_back(bitwuzla_term_is_bv_value_max_signed);

        is_not_funs.push_back(bitwuzla_term_is_bv_value_one);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_ones);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_min_signed);
      }
    }
    else if (kind == Solver::SPECIAL_VALUE_BV_MIN_SIGNED)
    {
      is_funs.push_back(bitwuzla_term_is_bv_value_min_signed);
      if (bw > 1)
      {
        is_not_funs.push_back(bitwuzla_term_is_bv_value_zero);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_one);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_ones);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_max_signed);
      }
      else
      {
        is_funs.push_back(bitwuzla_term_is_bv_value_one);
        is_funs.push_back(bitwuzla_term_is_bv_value_ones);

        is_not_funs.push_back(bitwuzla_term_is_bv_value_zero);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_max_signed);
      }
    }
    else
    {
      assert(kind == Solver::SPECIAL_VALUE_BV_MAX_SIGNED);
      is_funs.push_back(bitwuzla_term_is_bv_value_max_signed);
      if (bw > 1)
      {
        is_not_funs.push_back(bitwuzla_term_is_bv_value_zero);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_one);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_ones);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_min_signed);
      }
      else
      {
        is_funs.push_back(bitwuzla_term_is_bv_value_zero);

        is_not_funs.push_back(bitwuzla_term_is_bv_value_one);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_ones);
        is_not_funs.push_back(bitwuzla_term_is_bv_value_max_signed);
      }
    }
    if (d_rng.flip_coin())
    {
      assert(pick_fun_bool_unary(is_funs)(node));
    }
    else
    {
      assert(!pick_fun_bool_unary(is_not_funs)(node));
    }
  }
  else if (pick == RNGenerator::Choice::SECOND)
  {
    assert(bitwuzla_term_is_bv_value(node));
  }
  else
  {
    assert(pick == RNGenerator::Choice::THIRD);
    assert(!bitwuzla_term_is_const(node));
  }
}

/* -------------------------------------------------------------------------- */
/* Solver-specific operators, SolverManager configuration.                    */
/* -------------------------------------------------------------------------- */

const OpKind CBzlaSolver::OP_BV_DEC    = "cbzla-OP_BV_DEC";
const OpKind CBzlaSolver::OP_BV_INC    = "cbzla-OP_BV_INC";
const OpKind CBzlaSolver::OP_BV_REDAND = "cbzla-OP_BV_REDAND";
const OpKind CBzlaSolver::OP_BV_REDOR  = "cbzla-OP_BV_REDOR";
const OpKind CBzlaSolver::OP_BV_REDXOR = "cbzla-OP_BV_REDXOR";
const OpKind CBzlaSolver::OP_BV_ROL    = "cbzla-OP_BV_ROL";
const OpKind CBzlaSolver::OP_BV_ROR    = "cbzla-OP_BV_ROR";
const OpKind CBzlaSolver::OP_BV_SADDO  = "cbzla-OP_BV_SADDO";
const OpKind CBzlaSolver::OP_BV_SDIVO  = "cbzla-OP_BV_SDIVO";
const OpKind CBzlaSolver::OP_BV_SMULO  = "cbzla-OP_BV_SMULO";
const OpKind CBzlaSolver::OP_BV_SSUBO  = "cbzla-OP_BV_SSUBO";
const OpKind CBzlaSolver::OP_BV_UADDO  = "cbzla-OP_BV_UADDO";
const OpKind CBzlaSolver::OP_BV_UMULO  = "cbzla-OP_BV_UMULO";
const OpKind CBzlaSolver::OP_BV_USUBO  = "cbzla-OP_BV_USUBO";

void
CBzlaSolver::configure_smgr(SolverManager* smgr) const
{
  smgr->add_op_kind(OP_BV_DEC, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_BV_INC, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  smgr->add_op_kind(OP_BV_REDAND, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_BV_REDOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_BV_REDXOR, 1, 0, SORT_BV, {SORT_BV}, THEORY_BV);

  smgr->add_op_kind(OP_BV_UADDO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_BV_UMULO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_BV_USUBO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_BV_SADDO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_BV_SDIVO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_BV_SMULO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
  smgr->add_op_kind(OP_BV_SSUBO, 2, 0, SORT_BV, {SORT_BV}, THEORY_BV);
}

/* -------------------------------------------------------------------------- */
/* Solver-specific actions and states, FSM configuration.                     */
/* -------------------------------------------------------------------------- */

/* solver-specific actions */
const ActionKind CBzlaSolver::ACTION_IS_UNSAT_ASSUMPTION =
    "cbzla-is-unsat-assumption";
const ActionKind CBzlaSolver::ACTION_FIXATE_ASSUMPTIONS =
    "cbzla-fixate-assumptions";
const ActionKind CBzlaSolver::ACTION_RESET_ASSUMPTIONS =
    "cbzla-reset-assumptions";
const ActionKind CBzlaSolver::ACTION_SIMPLIFY        = "cbzla-simplify";
const ActionKind CBzlaSolver::ACTION_TERM_SET_SYMBOL = "cbzla-term-set-symbol";
/* solver-specific states */
const StateKind CBzlaSolver::STATE_FIX_RESET_ASSUMPTIONS =
    "cbzla-fix-reset-assumptions";

class CBzlaActionIsUnsatAssumption : public Action
{
 public:
  CBzlaActionIsUnsatAssumption(SolverManager& smgr)
      : Action(smgr, CBzlaSolver::ACTION_IS_UNSAT_ASSUMPTION, false)
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
    CBzlaSolver& cbzla_solver = static_cast<CBzlaSolver&>(d_smgr.get_solver());
    (void) bitwuzla_is_unsat_assumption(cbzla_solver.get_solver(),
                                        cbzla_solver.get_bzla_term(term));
  }
};

class CBzlaActionFixateAssumptions : public Action
{
 public:
  CBzlaActionFixateAssumptions(SolverManager& smgr)
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
    bitwuzla_fixate_assumptions(
        static_cast<CBzlaSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class CBzlaActionResetAssumptions : public Action
{
 public:
  CBzlaActionResetAssumptions(SolverManager& smgr)
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
    bitwuzla_reset_assumptions(
        static_cast<CBzlaSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class CBzlaActionSimplify : public Action
{
 public:
  CBzlaActionSimplify(SolverManager& smgr)
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
    bitwuzla_simplify(
        static_cast<CBzlaSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class CBzlaActionTermSetSymbol : public Action
{
 public:
  CBzlaActionTermSetSymbol(SolverManager& smgr)
      : Action(smgr, CBzlaSolver::ACTION_TERM_SET_SYMBOL, false)
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
    CBzlaSolver& cbzla_solver = static_cast<CBzlaSolver&>(d_smgr.get_solver());
    (void) bitwuzla_term_set_symbol(cbzla_solver.get_bzla_term(term),
                                    symbol.c_str());
  }
};

/* -------------------------------------------------------------------------- */

void
CBzlaSolver::configure_fsm(FSM* fsm) const
{
  State* s_assert = fsm->get_state(State::ASSERT);
  State* s_fix_reset_assumptions = fsm->new_state(STATE_FIX_RESET_ASSUMPTIONS);

  auto t_default = fsm->new_action<TransitionDefault>();

  // bitwuzla_is_unsat_assumption
  auto a_failed = fsm->new_action<CBzlaActionIsUnsatAssumption>();
  fsm->add_action_to_all_states(a_failed, 100);

  // bitwuzla_fixate_assumptions
  // bitwuzla_reset_assumptions
  auto a_fix_assumptions   = fsm->new_action<CBzlaActionFixateAssumptions>();
  auto a_reset_assumptions = fsm->new_action<CBzlaActionResetAssumptions>();
  s_fix_reset_assumptions->add_action(a_fix_assumptions, 5);
  s_fix_reset_assumptions->add_action(a_reset_assumptions, 5);
  s_fix_reset_assumptions->add_action(t_default, 1, s_assert);
  fsm->add_action_to_all_states_next(
      t_default, 2, s_fix_reset_assumptions, {State::OPT});

  // bitwuzla_simplify
  auto a_simplify = fsm->new_action<CBzlaActionSimplify>();
  fsm->add_action_to_all_states(a_simplify, 100);

  // bitwuzla_term_set_symbol
  auto a_set_symbol = fsm->new_action<CBzlaActionTermSetSymbol>();
  fsm->add_action_to_all_states(a_set_symbol, 100);
}

}  // namespace cbzla
}  // namespace smtmbt

#endif
