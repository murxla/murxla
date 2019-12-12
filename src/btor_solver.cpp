#include "btor_solver.hpp"

#include <cassert>

#include "fsm.hpp"
#include "theory.hpp"
#include "util.hpp"

namespace smtmbt {
namespace btor {

/* -------------------------------------------------------------------------- */

namespace {

bool
is_power_of_2(uint32_t x)
{
  assert(x > 0);
  return (x & (x - 1)) == 0;
}

}  // namespace

/* -------------------------------------------------------------------------- */
/* BtorSort                                                                   */
/* -------------------------------------------------------------------------- */

BtorSort::BtorSort(Btor* btor, BoolectorSort sort)
    : d_solver(btor), d_sort(boolector_copy_sort(btor, sort))
{
}

BtorSort::~BtorSort() { boolector_release_sort(d_solver, d_sort); }

size_t
BtorSort::hash() const
{
  return std::hash<BoolectorSort>{}(d_sort);
}

bool
BtorSort::equals(const Sort& other) const
{
  BtorSort* btor_sort = dynamic_cast<BtorSort*>(other.get());
  if (btor_sort)
  {
    return d_sort == btor_sort->d_sort;
  }
  return false;
}

bool
BtorSort::is_bool() const
{
  BoolectorSort s = boolector_bool_sort(d_solver);
  bool res        = s == d_sort;
  boolector_release_sort(d_solver, s);
  return res && d_kind == SORT_BOOL;
}

bool
BtorSort::is_bv() const
{
  return boolector_is_bitvec_sort(d_solver, d_sort);
}

uint32_t
BtorSort::get_bv_size() const
{
  return boolector_bitvec_sort_get_width(d_solver, d_sort);
}

/* -------------------------------------------------------------------------- */
/* BtorTerm                                                                   */
/* -------------------------------------------------------------------------- */

BtorTerm::BtorTerm(Btor* btor, BoolectorNode* term)
    : d_solver(btor), d_term(boolector_copy(btor, term))
{
}

BtorTerm::~BtorTerm() { boolector_release(d_solver, d_term); }

size_t
BtorTerm::hash() const
{
  return boolector_get_node_id(d_solver, d_term);
}

bool
BtorTerm::equals(const Term& other) const
{
  BtorTerm* btor_term = dynamic_cast<BtorTerm*>(other.get());
  if (btor_term)
  {
    return boolector_get_node_id(d_solver, d_term)
           == boolector_get_node_id(btor_term->d_solver, btor_term->d_term);
  }
  return false;
}

/* -------------------------------------------------------------------------- */
/* BtorSolver                                                                 */
/* -------------------------------------------------------------------------- */

void
BtorSolver::new_solver()
{
  assert(d_solver == nullptr);
  d_solver = boolector_new();

  /* Initialize Boolector options */
  if (d_option_name_to_enum.empty())
  {
    for (BtorOption opt = boolector_first_opt(d_solver);
         boolector_has_opt(d_solver, opt);
         opt = boolector_next_opt(d_solver, opt))
    {
      std::string name(boolector_get_opt_lng(d_solver, opt));
      d_option_name_to_enum[name] = opt;
    }
  }
}

void
BtorSolver::delete_solver()
{
  assert(d_solver != nullptr);
  boolector_delete(d_solver);
  d_solver = nullptr;
}

Btor*
BtorSolver::get_solver()
{
  return d_solver;
}

bool
BtorSolver::is_initialized() const
{
  return d_solver != nullptr;
}

TheoryIdVector
BtorSolver::get_supported_theories() const
{
  return {THEORY_BV, THEORY_BOOL};
}

OpKindSet
BtorSolver::get_unsupported_op_kinds() const
{
  return {};
}

Sort
BtorSolver::mk_sort(SortKind kind) const
{
  assert(kind == SORT_BOOL);
  BoolectorSort btor_res = boolector_bool_sort(d_solver);
  assert(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  boolector_release_sort(d_solver, btor_res);
  assert(res);
  return res;
}

Sort
BtorSolver::mk_sort(SortKind kind, uint32_t size) const
{
  assert(kind == SORT_BV);
  BoolectorSort btor_res = boolector_bitvec_sort(d_solver, size);
  assert(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  boolector_release_sort(d_solver, btor_res);
  assert(res);
  return res;
}

Term
BtorSolver::mk_const(Sort sort, const std::string name) const
{
  BoolectorNode* btor_res =
      boolector_var(d_solver, get_btor_sort(sort), name.c_str());
  assert(btor_res);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_value(Sort sort, bool value) const
{
  assert(sort->is_bool());
  BoolectorNode* btor_res =
      value ? boolector_true(d_solver) : boolector_false(d_solver);
  assert(btor_res);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_value(Sort sort, uint64_t value) const
{
  assert(sort->is_bv());

  BoolectorNode* btor_res = 0;
  BoolectorSort btor_sort = get_btor_sort(sort);
  uint32_t bw             = sort->get_bv_size();
  bool use_special_fun    = d_rng.flip_coin();

  if (!use_special_fun && value == 0)
  {
    btor_res = boolector_zero(d_solver, btor_sort);
  }
  else if (use_special_fun && value == 1)
  {
    btor_res = boolector_one(d_solver, btor_sort);
  }
  else if (use_special_fun && is_bv_special_value_ones_uint64(bw, value))
  {
    btor_res = boolector_ones(d_solver, btor_sort);
  }
  else if (use_special_fun && is_bv_special_value_min_signed_uint64(bw, value))
  {
    btor_res = boolector_min_signed(d_solver, btor_sort);
  }
  else if (use_special_fun && is_bv_special_value_max_signed_uint64(bw, value))
  {
    btor_res = boolector_max_signed(d_solver, btor_sort);
  }
  else
  {
    if (d_rng.flip_coin())
    {
      btor_res = boolector_unsigned_int(d_solver, (uint32_t) value, btor_sort);
    }
    else
    {
      btor_res = boolector_int(d_solver, (int32_t) value, btor_sort);
    }
  }
  assert(btor_res);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_value(Sort sort, std::string value, Base base) const
{
  assert(sort->is_bv());

  BoolectorNode* btor_res;
  BoolectorSort btor_sort = get_btor_sort(sort);

  switch (base)
  {
    case HEX:
      btor_res = boolector_consth(d_solver, btor_sort, value.c_str());
      break;
    case DEC:
      btor_res = boolector_constd(d_solver, btor_sort, value.c_str());
      break;
    default:
      assert(base == BIN);
      btor_res = boolector_const(d_solver, value.c_str());
  }
  assert(btor_res);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_term(const OpKind& kind,
                    std::vector<Term>& args,
                    std::vector<uint32_t>& params) const
{
  BoolectorNode* btor_res = nullptr;
  size_t n_args           = args.size();
  size_t n_params         = params.size();

  // BoolectorNode *boolector_read (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index);
  // BoolectorNode *boolector_write (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index, BoolectorNode *n_value);
  // BoolectorNode *boolector_apply (Btor *btor, BoolectorNode **arg_nodes, uint32_t argc, BoolectorNode *n_fun);

  switch (kind)
  {
    case OP_DISTINCT:
      assert(n_args > 1);
      btor_res = mk_term_pairwise(args, boolector_ne);
      break;
    case OP_EQUAL:
    case OP_BV_COMP:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_eq);
      break;
    case OP_IFF:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_iff);
      break;
    case OP_ITE:
      assert(n_args == 3);
      btor_res = boolector_cond(d_solver,
                                get_btor_term(args[0]),
                                get_btor_term(args[1]),
                                get_btor_term(args[2]));
      break;
    case OP_IMPLIES:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_implies);
      break;

    case OP_BV_EXTRACT:
      assert(n_args == 1);
      assert(n_params == 2);
      btor_res = boolector_slice(
          d_solver, get_btor_term(args[0]), params[0], params[1]);
      break;
    case OP_BV_REPEAT:
      assert(n_args == 1);
      assert(n_params == 1);
      btor_res = boolector_repeat(d_solver, get_btor_term(args[0]), params[0]);
      break;

    case OP_BV_ROTATE_LEFT:
    {
      assert(n_args == 1);
      assert(n_params == 1);

      BoolectorNode* arg = get_btor_term(args[0]);
      BoolectorSort s    = boolector_get_sort(d_solver, arg);
      uint32_t bw        = boolector_bitvec_sort_get_width(d_solver, s);

      /* use boolector_roli vs boolector_rol with 50% probability */
      if (d_rng.flip_coin())
      {
        btor_res = boolector_roli(d_solver, arg, params[0]);
      }
      else
      {
        BoolectorNode* tmp;
        /* use same bit-width vs log2 bit-width (if possible) with 50% prob */
        if (is_power_of_2(bw) && d_rng.flip_coin())
        {
          /* arg has bw that is power of 2, nbits argument with log2 bw */
          uint32_t bw2     = static_cast<uint32_t>(log2(bw));
          BoolectorSort s2 = boolector_bitvec_sort(d_solver, bw2);
          uint32_t nbits   = params[0] % bw;
          tmp              = boolector_unsigned_int(d_solver, nbits, s2);
          boolector_release_sort(d_solver, s2);
        }
        else
        {
          /* arg and nbits argument with same bw */
          tmp = boolector_unsigned_int(d_solver, params[0], s);
        }
        btor_res = boolector_rol(d_solver, arg, tmp);
        boolector_release(d_solver, tmp);
      }
      break;
    }

    case OP_BV_ROTATE_RIGHT:
    {
      assert(n_args == 1);
      assert(n_params == 1);
      BoolectorNode* arg = get_btor_term(args[0]);
      BoolectorSort s    = boolector_get_sort(d_solver, arg);
      uint32_t bw        = boolector_bitvec_sort_get_width(d_solver, s);

      /* use boolector_rori vs boolector_ror with 50% probability */
      if (d_rng.flip_coin())
      {
        btor_res = boolector_rori(d_solver, arg, params[0]);
      }
      else
      {
        BoolectorNode* tmp;
        /* use same bit-width vs log2 bit-width (if possible) with 50% prob */
        if (is_power_of_2(bw) && d_rng.flip_coin())
        {
          /* arg has bw that is power of 2, nbits argument with log2 bw */
          uint32_t bw2     = static_cast<uint32_t>(log2(bw));
          BoolectorSort s2 = boolector_bitvec_sort(d_solver, bw2);
          uint32_t nbits   = params[0] % bw;
          tmp              = boolector_unsigned_int(d_solver, nbits, s2);
          boolector_release_sort(d_solver, s2);
        }
        else
        {
          /* arg and nbits argument with same bw */
          tmp = boolector_unsigned_int(d_solver, params[0], s);
        }
        btor_res = boolector_ror(d_solver, arg, tmp);
        boolector_release(d_solver, tmp);
      }
      break;
    }

    case OP_BV_SIGN_EXTEND:
      assert(n_args == 1);
      assert(n_params == 1);
      btor_res = boolector_sext(d_solver, get_btor_term(args[0]), params[0]);
      break;
    case OP_BV_ZERO_EXTEND:
      assert(n_args == 1);
      assert(n_params == 1);
      btor_res = boolector_uext(d_solver, get_btor_term(args[0]), params[0]);
      break;
    case OP_BV_CONCAT:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_concat);
      break;
    case OP_AND:
    case OP_BV_AND:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_and);
      break;
    case OP_OR:
    case OP_BV_OR:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_or);
      break;
    case OP_XOR:
    case OP_BV_XOR:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_xor);
      break;
    case OP_BV_MULT:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_mul);
      break;
    case OP_BV_ADD:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_add);
      break;

    case OP_NOT:
    case OP_BV_NOT:
      assert(n_args == 1);
      btor_res = boolector_not(d_solver, get_btor_term(args[0]));
      break;
    case OP_BV_NEG:
      assert(n_args == 1);
      btor_res = boolector_neg(d_solver, get_btor_term(args[0]));
      break;
    case OP_BV_REDAND:
      assert(n_args == 1);
      btor_res = boolector_redand(d_solver, get_btor_term(args[0]));
      break;
    case OP_BV_REDOR:
      assert(n_args == 1);
      btor_res = boolector_redor(d_solver, get_btor_term(args[0]));
      break;
    case OP_BV_REDXOR:
      assert(n_args == 1);
      btor_res = boolector_redxor(d_solver, get_btor_term(args[0]));
      break;
    case OP_BV_INC:
      assert(n_args == 1);
      btor_res = boolector_inc(d_solver, get_btor_term(args[0]));
      break;
    case OP_BV_DEC:
      assert(n_args == 1);
      btor_res = boolector_dec(d_solver, get_btor_term(args[0]));
      break;

    case OP_BV_NAND:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_nand);
      break;
    case OP_BV_NOR:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_nor);
      break;
    case OP_BV_XNOR:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_xnor);
      break;
    case OP_BV_SUB:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sub);
      break;
    case OP_BV_UDIV:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_udiv);
      break;
    case OP_BV_UREM:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_urem);
      break;
    case OP_BV_SDIV:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sdiv);
      break;
    case OP_BV_SREM:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_srem);
      break;
    case OP_BV_SMOD:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_smod);
      break;
    case OP_BV_SHL:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sll);
      break;
    case OP_BV_LSHR:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_srl);
      break;
    case OP_BV_ASHR:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sra);
      break;
    case OP_BV_UADDO:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_uaddo);
      break;
    case OP_BV_UGT:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_ugt);
      break;
    case OP_BV_UGE:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_ugte);
      break;
    case OP_BV_ULT:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_ult);
      break;
    case OP_BV_ULE:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_ulte);
      break;
    case OP_BV_UMULO:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_umulo);
      break;
    case OP_BV_USUBO:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_usubo);
      break;
    case OP_BV_SADDO:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_saddo);
      break;
    case OP_BV_SDIVO:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sdivo);
      break;
    case OP_BV_SGT:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sgt);
      break;
    case OP_BV_SGE:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sgte);
      break;
    case OP_BV_SLT:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_slt);
      break;
    case OP_BV_SLE:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_slte);
      break;
    case OP_BV_SMULO:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_smulo);
      break;
    case OP_BV_SSUBO:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_ssubo);
      break;

    default: assert(false);
  }
  assert(btor_res);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  assert(res);
  boolector_release(d_solver, btor_res);
  return res;
}

// BoolectorNode *boolector_var (Btor *btor, BoolectorSort sort, const char *symbol); 
// BoolectorNode *boolector_array (Btor *btor, BoolectorSort sort, const char *symbol); 
// BoolectorNode *boolector_uf (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_forall (Btor *btor, BoolectorNode *params[], uint32_t paramc, BoolectorNode *body);
// BoolectorNode *boolector_exists (Btor *btor, BoolectorNode *param[], uint32_t paramc, BoolectorNode *body);
// BoolectorNode *boolector_fun (Btor *btor, BoolectorNode **param_nodes, uint32_t paramc, BoolectorNode *node);
// BoolectorNode *boolector_param (Btor *btor, BoolectorSort sort, const char *symbol);

Sort
BtorSolver::get_sort(Term term) const
{
  return std::shared_ptr<BtorSort>(new BtorSort(
      d_solver, boolector_get_sort(d_solver, get_btor_term(term))));
}

void
BtorSolver::assert_formula(const Term& t) const
{
  boolector_assert(d_solver, get_btor_term(t));
}

Solver::Result
BtorSolver::check_sat() const
{
  int32_t res = boolector_sat(d_solver);
  if (res == BOOLECTOR_SAT) return Result::SAT;
  if (res == BOOLECTOR_UNSAT) return Result::UNSAT;
  assert(res == BOOLECTOR_UNKNOWN);
  return Result::UNKNOWN;
}

/* -------------------------------------------------------------------------- */

BoolectorSort
BtorSolver::get_btor_sort(Sort sort) const
{
  BtorSort* btor_sort = dynamic_cast<BtorSort*>(sort.get());
  assert(btor_sort);
  return btor_sort->d_sort;
}

BoolectorNode*
BtorSolver::get_btor_term(Term term) const
{
  BtorTerm* btor_term = dynamic_cast<BtorTerm*>(term.get());
  assert(btor_term);
  return btor_term->d_term;
}

BoolectorNode*
BtorSolver::mk_term_left_assoc(std::vector<Term>& args,
                               BoolectorNode* (*fun)(Btor*,
                                                     BoolectorNode*,
                                                     BoolectorNode*) ) const
{
  assert(args.size() >= 2);
  BoolectorNode *res, *tmp;

  res = fun(d_solver, get_btor_term(args[0]), get_btor_term(args[1]));
  for (uint32_t i = 2, n_args = args.size(); i < n_args; ++i)
  {
    tmp = fun(d_solver, res, get_btor_term(args[i]));
    boolector_release(d_solver, res);
    res = tmp;
  }
  assert(res);
  return res;
}

BoolectorNode*
BtorSolver::mk_term_pairwise(std::vector<Term>& args,
                             BoolectorNode* (*fun)(Btor*,
                                                   BoolectorNode*,
                                                   BoolectorNode*) ) const
{
  assert(args.size() >= 2);
  BoolectorNode *res, *tmp, *old;

  res = 0;
  for (uint32_t i = 0, n_args = args.size(); i < n_args - 1; ++i)
  {
    for (uint32_t j = i + 1; j < n_args; ++j)
    {
      tmp = fun(d_solver, get_btor_term(args[i]), get_btor_term(args[j]));
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

void
BtorSolver::set_opt(const std::string& opt, const std::string& value) const
{
  assert(d_option_name_to_enum.find(opt) != d_option_name_to_enum.end());

  /* Boolector options are all integer values */
  BtorOption option = d_option_name_to_enum.at(opt);
  uint32_t val      = std::stoul(value);
  boolector_set_opt(d_solver, option, val);
}

/* -------------------------------------------------------------------------- */
/* Solver-specific actions, FSM configuration. */
/* -------------------------------------------------------------------------- */

class BtorActionReleaseAll : public Action
{
 public:
  BtorActionReleaseAll(SolverManager& smgr) : Action(smgr, "btor-release-all")
  {
  }

  bool run() override
  {
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
    SMTMBT_TRACE << get_id();
    d_smgr.clear();
    boolector_release_all(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionFixateAssumptions : public Action
{
 public:
  BtorActionFixateAssumptions(SolverManager& smgr)
      : Action(smgr, "btor-fixate-assumptions")
  {
  }

  bool run() override
  {
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
    SMTMBT_TRACE << get_id();
    d_smgr.clear();
    boolector_fixate_assumptions(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

class BtorActionResetAssumptions : public Action
{
 public:
  BtorActionResetAssumptions(SolverManager& smgr)
      : Action(smgr, "btor-reset-assumptions")
  {
  }

  bool run() override
  {
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
    SMTMBT_TRACE << get_id();
    d_smgr.clear();
    boolector_reset_assumptions(
        static_cast<BtorSolver&>(d_smgr.get_solver()).get_solver());
  }
};

void
BtorSolver::configure_fsm(FSM& fsm) const
{
  auto t_default = fsm.new_action<Transition>();

  // boolector_release_all
  auto a_release_all = fsm.new_action<BtorActionReleaseAll>();
  State* s_delete    = fsm.get_state("delete");
  s_delete->add_action(a_release_all, 1);

  // boolector_fixate_assumptions
  // boolector_reset_assumptions
  State* s_fix_reset_assumptions = fsm.new_state("btor-fix-reset-assumptions");
  auto a_fix_assumptions   = fsm.new_action<BtorActionFixateAssumptions>();
  auto a_reset_assumptions = fsm.new_action<BtorActionResetAssumptions>();
  s_fix_reset_assumptions->add_action(a_fix_assumptions, 10);
  s_fix_reset_assumptions->add_action(a_reset_assumptions, 10);
  State* s_assert = fsm.get_state("assert");
  s_assert->add_action(t_default, 1, s_fix_reset_assumptions);
  s_fix_reset_assumptions->add_action(t_default, 100, s_assert);
}

}  // namespace btor
}  // namespace smtmbt
