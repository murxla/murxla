#include "btor_solver.hpp"

#include <cassert>

#include "theory.hpp"

namespace smtmbt {
namespace btor {

/* -------------------------------------------------------------------------- */
/* BtorSort                                                                   */
/* -------------------------------------------------------------------------- */

BtorSort::BtorSort(Btor* btor, BoolectorSort sort, bool is_bool)
    : d_solver(btor),
      d_sort(boolector_copy_sort(btor, sort)),
      d_is_bool(is_bool)
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
    return d_sort == btor_sort->d_sort && d_is_bool == btor_sort->d_is_bool;
  }
  return false;
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
    : d_solver(btor), d_term(term)
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
}

void
BtorSolver::delete_solver()
{
  assert(d_solver != nullptr);
  boolector_delete(d_solver);
  d_solver = nullptr;
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

Sort
BtorSolver::mk_sort(SortKind kind) const
{
  assert(kind == SORT_BOOLEAN);
  BoolectorSort btor_res = boolector_bool_sort(d_solver);
  assert(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res, true));
  boolector_release_sort(d_solver, btor_res);
  return res;
}

Sort
BtorSolver::mk_sort(SortKind kind, uint32_t size) const
{
  assert(kind == SORT_BIT_VECTOR);
  BoolectorSort btor_res = boolector_bitvec_sort(d_solver, size);
  assert(btor_res);
  std::shared_ptr<BtorSort> res(new BtorSort(d_solver, btor_res));
  boolector_release_sort(d_solver, btor_res);
  return res;
}

Term
BtorSolver::mk_const(Sort sort, const std::string name) const
{
  BoolectorNode* btor_res =
      boolector_var(d_solver, get_sort(sort), name.c_str());
  assert(btor_res);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  std::cout << "const" << res << std::endl;
  return res;
}

Term
BtorSolver::mk_term(const OpKind& kind,
                    std::vector<Term>& args,
                    std::vector<uint32_t>& params) const
{
  // TODO TODO TODO indexed operators
  BoolectorNode* btor_res = nullptr;
  size_t n_args = args.size();
  size_t n_params         = params.size();

  // BoolectorNode *boolector_iff (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
  // BoolectorNode *boolector_uaddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
  // BoolectorNode *boolector_saddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
  // BoolectorNode *boolector_umulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
  // BoolectorNode *boolector_smulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

  // BoolectorNode *boolector_usubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
  // BoolectorNode *boolector_ssubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
  // BoolectorNode *boolector_sdivo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
  // BoolectorNode *boolector_read (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index);
  // BoolectorNode *boolector_write (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index, BoolectorNode *n_value);
  // BoolectorNode *boolector_inc (Btor *btor, BoolectorNode *node);
  // BoolectorNode *boolector_dec (Btor *btor, BoolectorNode *node);
  // BoolectorNode *boolector_redxor (Btor *btor, BoolectorNode *node);
  // BoolectorNode *boolector_apply (Btor *btor, BoolectorNode **arg_nodes, uint32_t argc, BoolectorNode *n_fun);

  switch (kind)
  {
    case DISTINCT:
      assert(n_args > 1);
      btor_res = mk_term_pairwise(args, boolector_ne);
      break;
    case EQUAL:
    case BV_COMP:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_eq);
      break;
    case ITE:
      assert(n_args == 3);
      btor_res = boolector_cond(
          d_solver, get_term(args[0]), get_term(args[1]), get_term(args[2]));
      break;
    case IMPLIES:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_implies);
      break;

    case BV_EXTRACT:
      assert(n_args == 1);
      assert(n_params == 2);
      btor_res =
          boolector_slice(d_solver, get_term(args[0]), params[0], params[1]);
      break;
    case BV_REPEAT:
      assert(n_args == 1);
      assert(n_params == 1);
      btor_res = boolector_repeat(d_solver, get_term(args[0]), params[0]);
      break;
    case BV_ROTATE_LEFT:
    {
      assert(n_args == 1);
      assert(n_params == 1);
      BoolectorNode* arg = get_term(args[0]);
      BoolectorSort s    = boolector_get_sort(d_solver, arg);
      uint32_t bw        = boolector_bitvec_sort_get_width(d_solver, s);
      uint32_t bw2       = static_cast<uint32_t>(log2(bw));
      BoolectorSort s2   = boolector_bitvec_sort(d_solver, bw2);
      BoolectorNode* tmp = boolector_unsigned_int(d_solver, params[0], s2);
      btor_res           = boolector_rol(d_solver, arg, tmp);
      boolector_release_sort(d_solver, s2);
      boolector_release(d_solver, tmp);
    }
      break;
    case BV_ROTATE_RIGHT:
    {
      assert(n_args == 1);
      assert(n_params == 1);
      BoolectorNode* arg = get_term(args[0]);
      BoolectorSort s    = boolector_get_sort(d_solver, arg);
      uint32_t bw        = boolector_bitvec_sort_get_width(d_solver, s);
      uint32_t bw2       = static_cast<uint32_t>(log2(bw));
      BoolectorSort s2   = boolector_bitvec_sort(d_solver, bw2);
      BoolectorNode* tmp = boolector_unsigned_int(d_solver, params[0], s2);
      btor_res           = boolector_ror(d_solver, arg, tmp);
      boolector_release_sort(d_solver, s2);
      boolector_release(d_solver, tmp);
    }
      break;
    case BV_SIGN_EXTEND:
      assert(n_args == 1);
      assert(n_params == 1);
      btor_res = boolector_sext(d_solver, get_term(args[0]), params[0]);
      break;
    case BV_ZERO_EXTEND:
      assert(n_args == 1);
      assert(n_params == 1);
      btor_res = boolector_uext(d_solver, get_term(args[0]), params[0]);
      break;
    case BV_CONCAT:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_concat);
      break;
    case AND:
    case BV_AND:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_and);
      break;
    case OR:
    case BV_OR:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_or);
      break;
    case XOR:
    case BV_XOR:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_xor);
      break;
    case BV_MULT:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_mul);
      break;
    case BV_ADD:
      assert(n_args > 1);
      btor_res = mk_term_left_assoc(args, boolector_add);
      break;
    case NOT:
    case BV_NOT:
      assert(n_args == 1);
      btor_res = boolector_not(d_solver, get_term(args[0]));
      break;
    case BV_NEG:
      assert(n_args == 1);
      btor_res = boolector_neg(d_solver, get_term(args[0]));
      break;
    case BV_REDOR:
      assert(n_args == 1);
      btor_res = boolector_redor(d_solver, get_term(args[0]));
      break;
    case BV_REDAND:
      assert(n_args == 1);
      btor_res = boolector_redand(d_solver, get_term(args[0]));
      break;
    case BV_NAND:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_nand);
      break;
    case BV_NOR:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_nor);
      break;
    case BV_XNOR:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_xnor);
      break;
    case BV_SUB:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sub);
      break;
    case BV_UDIV:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_udiv);
      break;
    case BV_UREM:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_urem);
      break;
    case BV_SDIV:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sdiv);
      break;
    case BV_SREM:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_srem);
      break;
    case BV_SMOD:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_smod);
      break;
    case BV_SHL:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sll);
      break;
    case BV_LSHR:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_srl);
      break;
    case BV_ASHR:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sra);
      break;
    case BV_ULT:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_ult);
      break;
    case BV_ULE:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_ulte);
      break;
    case BV_UGT:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_ugt);
      break;
    case BV_UGE:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_ugte);
      break;
    case BV_SLT:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_slt);
      break;
    case BV_SLE:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_slte);
      break;
    case BV_SGT:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sgt);
      break;
    case BV_SGE:
      assert(n_args == 2);
      btor_res = mk_term_left_assoc(args, boolector_sgte);
      break;
    default: assert(false);
  }
  assert(btor_res);
  std::shared_ptr<BtorTerm> res(new BtorTerm(d_solver, btor_res));
  std::cout << "const" << res << std::endl;
  return res;
}

// BoolectorNode *boolector_true (Btor *btor);
// BoolectorNode *boolector_false (Btor *btor);
// BoolectorNode *boolector_const (Btor *btor, const char *bits);
// BoolectorNode *boolector_constd (Btor *btor, BoolectorSort sort, const char *str);
// BoolectorNode *boolector_consth (Btor *btor, BoolectorSort sort, const char *str);
// BoolectorNode *boolector_unsigned_int (Btor *btor, uint32_t u, BoolectorSort sort);

// BoolectorNode *boolector_int (Btor *btor, int32_t i, BoolectorSort sort); 
// BoolectorNode *boolector_zero (Btor *btor, BoolectorSort sort); 
// BoolectorNode *boolector_ones (Btor *btor, BoolectorSort sort); 
// BoolectorNode *boolector_one (Btor *btor, BoolectorSort sort); 
// BoolectorNode *boolector_min_signed (Btor *btor, BoolectorSort sort); 
// BoolectorNode *boolector_max_signed (Btor *btor, BoolectorSort sort);

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
  return std::shared_ptr<BtorSort>(
      new BtorSort(d_solver, boolector_get_sort(d_solver, get_term(term))));
}

/* -------------------------------------------------------------------------- */

BoolectorSort
BtorSolver::get_sort(Sort sort) const
{
  return static_cast<BtorSort*>(sort.get())->d_sort;
}

BoolectorNode*
BtorSolver::get_term(Term term) const
{
  return static_cast<BtorTerm*>(term.get())->d_term;
}

BoolectorNode*
BtorSolver::mk_term_left_assoc(std::vector<Term>& args,
                               BoolectorNode* (*fun)(Btor*,
                                                     BoolectorNode*,
                                                     BoolectorNode*) ) const
{
  assert(args.size() >= 2);
  BoolectorNode *res, *tmp;

  res = fun(d_solver, get_term(args[0]), get_term(args[1]));
  for (uint32_t i = 2, n_args = args.size(); i < n_args; ++i)
  {
    tmp = fun(d_solver, res, get_term(args[i]));
    boolector_release(d_solver, res);
    res = tmp;
  }
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
      tmp = fun(d_solver, get_term(args[i]), get_term(args[j]));
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
  return res;
}

}  // namespace btor
}  // namespace smtmbt
