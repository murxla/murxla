#include "btor_solver_manager.hpp"

#include <cassert>
#include <functional>
#include <iostream>

#include "util.hpp"

#define SMTMBT_BTOR_BW_MIN 1
#define SMTMBT_BTOR_BW_MAX 128

namespace smtmbt {
namespace btor {

/* -------------------------------------------------------------------------- */

class BtorAction : public Action
{
 public:
  BtorAction(BtorSolverManagerBase* smgr, const std::string& id)
      : Action(smgr->get_rng(), id),
        d_smgr(static_cast<BtorSolverManager*>(smgr))
  {
  }

 protected:
  BtorSolverManager* d_smgr;
};

/* -------------------------------------------------------------------------- */

/* Transition-only actions (these actions are only used to make transitions
 * without executing any action). */

/**
 * Default transition action (no condition checked).
 *
 * State:      any state if applicable
 * Transition: unconditional
 */
class BtorActionNone : public BtorAction
{
 public:
  BtorActionNone(BtorSolverManagerBase* smgr) : BtorAction(smgr, "") {}
  bool run() override { return true; }
};

/**
 * Transition from creating inputs to the next state.
 *
 * State:      create inputs
 * Transition: if there exists at least one input
 */
class BtorActionNoneCreateInputs : public BtorAction
{
 public:
  BtorActionNoneCreateInputs(BtorSolverManagerBase* smgr) : BtorAction(smgr, "")
  {
  }
  bool run() override { return d_smgr->d_stats.inputs > 0; }
};

/* -------------------------------------------------------------------------- */

// void boolector_new ();
class BtorActionNew : public BtorAction
{
 public:
  BtorActionNew(BtorSolverManagerBase* smgr) : BtorAction(smgr, "new") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    if (btor != nullptr) boolector_delete(btor);
    btor = boolector_new();
    d_smgr->set_solver(btor);
    BoolectorSort bsort = boolector_bool_sort(btor);
    d_smgr->add_sort(bsort, THEORY_BV);
    d_smgr->set_bool_sort(bsort);
    return true;
  }
  // void untrace(const char* s) override;
};

// void boolector_delete (Btor *btor);
class BtorActionDelete : public BtorAction
{
 public:
  BtorActionDelete(BtorSolverManagerBase* smgr) : BtorAction(smgr, "delete") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    d_smgr->clear();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    boolector_delete(btor);
    d_smgr->set_solver(nullptr);
    return true;
  }
  // void untrace(const char* s) override;
};

// Btor *boolector_clone (Btor *btor);
// void boolector_set_term (Btor *btor, int32_t (*fun) (void *), void *state);
// int32_t boolector_terminate (Btor *btor);
// void boolector_set_abort (void (*fun) (const char* msg));
// void boolector_set_msg_prefix (Btor *btor, const char *prefix);
// uint32_t boolector_get_refs (Btor *btor);
// void boolector_reset_time (Btor *btor);
// void boolector_reset_stats (Btor *btor);
// void boolector_print_stats (Btor *btor);
// void boolector_set_trapi (Btor *btor, FILE *apitrace);
// FILE *boolector_get_trapi (Btor *btor);
// void boolector_push (Btor *btor, uint32_t level);
// void boolector_pop (Btor *btor, uint32_t level);
// void boolector_assert (Btor *btor, BoolectorNode *node);
// void boolector_assume (Btor *btor, BoolectorNode *node);
// bool boolector_failed (Btor *btor, BoolectorNode *node);
// BoolectorNode **boolector_get_failed_assumptions (Btor *btor);

// void boolector_fixate_assumptions (Btor *btor);
class BtorActionFixateAssumptions : public BtorAction
{
 public:
  BtorActionFixateAssumptions(BtorSolverManagerBase* smgr)
      : BtorAction(smgr, "fixate_assumptions")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    assert(d_smgr->get_solver());
    boolector_fixate_assumptions(d_smgr->get_solver());
    return true;
  }
  // void untrace(const char* s) override;
};

// void boolector_reset_assumptions (Btor *btor);
class BtorActionResetAssumptions : public BtorAction
{
 public:
  BtorActionResetAssumptions(BtorSolverManagerBase* smgr)
      : BtorAction(smgr, "reset_assumptions")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    assert(d_smgr->get_solver());
    boolector_reset_assumptions(d_smgr->get_solver());
    return true;
  }
};

// int32_t boolector_sat (Btor *btor);
class BtorActionSat : public BtorAction
{
 public:
  BtorActionSat(BtorSolverManagerBase* smgr) : BtorAction(smgr, "sat") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    assert(d_smgr->get_solver());
    boolector_sat(d_smgr->get_solver());
    return true;
  }
};

// int32_t boolector_limited_sat (Btor *btor, int32_t lod_limit, int32_t sat_limit);
// int32_t boolector_simplify (Btor *btor);
// void boolector_set_sat_solver (Btor *btor, const char *solver);
// void boolector_set_opt (Btor *btor, BtorOption opt, uint32_t val);
// uint32_t boolector_get_opt (Btor *btor, BtorOption opt);
// uint32_t boolector_get_opt_min (Btor *btor, BtorOption opt);
// uint32_t boolector_get_opt_max (Btor *btor, BtorOption opt);
// uint32_t boolector_get_opt_dflt (Btor *btor, BtorOption opt);
// const char *boolector_get_opt_lng (Btor *btor, BtorOption opt);
// const char *boolector_get_opt_shrt (Btor *btor, BtorOption opt);
// const char *boolector_get_opt_desc (Btor *btor, BtorOption opt);
// bool boolector_has_opt (Btor *Btor, BtorOption opt);
// BtorOption boolector_first_opt (Btor *btor);
// BtorOption boolector_next_opt (Btor *btor, BtorOption opt);
// BoolectorNode *boolector_copy (Btor *btor, BoolectorNode *node);
// void boolector_release (Btor *btor, BoolectorNode *node);

// void boolector_release_all (Btor *btor);
class BtorActionReleaseAll : public BtorAction
{
 public:
  BtorActionReleaseAll(BtorSolverManagerBase* smgr)
      : BtorAction(smgr, "release_all")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    assert(d_smgr->get_solver());
    boolector_release_all(d_smgr->get_solver());
    return true;
  }
};

// BoolectorNode *boolector_true (Btor *btor);
class BtorActionTrue : public BtorAction
{
 public:
  BtorActionTrue(BtorSolverManagerBase* smgr) : BtorAction(smgr, "true") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    BoolectorNode* res = boolector_true(btor);
    d_smgr->add_input(res, THEORY_BV);
    boolector_release(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorNode *boolector_false (Btor *btor);
class BtorActionFalse : public BtorAction
{
 public:
  BtorActionFalse(BtorSolverManagerBase* smgr) : BtorAction(smgr, "false") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    BoolectorNode* res = boolector_false(btor);
    d_smgr->add_input(res, THEORY_BV);
    boolector_release(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorNode *boolector_implies (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
class BtorActionImplies : public BtorAction
{
 public:
  BtorActionImplies(BtorSolverManagerBase* smgr) : BtorAction(smgr, "implies") {}

  bool run() override
  {
    BoolectorSort bsort = d_smgr->get_bool_sort();
    if (!d_smgr->has_term(bsort)) return false;
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    BoolectorNode* a   = d_smgr->pick_term(bsort);
    BoolectorNode* b   = d_smgr->pick_term(bsort);
    BoolectorNode* res = boolector_implies(btor, a, b);
    d_smgr->add_term(res, THEORY_BV);
    boolector_release(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorNode *boolector_iff (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
class BtorActionIff : public BtorAction
{
 public:
  BtorActionIff(BtorSolverManagerBase* smgr) : BtorAction(smgr, "iff") {}

  bool run() override
  {
    BoolectorSort bsort = d_smgr->get_bool_sort();
    if (!d_smgr->has_term(bsort)) return false;
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    BoolectorNode* a   = d_smgr->pick_term(bsort);
    BoolectorNode* b   = d_smgr->pick_term(bsort);
    BoolectorNode* res = boolector_iff(btor, a, b);
    d_smgr->add_term(res, THEORY_BV);
    boolector_release(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorNode *boolector_eq (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
class BtorActionEq : public BtorAction
{
 public:
  BtorActionEq(BtorSolverManagerBase* smgr) : BtorAction(smgr, "eq") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    BoolectorNode* a = d_smgr->pick_term();
    BoolectorNode* b = d_smgr->pick_term(a);
    BoolectorNode* res = boolector_eq(btor, a, b);
    d_smgr->add_term(res, THEORY_BV);
    boolector_release(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorNode *boolector_ne (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
class BtorActionNe : public BtorAction
{
 public:
  BtorActionNe(BtorSolverManagerBase* smgr) : BtorAction(smgr, "ne") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    BoolectorNode* a = d_smgr->pick_term();
    BoolectorNode* b = d_smgr->pick_term(a);
    BoolectorNode* res = boolector_ne(btor, a, b);
    d_smgr->add_term(res, THEORY_BV);
    boolector_release(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorNode *boolector_const (Btor *btor, const char *bits);
// BoolectorNode *boolector_constd (Btor *btor, BoolectorSort sort, const char *str);
// BoolectorNode *boolector_consth (Btor *btor, BoolectorSort sort, const char *str);

// BoolectorNode *boolector_zero (Btor *btor, BoolectorSort sort);
class BtorActionBVZero : public BtorAction
{
 public:
  BtorActionBVZero(BtorSolverManagerBase* smgr) : BtorAction(smgr, "zero") {}

  bool run() override
  {
    if (!d_smgr->has_sort(THEORY_BV)) return false;
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    BoolectorSort s    = d_smgr->pick_sort(THEORY_BV);
    BoolectorNode* res = boolector_zero(btor, s);
    d_smgr->add_term(res, THEORY_BV);
    boolector_release(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorNode *boolector_ones (Btor *btor, BoolectorSort sort);
class BtorActionBVOnes : public BtorAction
{
 public:
  BtorActionBVOnes(BtorSolverManagerBase* smgr) : BtorAction(smgr, "ones") {}

  bool run() override
  {
    if (!d_smgr->has_sort(THEORY_BV)) return false;
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    BoolectorSort s = d_smgr->pick_sort(THEORY_BV);
    BoolectorNode* res = boolector_ones(btor, s);
    d_smgr->add_term(res, THEORY_BV);
    boolector_release(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorNode *boolector_one (Btor *btor, BoolectorSort sort);
class BtorActionBVOne : public BtorAction
{
 public:
  BtorActionBVOne(BtorSolverManagerBase* smgr) : BtorAction(smgr, "one") {}

  bool run() override
  {
    if (!d_smgr->has_sort(THEORY_BV)) return false;
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    BoolectorSort s = d_smgr->pick_sort(THEORY_BV);
    BoolectorNode* res = boolector_one(btor, s);
    d_smgr->add_term(res, THEORY_BV);
    boolector_release(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorNode *boolector_min_signed (Btor *btor, BoolectorSort sort);
// BoolectorNode *boolector_max_signed (Btor *btor, BoolectorSort sort);
// BoolectorNode *boolector_unsigned_int (Btor *btor, uint32_t u, BoolectorSort sort);
// BoolectorNode *boolector_int (Btor *btor, int32_t i, BoolectorSort sort);
// BoolectorNode *boolector_var (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_array (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_uf (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_not (Btor *btor, BoolectorNode *node);
// BoolectorNode *boolector_neg (Btor *btor, BoolectorNode *node);
// BoolectorNode *boolector_redor (Btor *btor, BoolectorNode *node);
// BoolectorNode *boolector_redxor (Btor *btor, BoolectorNode *node);
// BoolectorNode *boolector_redand (Btor *btor, BoolectorNode *node);
// BoolectorNode *boolector_slice (Btor *btor, BoolectorNode *node, uint32_t upper, uint32_t lower);
// BoolectorNode *boolector_uext (Btor *btor, BoolectorNode *node, uint32_t width);
// BoolectorNode *boolector_sext (Btor *btor, BoolectorNode *node, uint32_t width);
// BoolectorNode *boolector_xor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_xnor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_and (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_nand (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_or (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_nor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_add (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_uaddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_saddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_mul (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_umulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_smulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_ult (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_slt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_ulte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_slte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_ugt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_sgt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_ugte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_sgte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_sll (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_srl (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_sra (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_rol (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_ror (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_sub (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_usubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_ssubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_udiv (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_sdiv (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_sdivo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_urem (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_srem (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_smod (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_concat (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_read (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index);
// BoolectorNode *boolector_write (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index, BoolectorNode *n_value);
// BoolectorNode *boolector_cond (Btor *btor, BoolectorNode *n_cond, BoolectorNode *n_then, BoolectorNode *n_else);
// BoolectorNode *boolector_param (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_fun (Btor *btor, BoolectorNode **param_nodes, uint32_t paramc, BoolectorNode *node);
// BoolectorNode *boolector_apply (Btor *btor, BoolectorNode **arg_nodes, uint32_t argc, BoolectorNode *n_fun);
// BoolectorNode *boolector_inc (Btor *btor, BoolectorNode *node);
// BoolectorNode *boolector_dec (Btor *btor, BoolectorNode *node);
// BoolectorNode *boolector_forall (Btor *btor, BoolectorNode *params[], uint32_t paramc, BoolectorNode *body);
// BoolectorNode *boolector_exists (Btor *btor, BoolectorNode *param[], uint32_t paramc, BoolectorNode *body);
// Btor *boolector_get_btor (BoolectorNode *node);
// int32_t boolector_get_id (Btor *btor, BoolectorNode *node);
// BoolectorSort boolector_get_sort (Btor *btor, const BoolectorNode *node);
// BoolectorSort boolector_fun_get_domain_sort (Btor *btor, const BoolectorNode *node);
// BoolectorSort boolector_fun_get_codomain_sort (Btor *btor, const BoolectorNode *node);
// BoolectorNode *boolector_match_node_by_id (Btor *btor, int32_t id);
// BoolectorNode *boolector_match_node_by_symbol (Btor *btor, const char *symbol);
// BoolectorNode *boolector_match_node (Btor *btor, BoolectorNode *node);
// const char *boolector_get_symbol (Btor *btor, BoolectorNode *node);
// void boolector_set_symbol (Btor *btor, BoolectorNode *node, const char *symbol);
// uint32_t boolector_get_width (Btor *btor, BoolectorNode *node);
// uint32_t boolector_get_index_width (Btor *btor, BoolectorNode *n_array);
// const char *boolector_get_bits (Btor *btor, BoolectorNode *node);
// void boolector_free_bits (Btor *btor, const char *bits);
// uint32_t boolector_get_fun_arity (Btor *btor, BoolectorNode *node);
// bool boolector_is_const (Btor *btor, BoolectorNode *node);
// bool boolector_is_var (Btor *btor, BoolectorNode *node);
// bool boolector_is_array (Btor *btor, BoolectorNode *node);
// bool boolector_is_array_var (Btor *btor, BoolectorNode *node);
// bool boolector_is_param (Btor *btor, BoolectorNode *node);
// bool boolector_is_bound_param (Btor *btor, BoolectorNode *node);
// bool boolector_is_uf (Btor *btor, BoolectorNode *node);
// bool boolector_is_fun (Btor *btor, BoolectorNode *node);
// int32_t boolector_fun_sort_check (Btor *btor, BoolectorNode **arg_nodes, uint32_t argc, BoolectorNode *n_fun);
// const char *boolector_bv_assignment (Btor *btor, BoolectorNode *node);
// void boolector_free_bv_assignment (Btor *btor, const char *assignment);
// void boolector_array_assignment (Btor *btor, BoolectorNode *n_array, char ***indices, char ***values, uint32_t *size);
// void boolector_free_array_assignment (Btor *btor, char **indices, char **values, uint32_t size);
// void boolector_uf_assignment (Btor *btor, BoolectorNode *n_uf, char ***args, char ***values, uint32_t *size);
// void boolector_free_uf_assignment (Btor *btor, char **args, char **values, uint32_t size);
// void boolector_print_model (Btor *btor, char *format, FILE *file);

// BoolectorSort boolector_bool_sort (Btor *btor);
class BtorActionBoolSort : public BtorAction
{
 public:
  BtorActionBoolSort(BtorSolverManagerBase* smgr)
      : BtorAction(smgr, "bool_sort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    BoolectorSort res = boolector_bool_sort(btor);
    d_smgr->add_sort(res, THEORY_BV);
    boolector_release_sort(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorSort boolector_bitvec_sort (Btor *btor, uint32_t width);
class BtorActionBVSort : public BtorAction
{
 public:
  BtorActionBVSort(BtorSolverManagerBase* smgr)
      : BtorAction(smgr, "bitvec_sort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Btor* btor = d_smgr->get_solver();
    assert(btor);
    RNGenerator& rng  = d_smgr->get_rng();
    uint32_t bw       = rng.pick_uint32(SMTMBT_BTOR_BW_MIN, SMTMBT_BTOR_BW_MAX);
    BoolectorSort res = boolector_bitvec_sort(btor, bw);
    d_smgr->add_sort(res, THEORY_BV);
    boolector_release_sort(btor, res);
    return true;
  }
  // void untrace(const char* s) override;
};

// BoolectorSort boolector_fun_sort (Btor *btor, BoolectorSort *domain, uint32_t arity, BoolectorSort codomain);
// BoolectorSort boolector_array_sort (Btor *btor, BoolectorSort index, BoolectorSort element);
// BoolectorSort boolector_copy_sort (Btor *btor, BoolectorSort sort);
// void boolector_release_sort (Btor *btor, BoolectorSort sort);
// bool boolector_is_equal_sort (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// bool boolector_is_array_sort (Btor *btor, BoolectorSort sort);
// bool boolector_is_bitvec_sort (Btor *btor, BoolectorSort sort);
// bool boolector_is_fun_sort (Btor *btor, BoolectorSort sort);
// int32_t boolector_parse (Btor *btor, FILE *infile, const char *infile_name, FILE *outfile, char **error_msg, int32_t *status);
// int32_t boolector_parse_btor (Btor *btor, FILE *infile, const char *infile_name, FILE *outfile, char **error_msg, int32_t *status);
// int32_t boolector_parse_btor2 (Btor *btor, FILE *infile, const char *infile_name, FILE *outfile, char **error_msg, int32_t *status);
// int32_t boolector_parse_smt1 (Btor *btor, FILE
// *infile, const char *infile_name, FILE *outfile, char **error_msg, int32_t
// *status); int32_t boolector_parse_smt2 (Btor *btor, FILE *infile, const char
// *infile_name, FILE *outfile, char **error_msg, int32_t *status);
// void boolector_dump_btor_node (Btor *btor, FILE *file, BoolectorNode *node);
// void boolector_dump_btor (Btor *btor, FILE *file);
#if 0
// void boolector_dump_btor2 (Btor * btor, FILE * file);
#endif
// void boolector_dump_smt2_node (Btor *btor, FILE *file, BoolectorNode *node);
// void boolector_dump_smt2 (Btor *btor, FILE *file);
// void boolector_dump_aiger_ascii (Btor *btor, FILE *file, bool merge_roots);
// void boolector_dump_aiger_binary (Btor *btor, FILE *file, bool merge_roots);
// const char *boolector_copyright (Btor *btor);
// const char *boolector_version (Btor *btor);
/* -------------------------------------------------------------------------- */

size_t
BoolectorNodeHashFunc::operator()(const BoolectorNode* n) const
{
  Btor* btor = boolector_get_btor(const_cast<BoolectorNode*>(n));
  int32_t id = boolector_get_node_id(btor, const_cast<BoolectorNode*>(n));
  return std::hash<int32_t>{}(id);
}

size_t
BoolectorSortHashFunc::operator()(const BoolectorSort s) const
{
  return std::hash<BoolectorSort>{}(s);
}

/* -------------------------------------------------------------------------- */

void
BtorSolverManager::clear()
{
  assert(d_terms.empty() || d_solver);
  TheoryId theory;
  BoolectorSort sort;
  BtorSolverManager::SortMap smap;
  BtorSolverManager::TermMap tmap;

  for (auto& p : d_terms)
  {
    std::tie(theory, smap) = p;
    for (auto& p : smap)
    {
      std::tie(sort, tmap) = p;
      for (auto& p : tmap)
      {
        boolector_release(d_solver, p.first);
      }
    }
  }
  d_terms.clear();
  for (auto& p : d_sorts2theory)
  {
    std::tie(sort, theory) = p;
    boolector_release_sort(d_solver, sort);
  }
  d_sorts2theory.clear();
  d_theory2sorts.clear();

  if (get_bool_sort())
  {
    boolector_release_sort(d_solver, get_bool_sort());
    set_bool_sort(0);
  }
}

BtorSolverManager::~BtorSolverManager()
{
  clear();

  if (d_solver != nullptr)
  {
    boolector_delete(d_solver);
  }
}

BoolectorNode*
BtorSolverManager::copy_term(BoolectorNode* term)
{
  return boolector_copy(d_solver, term);
}

BoolectorSort
BtorSolverManager::copy_sort(BoolectorSort sort)
{
  return boolector_copy_sort(d_solver, sort);
}

BoolectorSort
BtorSolverManager::get_sort(BoolectorNode* term)
{
  return boolector_get_sort(d_solver, term);
}

BoolectorSort
BtorSolverManager::get_bool_sort()
{
  return d_bool_sort;
}

void
BtorSolverManager::set_bool_sort(BoolectorSort sort)
{
  d_bool_sort = sort;
}

void
BtorSolverManager::configure()
{
  /* Actions ................................................................ */
  /* create/delete solver */
  auto adelete = new_action<BtorActionDelete>();
  auto anew    = new_action<BtorActionNew>();
  /* make consts */
  auto afalse = new_action<BtorActionFalse>();
  auto atrue  = new_action<BtorActionTrue>();
  auto aone   = new_action<BtorActionBVOne>();
  auto aones  = new_action<BtorActionBVOnes>();
  auto azero  = new_action<BtorActionBVZero>();
  /* make sort */
  auto aboolsort = new_action<BtorActionBoolSort>();
  auto abvsort   = new_action<BtorActionBVSort>();
  /* make terms */
  auto aeq  = new_action<BtorActionEq>();
  auto aiff = new_action<BtorActionIff>();
  auto aimp = new_action<BtorActionImplies>();
  auto ane  = new_action<BtorActionNe>();
  /* commands */
  auto afixa  = new_action<BtorActionFixateAssumptions>();
  auto relall = new_action<BtorActionReleaseAll>();
  auto aresa  = new_action<BtorActionResetAssumptions>();
  auto asat   = new_action<BtorActionSat>();
  /* transitions */
  auto tinputs = new_action<BtorActionNoneCreateInputs>();
  auto tnone   = new_action<BtorActionNone>();

  /* States ................................................................. */
  auto sdelete = d_fsm.new_state("delete");
  auto sinputs = d_fsm.new_state("create inputs");
  auto snew    = d_fsm.new_state("new");
  auto ssat    = d_fsm.new_state("sat");
  auto sterms  = d_fsm.new_state("create terms");
  auto sfinal  = d_fsm.new_state("final", nullptr, true);

  /* Transitions ............................................................ */
  snew->add_action(anew, 10, sinputs);

  sinputs->add_action(atrue, 20);
  sinputs->add_action(afalse, 20);
  sinputs->add_action(aboolsort, 2);
  sinputs->add_action(abvsort, 20);
  sinputs->add_action(azero, 20);
  sinputs->add_action(aone, 20);
  sinputs->add_action(aones, 20);
  sinputs->add_action(tinputs, 10, sterms);

  sterms->add_action(aeq, 10);
  sterms->add_action(aiff, 10);
  sterms->add_action(aimp, 10);
  sterms->add_action(ane, 10);
  sterms->add_action(tnone, 1, ssat);

  ssat->add_action(asat, 10, sdelete);

  sdelete->add_action(adelete, 10, sfinal);

  // TODO reset_assumptions
  // TODO fixate_assumptions
  // TODO release_all

  /* Initial State .......................................................... */
  d_fsm.set_init_state(snew);
}

/* -------------------------------------------------------------------------- */

}  // namespace btor
}  // namespace smtmbt
