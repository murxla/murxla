#include "btor_solver_manager.hpp"

#include <cassert>
#include <functional>
#include <iostream>

#include "util.hpp"

#define SMTMBT_BTOR_BW_MIN 1
#define SMTMBT_BTOR_BW_MAX 128

namespace smtmbt {
namespace btor {

#if 0

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

// BoolectorNode *boolector_array (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_uf (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_redxor (Btor *btor, BoolectorNode *node);
// BoolectorNode *boolector_uaddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_saddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_umulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_smulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_usubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_ssubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_sdivo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// BoolectorNode *boolector_read (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index);
// BoolectorNode *boolector_write (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index, BoolectorNode *n_value);
// BoolectorNode *boolector_param (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_fun (Btor *btor, BoolectorNode **param_nodes, uint32_t paramc, BoolectorNode *node);
// BoolectorNode *boolector_apply (Btor *btor, BoolectorNode **arg_nodes, uint32_t argc, BoolectorNode *n_fun);
// BoolectorNode *boolector_inc (Btor *btor, BoolectorNode *node);
// BoolectorNode *boolector_dec (Btor *btor, BoolectorNode *node);
// BoolectorNode *boolector_forall (Btor *btor, BoolectorNode *params[], uint32_t paramc, BoolectorNode *body);
// BoolectorNode *boolector_exists (Btor *btor, BoolectorNode *param[], uint32_t paramc, BoolectorNode *body);
// Btor *boolector_get_btor (BoolectorNode *node);
// int32_t boolector_get_id (Btor *btor, BoolectorNode *node);
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
// bool boolector_is_bv_const_zero (Btor *btor, BoolectorNode *node);
// bool boolector_is_bv_const_one (Btor *btor, BoolectorNode *node);
// bool boolector_is_bv_const_ones (Btor *btor, BoolectorNode *node);
// bool boolector_is_bv_const_max_signed (Btor *btor, BoolectorNode *node);
// bool boolector_is_bv_const_min_signed (Btor *btor, BoolectorNode *node);
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

// BoolectorSort boolector_fun_sort (Btor *btor, BoolectorSort *domain, uint32_t arity, BoolectorSort codomain);
// BoolectorSort boolector_array_sort (Btor *btor, BoolectorSort index, BoolectorSort element);
// bool boolector_is_equal_sort (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
// bool boolector_is_array_sort (Btor *btor, BoolectorSort sort);
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
  for (auto& p : d_sorts_to_theory)
  {
    std::tie(sort, theory) = p;
    boolector_release_sort(d_solver, sort);
  }
  d_sorts_to_theory.clear();
  d_theory_to_sorts.clear();

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
  // auto afixa  = new_action<BtorActionFixateAssumptions>();
  // auto relall = new_action<BtorActionReleaseAll>();
  // auto aresa  = new_action<BtorActionResetAssumptions>();
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

#endif

}  // namespace btor
}  // namespace smtmbt
