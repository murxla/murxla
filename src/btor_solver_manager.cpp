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

// int32_t boolector_limited_sat (Btor *btor, int32_t lod_limit, int32_t sat_limit);
//
// void boolector_set_opt (Btor *btor, BtorOption opt, uint32_t val);
// uint32_t boolector_get_opt_dflt (Btor *btor, BtorOption opt);
// const char *boolector_get_opt_shrt (Btor *btor, BtorOption opt);
// const char *boolector_get_opt_desc (Btor *btor, BtorOption opt);
// BtorOption boolector_first_opt (Btor *btor);
// BtorOption boolector_next_opt (Btor *btor, BtorOption opt);
//
// Btor *boolector_get_btor (BoolectorNode *node);
// int32_t boolector_get_id (Btor *btor, BoolectorNode *node);
//
// BoolectorNode *boolector_match_node_by_id (Btor *btor, int32_t id);
// BoolectorNode *boolector_match_node_by_symbol (Btor *btor, const char *symbol);
// BoolectorNode *boolector_match_node (Btor *btor, BoolectorNode *node);
//
// const char *boolector_get_symbol (Btor *btor, BoolectorNode *node);
// void boolector_set_symbol (Btor *btor, BoolectorNode *node, const char *symbol);
//
// uint32_t boolector_get_width (Btor *btor, BoolectorNode *node);
// uint32_t boolector_get_index_width (Btor *btor, BoolectorNode *n_array);
//
// const char *boolector_get_bits (Btor *btor, BoolectorNode *node);
// void boolector_free_bits (Btor *btor, const char *bits);
//
// const char *boolector_bv_assignment (Btor *btor, BoolectorNode *node);
// void boolector_free_bv_assignment (Btor *btor, const char *assignment);
// void boolector_print_model (Btor *btor, char *format, FILE *file);

// bool boolector_is_equal_sort (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);
//
// int32_t boolector_parse (Btor *btor, FILE *infile, const char *infile_name, FILE *outfile, char **error_msg, int32_t *status);
// int32_t boolector_parse_btor (Btor *btor, FILE *infile, const char *infile_name, FILE *outfile, char **error_msg, int32_t *status);
// int32_t boolector_parse_btor2 (Btor *btor, FILE *infile, const char *infile_name, FILE *outfile, char **error_msg, int32_t *status);
// int32_t boolector_parse_smt1 (Btor *btor, FILE *infile, const char *infile_name, FILE *outfile, char **error_msg, int32_t
// *status); int32_t boolector_parse_smt2 (Btor *btor, FILE *infile, const char *infile_name, FILE *outfile, char **error_msg, int32_t *status);
//
// void boolector_dump_btor_node (Btor *btor, FILE *file, BoolectorNode *node);
// void boolector_dump_btor (Btor *btor, FILE *file);
#if 0
// void boolector_dump_btor2 (Btor * btor, FILE * file);
#endif
// void boolector_dump_smt2_node (Btor *btor, FILE *file, BoolectorNode *node);
// void boolector_dump_smt2 (Btor *btor, FILE *file);
// void boolector_dump_aiger_ascii (Btor *btor, FILE *file, bool merge_roots);
// void boolector_dump_aiger_binary (Btor *btor, FILE *file, bool merge_roots);
//
// const char *boolector_copyright (Btor *btor);
// const char *boolector_version (Btor *btor);
//
/* -------------------------------------------------------------------------- */

// BoolectorNode *boolector_array (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_uf (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_read (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index);
// BoolectorNode *boolector_write (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index, BoolectorNode *n_value);
// BoolectorNode *boolector_param (Btor *btor, BoolectorSort sort, const char *symbol);
// BoolectorNode *boolector_fun (Btor *btor, BoolectorNode **param_nodes, uint32_t paramc, BoolectorNode *node);
// BoolectorNode *boolector_apply (Btor *btor, BoolectorNode **arg_nodes, uint32_t argc, BoolectorNode *n_fun);
// BoolectorNode *boolector_forall (Btor *btor, BoolectorNode *params[], uint32_t paramc, BoolectorNode *body);
// BoolectorNode *boolector_exists (Btor *btor, BoolectorNode *param[], uint32_t paramc, BoolectorNode *body);
//
// BoolectorSort boolector_fun_get_domain_sort (Btor *btor, const BoolectorNode *node);
// BoolectorSort boolector_fun_get_codomain_sort (Btor *btor, const BoolectorNode *node);
//
// uint32_t boolector_get_fun_arity (Btor *btor, BoolectorNode *node);
// bool boolector_is_array (Btor *btor, BoolectorNode *node);
// bool boolector_is_array_var (Btor *btor, BoolectorNode *node);
// bool boolector_is_param (Btor *btor, BoolectorNode *node);
// bool boolector_is_bound_param (Btor *btor, BoolectorNode *node);
// bool boolector_is_uf (Btor *btor, BoolectorNode *node);
// bool boolector_is_fun (Btor *btor, BoolectorNode *node);
// int32_t boolector_fun_sort_check (Btor *btor, BoolectorNode **arg_nodes, uint32_t argc, BoolectorNode *n_fun);
// void boolector_array_assignment (Btor *btor, BoolectorNode *n_array, char ***indices, char ***values, uint32_t *size);
// void boolector_free_array_assignment (Btor *btor, char **indices, char **values, uint32_t size);
// void boolector_uf_assignment (Btor *btor, BoolectorNode *n_uf, char ***args, char ***values, uint32_t *size);
// void boolector_free_uf_assignment (Btor *btor, char **args, char **values, uint32_t size);
// bool boolector_is_array_sort (Btor *btor, BoolectorSort sort);
// bool boolector_is_fun_sort (Btor *btor, BoolectorSort sort);
// BoolectorSort boolector_fun_sort (Btor *btor, BoolectorSort *domain, uint32_t arity, BoolectorSort codomain);
// BoolectorSort boolector_array_sort (Btor *btor, BoolectorSort index, BoolectorSort element);

/* -------------------------------------------------------------------------- */

#endif

}  // namespace btor
}  // namespace smtmbt
