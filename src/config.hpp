#ifndef __SMTMBT__CONFIG_H
#define __SMTMBT__CONFIG_H

/**
 * Maximum number of actions.
 *
 * There is no real upper limit, but we have to define this statically, because
 * statistics are created in shared memory (and thus no dynamic data structure
 * can be used). If an exception is raised to indicate that the maximum number
 * of actions has been exceeded, increase this value.
 */
#define SMTMBT_MAX_N_ACTIONS 100
/**
 * Maximum length of action kinds.
 *
 * There is no real upper limit, but we have to define this statically, because
 * statistics are created in shared memory (and thus no dynamic data structure
 * can be used). If an exception is raised to indicate that the maximum length
 * of an action kind has been exceeded, increase this value.
 */
#define SMTMBT_MAX_LEN_ACTION_KIND 100

#define SMTMBT_BW_MIN 1
#define SMTMBT_BW_MAX 128

#define SMTMBT_INT_LEN_MAX 50
#define SMTMBT_REAL_LEN_MAX 50
#define SMTMBT_STR_LEN_MAX 100

#define SMTMBT_SYMBOL_LEN_MAX 128

#define SMTMBT_MAX_N_ASSUMPTIONS_CHECK_SAT 5
#define SMTMBT_MAX_N_PUSH_LEVELS 5
#define SMTMBT_MAX_N_TERMS_GET_VALUE 5

/* mk_term: at least one argument */
#define SMTMBT_MK_TERM_N_ARGS -1
/* mk_term: at least two arguemtns */
#define SMTMBT_MK_TERM_N_ARGS_BIN -2
/* mk_term: min number of arguments */
#define SMTMBT_MK_TERM_N_ARGS_MIN(arity) ((arity) < 0 ? -(arity) : (arity))
/* mk_term: max number of arguments */
#define SMTMBT_MK_TERM_N_ARGS_MAX 11

#endif
