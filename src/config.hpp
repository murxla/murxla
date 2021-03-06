/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__CONFIG_H
#define __MURXLA__CONFIG_H

/**
 * Maximum number of actions.
 *
 * There is no real upper limit, but we have to define this statically, because
 * statistics are created in shared memory (and thus no dynamic data structure
 * can be used). If an exception is raised to indicate that the maximum number
 * of actions has been exceeded, increase this value.
 */
#define MURXLA_MAX_N_ACTIONS 100
/**
 * Maximum number of operators.
 *
 * There is no real upper limit, but we have to define this statically, because
 * statistics are created in shared memory (and thus no dynamic data structure
 * can be used). If an exception is raised to indicate that the maximum number
 * of operators has been exceeded, increase this value.
 */
#define MURXLA_MAX_N_OPS 300
/**
 * Maximum number of states.
 *
 * There is no real upper limit, but we have to define this statically, because
 * statistics are created in shared memory (and thus no dynamic data structure
 * can be used). If an exception is raised to indicate that the maximum number
 * of states has been exceeded, increase this value.
 */
#define MURXLA_MAX_N_STATES 100
/**
 * Maximum length of action, operator and state kinds.
 *
 * There is no real upper limit, but we have to define this statically, because
 * statistics are created in shared memory (and thus no dynamic data structure
 * can be used). If an exception is raised to indicate that the maximum length
 * of a kind has been exceeded, increase this value.
 */
#define MURXLA_MAX_KIND_LEN 100

/** Minimum bit-width for bit-vector terms. */
#define MURXLA_BW_MIN 1
/** Maximum bit-width for bit-vector terms. */
#define MURXLA_BW_MAX 128

/** Maximum length for strings representing integer values. */
#define MURXLA_INT_LEN_MAX 50
/** Maximum length for strings representing real values. */
#define MURXLA_REAL_LEN_MAX 50
/** Maximum length for strings representing rational values. */
#define MURXLA_RATIONAL_LEN_MAX 10
/** Maximum length for strings representing string values. */
#define MURXLA_STR_LEN_MAX 100

/** Minimum number of datatype selectors for a datatype constructor. */
#define MURXLA_DT_SEL_MIN 0
/** Maximum number of datatype selectors for a datatype constructor. */
#define MURXLA_DT_SEL_MAX 5
/** Minimum number of datatype constructors for a datatype. */
#define MURXLA_DT_CON_MIN 1
/** Maximum number of datatype constructors for a datatype. */
#define MURXLA_DT_CON_MAX 5
/**
 * Minimum number of datatype parameter sorts for a parametric datatype sort.
 */
#define MURXLA_DT_PARAM_SORT_MIN 1
/**
 * Maximum number of datatype parameter sorts for a parametric datatype sort.
 */
#define MURXLA_DT_PARAM_SORT_MAX 3
/**
 * The maximum number of datatypes to create (at once).
 * This is (declare-datatype ...) vs (declare-datatypes ...) in SMT-LIB.
 * For the latter, we declare at most the number below with one single command.
 */
#define MURXLA_DT_MAX_N_DTYPES 3

/** Maximum length for symbols. */
#define MURXLA_SYMBOL_LEN_MAX 128

/** Maximum number of assumptions in check-sat-assuming calls. */
#define MURXLA_MAX_N_ASSUMPTIONS_CHECK_SAT 5
/** Maximum number of context levels for push commands. */
#define MURXLA_MAX_N_PUSH_LEVELS 5
/** Maximum number of argument terms for get-value commands. */
#define MURXLA_MAX_N_TERMS_GET_VALUE 5

/** Arity of n-ary operators that expect at least one argument. */
#define MURXLA_MK_TERM_N_ARGS -1
/** Arity of n-ary operators that expect at least two arguments. */
#define MURXLA_MK_TERM_N_ARGS_BIN -2
/** Minimum number of arguments to be picked for Solver::mk_term(). */
#define MURXLA_MK_TERM_N_ARGS_MIN(arity) ((arity) < 0 ? -(arity) : (arity))
/** Maximum number of arguments to be picked for Solver::mk_term(). */
#define MURXLA_MK_TERM_N_ARGS_MAX 5

/**
 * Minimum number of quantified terms on the current level before binding
 * a variable.
 */
#define MURXLA_MIN_N_QUANT_TERMS 5

/** Maximum number of nested stores created in ActionMkTerm::mk_store. */
#define MURXLA_MAX_STORE_CHAIN_LENGTH 32

/** Maximum number of nested unions created in ActionMkTerm::mk_set_value. */
#define MURXLA_MAX_UNION_CHAIN_LENGTH 32

/** Maximum number of terms created for function body in ActionMkFun. */
#define MURXLA_MK_FUN_MAX_ARGS 5
#define MURXLA_MK_FUN_MAX_TERMS 32

#define MURXLA_CHECK_SOLVER_OPT_PREFIX "murxla-check-solver:"

#endif
