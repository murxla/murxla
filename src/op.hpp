/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__OP_H
#define __MURXLA__OP_H

#include <cassert>
#include <cstdint>
#include <unordered_map>
#include <vector>

#include "sort.hpp"

namespace murxla {

namespace statistics {
struct Statistics;
}

/* -------------------------------------------------------------------------- */

/** The struct representing an operator. */
struct Op
{
  /** The kind of an operator. */
  using Kind = std::string;

  /**
   * \addtogroup operator-kinds
   * @{
   */

  /** The operator kind representing an undefined kind. */
  inline static const Kind UNDEFINED = "OP_UNDEFINED";
  /** The operator kind representing an internal kind. */
  inline static const Kind INTERNAL = "OP_INTERNAL";

  //// Leaf kinds (only needed for Term::get_kind)
  /**
   * The operator kind representing a first order constant.
   *
   * Created with Solver::mk_const().
   */
  inline static const Kind CONSTANT = "OP_CONSTANT";
  /** The operator kind representing a const array. */
  // inline static const Kind CONST_ARRAY = "OP_CONST_ARRAY";
  /**
   * The operator kind representing a value.
   *
   * Created with Solver::mk_value().
   */
  inline static const Kind VALUE = "OP_VALUE";
  /**
   * The operator kind representing a variable.
   *
   * Created with Solver::mk_var().
   */
  inline static const Kind VARIABLE = "OP_VARIABLE";
  /**
   * The operator kind representing a function.
   *
   * Created with Solver::mk_fun().
   */
  inline static const Kind FUN = "OP_FUN";

  //// Special cases
  /**
   * The operator kind representing the distinct operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_ANY, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (distinct <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind DISTINCT = "OP_DISTINCT";
  /**
   * The operator kind representing the equality operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_ANY, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (= <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind EQUAL = "OP_EQUAL";
  /**
   * The operator kind representing the if-then-else operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_BOOL, SORT_ANY, SORT_ANY}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (ite <condition> <then> <else>)
   * \endverbatim
   */
  inline static const Kind ITE = "OP_ITE";

  //// Arrays
  /**
   * The operator kind representing the select operator on arrays.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_ARRAY, SORT_ANY}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (select <array> <index term>)
   * \endverbatim
   */
  inline static const Kind ARRAY_SELECT = "OP_ARRAY_SELECT";
  /**
   * The operator kind representing the store operator on arrays.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_ARRAY, SORT_ANY, SORT_ANY}`
   *   - [0]: array term
   *   - [1]: index term
   *   - [2]: value term
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (store <array> <index term> <value term>)
   * \endverbatim
   */
  inline static const Kind ARRAY_STORE = "OP_ARRAY_STORE";

  //// Boolean
  /**
   * The operator kind representing the Boolean and operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_BOOL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (and <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind AND = "OP_AND";
  /**
   * The operator kind representing the Boolean if-and-only-if operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BOOL, SORT_BOOL}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (= <boolean term_1> ... <boolean term_n>)
   * \endverbatim
   */
  inline static const Kind IFF = "OP_IFF";
  /**
   * The operator kind representing the Boolean implies operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_BOOL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (=> <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind IMPLIES = "OP_IMPLIES";
  /**
   * The operator kind representing the Boolean not operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BOOL}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (not <term_1>)
   * \endverbatim
   */
  inline static const Kind NOT = "OP_NOT";
  /**
   * The operator kind representing the Boolean or operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_BOOL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (or <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind OR = "OP_OR";
  /**
   * The operator kind representing the Boolean xor operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BOOL, SORT_BOOL}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (xor <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind XOR = "OP_XOR";

  //// BV
  /**
   * The operator kind representing the bit-vector extract operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BV}`
   * - **indices**: `{uint32_t, uint32_t}`
   *   - [0]: upper index
   *   - [1]: lower index
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ extract <hi> <lo>) <term>)
   * \endverbatim
   */
  inline static const Kind BV_EXTRACT = "OP_BV_EXTRACT";
  /**
   * The operator kind representing the bit-vector repeat operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BV}`
   * - **indices**: `{uint32_t}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ repeat <n>) <term>)
   * \endverbatim
   */
  inline static const Kind BV_REPEAT = "OP_BV_REPEAT";
  /**
   * The operator kind representing the bit-vector rotate left operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BV}`
   * - **indices**: `{uint32_t}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ rotate_left <n>) <term>)
   * \endverbatim
   */
  inline static const Kind BV_ROTATE_LEFT = "OP_BV_ROTATE_LEFT";
  /**
   * The operator kind representing the bit-vector rotate right operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BV}`
   * - **indices**: `{uint32_t}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ rotate_right <n>) <term>)
   * \endverbatim
   */
  inline static const Kind BV_ROTATE_RIGHT = "OP_BV_ROTATE_RIGHT";
  /**
   * The operator kind representing the bit-vector signed extension operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BV}`
   * - **indices**: `{uint32_t}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ sign_extend <n>) <term>)
   * \endverbatim
   */
  inline static const Kind BV_SIGN_EXTEND = "OP_BV_SIGN_EXTEND";
  /**
   * The operator kind representing the bit-vector zero extension operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BV}`
   * - **indices**: `{uint32_t}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ zero_extend <n>) <term>)
   * \endverbatim
   */
  inline static const Kind BV_ZERO_EXTEND = "OP_BV_ZERO_EXTEND";
  /**
   * The operator kind representing the bit-vector addition operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_BV, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvadd <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind BV_ADD = "OP_BV_ADD";
  /**
   * The operator kind representing the bit-vector and operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_BV, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvand <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind BV_AND = "OP_BV_AND";
  /**
   * The operator kind representing the bit-vector arithmetic right shift
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   *   - [0]: the term to shift
   *   - [1]: the shift term
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvashr <term> <shift>)
   * \endverbatim
   */
  inline static const Kind BV_ASHR = "OP_BV_ASHR";
  /**
   * The operator kind representing the bit-vector comparison operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvcomp <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_COMP = "OP_BV_COMP";
  /**
   * The operator kind representing the bit-vector concatenation operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_BV, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (concat <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_CONCAT = "OP_BV_CONCAT";
  /**
   * The operator kind representing the bit-vector logical right shift operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   *   - [0]: the term to shift
   *   - [1]: the shift term
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvlshr <term> <shift>)
   * \endverbatim
   */
  inline static const Kind BV_LSHR = "OP_BV_LSHR";
  /**
   * The operator kind representing the bit-vector multiplication operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_BV, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvmul <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind BV_MULT = "OP_BV_MULT";
  /**
   * The operator kind representing the bit-vector nand operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvnand <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_NAND = "OP_BV_NAND";
  /**
   * The operator kind representing the bit-vector negation (two's complement)
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvneg <term>)
   * \endverbatim
   */
  inline static const Kind BV_NEG = "OP_BV_NEG";
  /**
   * The operator kind representing the bit-vector nor operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvnor <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_NOR = "OP_BV_NOR";
  /**
   * The operator kind representing the bit-vector not operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvnot <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_NOT = "OP_BV_NOT";
  /**
   * The operator kind representing the bit-vector or operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_BV, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvor <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind BV_OR = "OP_BV_OR";
  /**
   * The operator kind representing the bit-vector signed division operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvsdiv <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_SDIV = "OP_BV_SDIV";
  /**
   * The operator kind representing the bit-vector signed greater or equal
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvsge <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_SGE = "OP_BV_SGE";
  /**
   * The operator kind representing the bit-vector signed greater than operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvsgt <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_SGT = "OP_BV_SGT";
  /**
   * The operator kind representing the bit-vector left shift operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   *   - [0]: the term to shift
   *   - [1]: the shift term
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvshl <term> <shift>)
   * \endverbatim
   */
  inline static const Kind BV_SHL = "OP_BV_SHL";
  /**
   * The operator kind representing the bit-vector signed less or equal
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvsle <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_SLE = "OP_BV_SLE";
  /**
   * The operator kind representing the bit-vector signed less than operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvslt <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_SLT = "OP_BV_SLT";
  /**
   * The operator kind representing the bit-vector signed remainder operator
   * (sign follows divisor).
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvsmod <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_SMOD = "OP_BV_SMOD";
  /**
   * The operator kind representing the bit-vector signed remainder operator
   * (sign follows dividend).
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvsrem <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_SREM = "OP_BV_SREM";
  /**
   * The operator kind representing the bit-vector subtraction operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvsub <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_SUB = "OP_BV_SUB";
  /**
   * The operator kind representing the bit-vector unsigned division operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvudiv <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_UDIV = "OP_BV_UDIV";
  /**
   * The operator kind representing the bit-vector unsigned greater or equal
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvuge <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_UGE = "OP_BV_UGE";
  /**
   * The operator kind representing the bit-vector unsigned greater than
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvugt <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_UGT = "OP_BV_UGT";
  /**
   * The operator kind representing the bit-vector unsigned less or equal
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvule <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_ULE = "OP_BV_ULE";
  /**
   * The operator kind representing the bit-vector unsigned less than operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvult <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_ULT = "OP_BV_ULT";
  /**
   * The operator kind representing the bit-vector unsigned remainder operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvurem <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_UREM = "OP_BV_UREM";
  /**
   * The operator kind representing the bit-vector xnor operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_BV, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvxnor <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_XNOR = "OP_BV_XNOR";
  /**
   * The operator kind representing the bit-vector xor operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BV, SORT_BV}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (bvxor <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind BV_XOR = "OP_BV_XOR";

  //// Datatypes
  /**
   * The operator kind representing the datatypes apply constructor operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **sort**: SORT_DT
   * - **str_args**: `{<constructor name>}`
   * - **args**: `{SORT_ANY, ...}`
   *   - [0..n-1]: terms of selector codomain sort for each selector, in
   *               declaration order
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (<cons> <args...>)
   * \endverbatim
   */
  inline static const Kind DT_APPLY_CONS = "OP_DT_APPLY_CONS";
  /**
   * The operator kind representing the datatypes apply selector operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **str_args**: `{<constructor name>, <selector name>}`
   * - **args**: `{SORT_ANY}`
   *   - [0]: term of selector codomain sort
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (<sel> <term>)
   * \endverbatim
   */
  inline static const Kind DT_APPLY_SEL = "OP_DT_APPLY_SEL";
  /**
   * The operator kind representing the datatypes tester operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **str_args**: `{<constructor name>}`
   * - **args**: `{SORT_DT}`
   *   - [0]: term of selector codomain sort
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ is <cons>) <term>)
   * \endverbatim
   */
  inline static const Kind DT_APPLY_TESTER = "OP_DT_APPLY_TESTER";
  /**
   * The operator kind representing the datatypes updater operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **str_args**: `{<constructor name>, <selector name>}`
   * - **args**: `{SORT_DT}`
   *   - [0]: term of selector codomain sort
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ update <sel>) <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind DT_APPLY_UPDATER = "OP_DT_APPLY_UPDATER";
  /**
   * The operator kind representing the datatypes match operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_ANY, ...}`
   *   - [0..n-1]: match (binder) case terms
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (match <term> <match_case_1> ... <match_case_n>)
   * \endverbatim
   */
  inline static const Kind DT_MATCH = "OP_DT_MATCH";
  /**
   * The operator kind representing the datatypes match case without binders.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **sort**: SORT_DT
   * - **str_args**: `{<constructor name>}`
   * - **args**: `{SORT_ANY}`
   *   - [0]: match term
   *
   * @note This match case operator is used for constructors without selectors.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (<cons> <term>)
   * \endverbatim
   */
  inline static const Kind DT_MATCH_CASE = "OP_DT_MATCH_CASE";
  /**
   * The operator kind representing the datatypes match with binders.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **sort**: SORT_DT
   * - **str_args**: `{<constructor name>}` (regular pattern) or `{}` (variable
   *                 pattern)
   * - **args**: `{SORT_ANY}`
   *   - [0..n-2]: variables (one per selector for regular pattern)
   *   - [n-1]: match term
   *
   * @note This match case operator is used for constructors with selectors.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((<cons> <binder_1> ... <binder_n>) (const <term_1> ... <term_n>))
   *
   *     (<binder> <term>)
   * \endverbatim
   */
  inline static const Kind DT_MATCH_BIND_CASE = "OP_DT_MATCH_BIND_CASE";
  // inline static const Kind DT_TUPLE_PROJECT   = "OP_DT_TUPLE_PROJECT";

  //// FP
  /**
   * The operator kind representing the floating-point to floating-point
   * conversion operator from a bit-vector in in IEEE 754-2008 interchange
   * format.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BV}`
   * - **indices**: `{uint32_t, uint32_t}`
   *   - [0]: exponent size
   *   - [1]: signifcand size
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ to_fp eb sb) <term>)
   * \endverbatim
   */
  inline static const Kind FP_TO_FP_FROM_BV = "OP_FP_TO_FP_FROM_BV";
  /**
   * The operator kind representing the floating-point to floating-point
   * conversion operator from a signed machine integer, represented as two's
   * complement bit-vector.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_RM, SORT_BV}`
   * - **indices**: `{uint32_t, uint32_t}`
   *   - [0]: exponent size
   *   - [1]: signifcand size
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ to_fp eb sb) <term>)
   * \endverbatim
   */
  inline static const Kind FP_TO_FP_FROM_SBV = "OP_FP_TO_FP_FROM_SBV";
  /**
   * The operator kind representing the floating-point to floating-point
   * conversion operator from a floating-point term.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_RM, SORT_FP}`
   * - **indices**: `{uint32_t, uint32_t}`
   *   - [0]: exponent size
   *   - [1]: signifcand size
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ to_fp eb sb) <term>)
   * \endverbatim
   */
  inline static const Kind FP_TO_FP_FROM_FP = "OP_FP_TO_FP_FROM_FP";
  /**
   * The operator kind representing the floating-point to floating-point
   * conversion operator from an unsigned machine integer, represented as a
   * bit-vector.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_RM, SORT_BV}`
   * - **indices**: `{uint32_t, uint32_t}`
   *   - [0]: exponent size
   *   - [1]: signifcand size
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ to_fp eb sb) <term>)
   * \endverbatim
   */
  inline static const Kind FP_TO_FP_FROM_UBV = "OP_FP_TO_FP_FROM_UBV";
  /**
   * The operator kind representing the floating-point to floating-point
   * conversion operator from a real term.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_RM, SORT_REAL}`
   * - **indices**: `{uint32_t, uint32_t}`
   *   - [0]: exponent size
   *   - [1]: signifcand size
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ to_fp eb sb) <term>)
   * \endverbatim
   */
  inline static const Kind FP_TO_FP_FROM_REAL = "OP_FP_TO_FP_FROM_REAL";
  /**
   * The operator kind representing the floating-point to signed bit-vector
   * conversion operator from a floating-point term.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_RM, SORT_FP}`
   * - **indices**: `{uint32_t}`
   *   - [0]: bit-vector size
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ fp.to_sbv m) <term>)
   * \endverbatim
   */
  inline static const Kind FP_TO_SBV = "OP_FP_TO_SBV";
  /**
   * The operator kind representing the floating-point to unsigned bit-vector
   * conversion operator from a floating-point term.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_RM, SORT_FP}`
   * - **indices**: `{uint32_t}`
   *   - [0]: bit-vector size
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ fp.to_ubv m) <term>)
   * \endverbatim
   */
  inline static const Kind FP_TO_UBV = "OP_FP_TO_UBV";
  /**
   * The operator kind representing the floating-point absolute value operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.abs <term>)
   * \endverbatim
   */
  inline static const Kind FP_ABS = "OP_FP_ABS";
  /**
   * The operator kind representing the floating-point addition operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_RM, SORT_FP, SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.abs <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind FP_ADD = "OP_FP_ADD";
  /**
   * The operator kind representing the floating-point division operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_RM, SORT_FP, SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.div <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind FP_DIV = "OP_FP_DIV";
  /**
   * The operator kind representing the floating-point equality operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_FP, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.eq <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind FP_EQ = "OP_FP_EQ";
  /**
   * The operator kind representing the floating-point fused multiplication and
   * addition operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 4
   * - **args**: `{SORT_RM, SORT_FP, SORT_FP, SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.fma <term_1> <term_2> <term_3> <term_4>)
   * \endverbatim
   */
  inline static const Kind FP_FMA = "OP_FP_FMA";
  /**
   * The operator kind representing the floating-point `fp` operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_RM, SORT_BV, SORT_BV, SORT_BV}`
   *   - [0]: the sign bit
   *   - [1]: the exponent
   *   - [2]: the signifcand
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind FP_FP = "OP_FP_FP";
  /**
   * The operator kind representing the floating-point isNormal tester
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.isNormal <term>)
   * \endverbatim
   */
  inline static const Kind FP_IS_NORMAL = "OP_FP_IS_NORMAL";
  /**
   * The operator kind representing the floating-point isSubnormal tester
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.isSubnormal <term>)
   * \endverbatim
   */
  inline static const Kind FP_IS_SUBNORMAL = "OP_FP_IS_SUBNORMAL";
  /**
   * The operator kind representing the floating-point isInfinite tester
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.isInfinite <term>)
   * \endverbatim
   */
  inline static const Kind FP_IS_INF = "OP_FP_IS_INF";
  /**
   * The operator kind representing the floating-point isNaN tester
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.isNaN <term>)
   * \endverbatim
   */
  inline static const Kind FP_IS_NAN = "OP_FP_IS_NAN";
  /**
   * The operator kind representing the floating-point isNegative tester
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.isNegative <term>)
   * \endverbatim
   */
  inline static const Kind FP_IS_NEG = "OP_FP_IS_NEG";
  /**
   * The operator kind representing the floating-point isPositive tester
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.isPositive <term>)
   * \endverbatim
   */
  inline static const Kind FP_IS_POS = "OP_FP_IS_POS";
  /**
   * The operator kind representing the floating-point isZero tester
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.isZero <term>)
   * \endverbatim
   */
  inline static const Kind FP_IS_ZERO = "OP_FP_IS_ZERO";
  /**
   * The operator kind representing the floating-point less than operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_FP, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.lt <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind FP_LT = "OP_FP_LT";
  /**
   * The operator kind representing the floating-point less or equal operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_FP, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.leq <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind FP_LEQ = "OP_FP_LEQ";
  /**
   * The operator kind representing the floating-point greater than operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_FP, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.gt <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind FP_GT = "OP_FP_GT";
  /**
   * The operator kind representing the floating-point greater or equal
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_FP, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.geq <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind FP_GEQ = "OP_FP_GEQ";
  /**
   * The operator kind representing the floating-point max operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_FP, SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.max <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind FP_MAX = "OP_FP_MAX";
  /**
   * The operator kind representing the floating-point min operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_FP, SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.min <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind FP_MIN = "OP_FP_MIN";
  /**
   * The operator kind representing the floating-point multiplication operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_RM, SORT_FP, SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.mul <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind FP_MUL = "OP_FP_MUL";
  /**
   * The operator kind representing the floating-point negation operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.neg <term>)
   * \endverbatim
   */
  inline static const Kind FP_NEG = "OP_FP_NEG";
  /**
   * The operator kind representing the floating-point remainder operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_FP, SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.rem <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind FP_REM = "OP_FP_REM";
  /**
   * The operator kind representing the floating-point round to integral
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_RM, SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.roundToIntegral <term>)
   * \endverbatim
   */
  inline static const Kind FP_RTI = "OP_FP_RTI";
  /**
   * The operator kind representing the floating-point square root operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_RM, SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.sqrt <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind FP_SQRT = "OP_FP_SQRT";
  /**
   * The operator kind representing the floating-point subtraction operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_RM, SORT_FP, SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.sub <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind FP_SUB = "OP_FP_SUB";
  /**
   * The operator kind representing the floating-point to real conversion
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_FP}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (fp.to_real <term>)
   * \endverbatim
   */
  inline static const Kind FP_TO_REAL = "OP_FP_TO_REAL";

  //// Ints
  /**
   * The operator kind representing the integer divisible operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_INT}`
   * - **indices**: `{uint32_t}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ divisible n) <term>)
   * \endverbatim
   */
  inline static const Kind INT_IS_DIV = "OP_INT_IS_DIV";
  /**
   * The operator kind representing the integer negation operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_INT}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (- <term>)
   * \endverbatim
   */
  inline static const Kind INT_NEG    = "OP_INT_NEG";
  /**
   * The operator kind representing the integer subtraction operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_INT, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (- <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind INT_SUB    = "OP_INT_SUB";
  /**
   * The operator kind representing the integer addition operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_INT, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (+ <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind INT_ADD    = "OP_INT_ADD";
  /**
   * The operator kind representing the integer multiplication operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_INT, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (* <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind INT_MUL    = "OP_INT_MUL";
  /**
   * The operator kind representing the integer division operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_INT, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (div <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind INT_DIV    = "OP_INT_DIV";
  /**
   * The operator kind representing the integer modulus operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_INT, SORT_INT}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (mod <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind INT_MOD    = "OP_INT_MOD";
  /**
   * The operator kind representing the integer absolute value operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_INT}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (abs <term>)
   * \endverbatim
   */
  inline static const Kind INT_ABS    = "OP_INT_ABS";
  /**
   * The operator kind representing the integer less than operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_INT, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (< <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind INT_LT     = "OP_INT_LT";
  /**
   * The operator kind representing the integer less or equal operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_INT, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (<= <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind INT_LTE    = "OP_INT_LTE";
  /**
   * The operator kind representing the integer greater than operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_INT, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (> <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind INT_GT     = "OP_INT_GT";
  /**
   * The operator kind representing the integer greater or equal operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_INT, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (>= <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind INT_GTE    = "OP_INT_GTE";
  /**
   * The operator kind representing the integer to real conversion operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_INT}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (to_real <term>)
   * \endverbatim
   */
  inline static const Kind INT_TO_REAL = "OP_INT_TO_REAL";

  //// Reals
  /**
   * The operator kind representing the reals negation operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (- <term>)
   * \endverbatim
   */
  inline static const Kind REAL_NEG    = "OP_REAL_NEG";
  /**
   * The operator kind representing the reals subtraction operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REAL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (- <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind REAL_SUB    = "OP_REAL_SUB";
  /**
   * The operator kind representing the reals addition operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REAL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (+ <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind REAL_ADD    = "OP_REAL_ADD";
  /**
   * The operator kind representing the reals multiplication operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REAL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (* <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind REAL_MUL    = "OP_REAL_MUL";
  /**
   * The operator kind representing the reals division operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REAL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (/ <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind REAL_DIV    = "OP_REAL_DIV";
  /**
   * The operator kind representing the reals less than operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REAL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (< <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind REAL_LT     = "OP_REAL_LT";
  /**
   * The operator kind representing the reals less or equal operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REAL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (<= <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind REAL_LTE    = "OP_REAL_LTE";
  /**
   * The operator kind representing the reals greater than operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REAL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (> <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind REAL_GT     = "OP_REAL_GT";
  /**
   * The operator kind representing the reals greater or equal operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REAL, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (>= <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind REAL_GTE    = "OP_REAL_GTE";
  /**
   * The operator kind representing the reals is integer tester operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (is_int <term>)
   * \endverbatim
   */
  inline static const Kind REAL_IS_INT = "OP_REAL_IS_INT";
  /**
   * The operator kind representing the reals to integer conversion operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (to_real <term>)
   * \endverbatim
   */
  inline static const Kind REAL_TO_INT = "OP_REAL_TO_INT";

  //// Quantifiers
  /**
   * The operator kind representing the a universal quantifier operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_ANY, ..., SORT_BOOL}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (forall ((<binder_1> <sort_1>) ... (<binder_n> <sort_n>)) <body>)
   * \endverbatim
   */
  inline static const Kind FORALL = "OP_FORALL";
  /**
   * The operator kind representing the a existential quantifier operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_ANY, ..., SORT_BOOL}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (exists ((<binder_1> <sort_1>) ... (<binder_n> <sort_n>)) <body>)
   * \endverbatim
   */
  inline static const Kind EXISTS = "OP_EXISTS";

  //// Strings
  /**
   * The operator kind representing the constant denoting the set of all
   * strings.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 0
   * - **args**: `{}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     re.all
   * \endverbatim
   */
  inline static const Kind RE_ALL = "OP_RE_ALL";
  /**
   * The operator kind representing the constant denoting the set of all
   * strings of length 1.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 0
   * - **args**: `{}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     re.allchar
   * \endverbatim
   */
  inline static const Kind RE_ALLCHAR = "OP_RE_ALLCHAR";
  /**
   * The operator kind representing the regular expression complement operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REGLAN}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (re.comp <term>)
   * \endverbatim
   */
  inline static const Kind RE_COMP = "OP_RE_COMP";
  /**
   * The operator kind representing the regular expression concatenation
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REGLAN, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (re.concat <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind RE_CONCAT = "OP_RE_CONCAT";
  /**
   * The operator kind representing the regular expression difference operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REGLAN, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (re.diff <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind RE_DIFF = "OP_RE_DIFF";
  /**
   * The operator kind representing the constant the empty string.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 0
   * - **args**: `{}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     re.none
   * \endverbatim
   */
  inline static const Kind RE_NONE = "OP_RE_NONE";
  /**
   * The operator kind representing the regular expression intersection
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REGLAN, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (re.inter <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind RE_INTER = "OP_RE_INTER";
  /**
   * The operator kind representing the regular expression loop operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REGLAN}`
   * - **indices**: `{uint32_t, uint32_t}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ re.loop n m) <term>)
   * \endverbatim
   */
  inline static const Kind RE_LOOP = "OP_RE_LOOP";
  /**
   * The operator kind representing the regular expression option operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REGLAN}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (re.opt <term>)
   * \endverbatim
   */
  inline static const Kind RE_OPT = "OP_RE_OPT";
  /**
   * The operator kind representing the regular expression Kleene cross
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REGLAN}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (re.+ <term>)
   * \endverbatim
   */
  inline static const Kind RE_PLUS = "OP_RE_PLUS";
  /**
   * The operator kind representing the regular expression power operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REGLAN}`
   * - **indices**: `{uint32_t}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     ((_ re.^ n) <term>)
   * \endverbatim
   */
  inline static const Kind RE_POW = "OP_RE_POW";
  /**
   * The operator kind representing the regular expression range operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (re.range <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind RE_RANGE = "OP_RE_RANGE";
  /**
   * The operator kind representing the regular expression Kleene closure
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REGLAN}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (re.* <term>)
   * \endverbatim
   */
  inline static const Kind RE_STAR = "OP_RE_STAR";
  /**
   * The operator kind representing the regular expression union operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_REGLAN, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (re.union <term_1> ... <term_n>)
   * \endverbatim
   */
  inline static const Kind RE_UNION = "OP_RE_UNION";
  /**
   * The operator kind representing the string at operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_STRING, SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.at <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind STR_AT = "OP_STR_AT";
  /**
   * The operator kind representing the string concatenation operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_STRING, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.at <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind STR_CONCAT = "OP_STR_CONCAT";
  /**
   * The operator kind representing the string contains operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_STRING, SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.contains <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind STR_CONTAINS = "OP_STR_CONTAINS";
  /**
   * The operator kind representing the string from code conversion operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_INT}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.from_code <term>)
   * \endverbatim
   */
  inline static const Kind STR_FROM_CODE = "OP_STR_FROM_CODE";
  /**
   * The operator kind representing the string from integer conversion operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.from_int <term>)
   * \endverbatim
   */
  inline static const Kind STR_FROM_INT = "OP_STR_FROM_INT";
  /**
   * The operator kind representing the string index of operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_STRING, SORT_STRING, SORT_INT}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.indexof <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind STR_INDEXOF = "OP_STR_INDEXOF";
  /**
   * The operator kind representing the string regular expression membership
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_STRING, SORT_REGLAN}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.in_re <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind STR_IN_RE = "OP_STR_IN_RE";
  /**
   * The operator kind representing the string is_digit tester operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.is_digit <term>)
   * \endverbatim
   */
  inline static const Kind STR_IS_DIGIT = "OP_STR_IS_DIGIT";
  /**
   * The operator kind representing the string less or equal operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_STRING, SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.<= <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind STR_LE = "OP_STR_LE";
  /**
   * The operator kind representing the string length operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_STRING}`
   * - **indices**: `{}`
   *
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.len <term>)
   * \endverbatim
   */
  inline static const Kind STR_LEN = "OP_STR_LEN";
  /**
   * The operator kind representing the string less than operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_STRING, SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.< <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind STR_LT = "OP_STR_LT";
  /**
   * The operator kind representing the string prefix of operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_STRING, SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.prefixof <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind STR_PREFIXOF = "OP_STR_PREFIXOF";
  /**
   * The operator kind representing the string replace operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_STRING, SORT_STRING, SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.replace <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind STR_REPLACE = "OP_STR_REPLACE";
  /**
   * The operator kind representing the string replace all operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_STRING, SORT_STRING, SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.replace_all <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind STR_REPLACE_ALL = "OP_STR_REPLACE_ALL";
  /**
   * The operator kind representing the string `replace_re` operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_STRING, SORT_REGLAN, SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.replace_re <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind STR_REPLACE_RE = "OP_STR_REPLACE_RE";
  /**
   * The operator kind representing the string `replace_re_all` operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_STRING, SORT_REGLAN, SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.replace_re_all <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind STR_REPLACE_RE_ALL = "OP_STR_REPLACE_RE_ALL";
  /**
   * The operator kind representing the string substring operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_STRING, SORT_INT, SORT_INT}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.substr <term_1> <term_2> <term_3>)
   * \endverbatim
   */
  inline static const Kind STR_SUBSTR = "OP_STR_SUBSTR";
  /**
   * The operator kind representing the string suffix of operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_STRING, SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.suffixof <term_1> <term_2>)
   * \endverbatim
   */
  inline static const Kind STR_SUFFIXOF = "OP_STR_SUFFIXOF";
  /**
   * The operator kind representing the string to code conversion operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.to_code <term>)
   * \endverbatim
   */
  inline static const Kind STR_TO_CODE = "OP_STR_TO_CODE";
  /**
   * The operator kind representing the string to code integer conversion
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.to_int <term>)
   * \endverbatim
   */
  inline static const Kind STR_TO_INT = "OP_STR_TO_INT";
  /**
   * The operator kind representing the string to regular expression conversion
   * operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_STRING}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (str.to_re <term>)
   * \endverbatim
   */
  inline static const Kind STR_TO_RE = "OP_STR_TO_RE";

  //// Transcendentals
  /**
   * The operator kind representing the transcendentals constant pi.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 0
   * - **args**: `{}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_PI = "OP_TRANS_PI";
  /**
   * The operator kind representing the transcendentals sine operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_SINE = "OP_TRANS_SINE";
  /**
   * The operator kind representing the transcendentals cosine operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_COSINE = "OP_TRANS_COSINE";
  /**
   * The operator kind representing the transcendentals tangent operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_TANGENT = "OP_TRANS_TANGENT";
  /**
   * The operator kind representing the transcendentals cotangent operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_COTANGENT = "OP_TRANS_COTANGENT";
  /**
   * The operator kind representing the transcendentals secant operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_SECANT = "OP_TRANS_SECANT";
  /**
   * The operator kind representing the transcendentals secant operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_COSECANT = "OP_TRANS_COSECANT";
  /**
   * The operator kind representing the transcendentals arcsine operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_ARCSINE = "OP_TRANS_ARCSINE";
  /**
   * The operator kind representing the transcendentals arccosine operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_ARCCOSINE = "OP_TRANS_ARCCOSINE";
  /**
   * The operator kind representing the transcendentals arctangent operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_ARCTANGENT = "OP_TRANS_ARCTANGENT";
  /**
   * The operator kind representing the transcendentals arccosine operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_ARCCOSECANT  = "OP_TRANS_ARCCOSECANT";
  /**
   * The operator kind representing the transcendentals arcsecant operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_ARCSECANT = "OP_TRANS_ARCSECANT";
  /**
   * The operator kind representing the transcendentals arccotangent operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_ARCCOTANGENT = "OP_TRANS_ARCCOTANGENT";
  /**
   * The operator kind representing the transcendentals square root operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_REAL}`
   * - **indices**: `{}`
   */
  inline static const Kind TRANS_SQRT = "OP_TRANS_SQRT";

  //// UF
  /**
   * The operator kind representing the function application operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_FUN, SORT_ANY, ...}`
   * - **indices**: `{}`
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (<fun> <args...>)
   * \endverbatim
   */
  inline static const Kind UF_APPLY = "OP_UF_APPLY";

  /* Operators of non-standardized theories. */
  //// Bags
  /**
   * The operator kind representing the bag union operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BAG, SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_UNION_MAX = "OP_BAG_UNION_MAX";
  /**
   * The operator kind representing the bag disjoint union operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BAG, SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_UNION_DISJOINT = "OP_BAG_UNION_DISJOINT";
  /**
   * The operator kind representing the bag intersection operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BAG, SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_INTERSECTION_MIN = "OP_BAG_INTERSECTION_MIN";
  /**
   * The operator kind representing the bag difference subtract operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BAG, SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_DIFFERENCE_SUBTRACT =
      "OP_BAG_DIFFERENCE_SUBTRACT";
  /**
   * The operator kind representing the bag difference remove operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BAG, SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_DIFFERENCE_REMOVE = "OP_BAG_DIFFERENCE_REMOVE";
  /**
   * The operator kind representing the bag subbag operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BAG, SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_SUBBAG = "OP_BAG_SUBBAG";
  /**
   * The operator kind representing the bag count operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_BAG, SORT_ANY}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_COUNT = "OP_BAG_COUNT";
  /**
   * The operator kind representing the bag duplicate removal operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_DUPLICATE_REMOVAL = "OP_BAG_DUPLICATE_REMOVAL";
  /**
   * The operator kind representing the bag make operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_ANY, SORT_INT}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_MAKE = "OP_BAG_MAKE";
  /**
   * The operator kind representing the empty bag constant.
   *
   * Created with Solver::mk_special_value() with
   * AbsTerm::SPECIAL_VALUE_BAG_EMPTY.
   */
  inline static const Kind BAG_EMPTY = "OP_BAG_EMPTY";
  /**
   * The operator kind representing the bag cardinality operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_CARD = "OP_BAG_CARD";
  /**
   * The operator kind representing the bag choose operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_CHOOSE = "OP_BAG_CHOOSE";
  /**
   * The operator kind representing the bag is singleton tester operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_IS_SINGLETON = "OP_BAG_IS_SINGLETON";
  /**
   * The operator kind representing the bag from set conversion operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_SET}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_FROM_SET = "OP_BAG_FROM_SET";
  /**
   * The operator kind representing the bag to set conversion operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BAG}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_TO_SET = "OP_BAG_TO_SET";
  /**
   * The operator kind representing the bag map operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_BAG, SORT_FUN}`
   * - **indices**: `{}`
   */
  inline static const Kind BAG_MAP = "OP_BAG_MAP";

  //// Sequences
  /**
   * The operator kind representing the sequence concatenation operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_SEQ, ...}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_CONCAT = "OP_SEQ_CONCAT";
  /**
   * The operator kind representing the sequence length operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_SEQ}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_LENGTH = "OP_SEQ_LENGTH";
  /**
   * The operator kind representing the sequence extract operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_SEQ, SORT_INT, SORT_INT}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_EXTRACT = "OP_SEQ_EXTRACT";
  /**
   * The operator kind representing the sequence update operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_SEQ, SORT_INT, SORT_SEQ}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_UPDATE = "OP_SEQ_UPDATE";
  /**
   * The operator kind representing the sequence at operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_SEQ, SORT_INT}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_AT = "OP_SEQ_AT";
  /**
   * The operator kind representing the sequence update operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_SEQ, SORT_SEQ}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_CONTAINS = "OP_SEQ_CONTAINS";
  /**
   * The operator kind representing the sequence index of operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_SEQ, SORT_SEQ, SORT_INT}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_INDEXOF = "OP_SEQ_INDEXOF";
  /**
   * The operator kind representing the sequence replace operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_SEQ, SORT_SEQ, SORT_SEQ}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_REPLACE = "OP_SEQ_REPLACE";
  /**
   * The operator kind representing the sequence replace all operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_SEQ, SORT_SEQ, SORT_SEQ}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_REPLACE_ALL = "OP_SEQ_REPLACE_ALL";
  /**
   * The operator kind representing the sequence reverse operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_SEQ}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_REV = "OP_SEQ_REV";
  /**
   * The operator kind representing the sequence prefix operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_SEQ, SORT_SEQ}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_PREFIX = "OP_SEQ_PREFIX";
  /**
   * The operator kind representing the sequence suffix operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_SEQ, SORT_SEQ}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_SUFFIX = "OP_SEQ_SUFFIX";
  /**
   * The operator kind representing the sequence unit operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_ANY}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_UNIT = "OP_SEQ_UNIT";
  /**
   * The operator kind representing the sequence nth operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_SEQ, SORT_INT}`
   * - **indices**: `{}`
   */
  inline static const Kind SEQ_NTH = "OP_SEQ_NTH";

  //// Sets
  /**
   * The operator kind representing the set cardinality operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_SET}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_CARD = "OP_SET_CARD";
  /**
   * The operator kind representing the set complement operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_SET}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_COMPLEMENT = "OP_SET_COMPLEMENT";
  /**
   * The operator kind representing the set comprehension operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 3
   * - **args**: `{SORT_BOOL, SORT_ANY, SORT_ANY}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_COMPREHENSION = "OP_SET_COMPREHENSION";
  /**
   * The operator kind representing the set choose operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_SET}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_CHOOSE = "OP_SET_CHOOSE";
  /**
   * The operator kind representing the set intersection operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_SET, SORT_SET}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_INTERSECTION  = "OP_SET_INTERSECTION";
  /**
   * The operator kind representing the set insert operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: #MURXLA_MK_TERM_N_ARGS_BIN
   * - **args**: `{SORT_SET, SORT_ANY, ...}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_INSERT = "OP_SET_INSERT";
  /**
   * The operator kind representing the set is singleton tester operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_SET}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_IS_SINGLETON = "OP_SET_IS_SINGLETON";
  /**
   * The operator kind representing the set union operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_SET, SORT_SET}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_UNION = "OP_SET_UNION";
  /**
   * The operator kind representing the set member operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_SET, SORT_ANY}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_MEMBER = "OP_SET_MEMBER";
  /**
   * The operator kind representing the set minus operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_SET, SORT_SET}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_MINUS = "OP_SET_MINUS";
  /**
   * The operator kind representing the set singleton operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 1
   * - **args**: `{SORT_SET}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_SINGLETON = "OP_SET_SINGLETON";
  /**
   * The operator kind representing the set subset operator.
   *
   * Created with Solver::mk_term() with
   * - **arity**: 2
   * - **args**: `{SORT_SET, SORT_SET}`
   * - **indices**: `{}`
   */
  inline static const Kind SET_SUBSET = "OP_SET_SUBSET";

  //// Relations
  /**
   * The operator kind representing the relations join operator.
   * @note  Not yet supported.
   */
  inline static const Kind REL_JOIN = "OP_REL_JOIN";
  /**
   * The operator kind representing the relations join image operator.
   * @note  Not yet supported.
   */
  inline static const Kind REL_JOIN_IMAGE = "OP_REL_JOIN_IMAGE";
  /**
   * The operator kind representing the relations identity operator.
   * @note  Not yet supported.
   */
  inline static const Kind REL_IDEN = "OP_REL_IDEN";
  /**
   * The operator kind representing the relations product operator.
   * @note  Not yet supported.
   */
  inline static const Kind REL_PRODUCT = "OP_REL_PRODUCT";
  /**
   * The operator kind representing the relations transitive closure operator.
   * @note  Not yet supported.
   */
  inline static const Kind REL_TCLOSURE = "OP_REL_TCLOSURE";
  /**
   * The operator kind representing the relations transpose operator.
   * @note  Not yet supported.
   */
  inline static const Kind REL_TRANSPOSE = "OP_REL_TRANSPOSE";

  /** @} */

  /**
   * Constructor.
   *
   * @param id               The unique id of the operator.
   * @param kind             The kind of the operator.
   * @param arity            The arity of the operator. Use
   *                         #MURXLA_MK_TERM_N_ARGS for n-ary operators that
   *                         expect at least one argument, and
   *                         #MURXLA_MK_TERM_N_ARGS_BIN for n-ary operators that
   *                         expect at least two arguments.
   * @param nidxs            The number of indices of the operator.
   * @param sort_kinds       The sort kind of the operator.
   * @param sort_kinds_args  A vector of sorts of the operators' arguments. If
   *                         all or the remaining kinds are the same, it's
   *                         sufficient to only list it once.
   * @param theory           The associated theory.
   */
  Op(uint64_t id,
     const Kind& kind,
     int32_t arity,
     uint32_t nidxs,
     SortKindSet sort_kinds,
     const std::vector<SortKindSet>& sort_kinds_args,
     Theory theory);

  /**
   * Operator overload for equality over operators.
   *
   * @param other  The operator to be compared with this operator.
   * @return  True if both operators are equal.
   */
  bool operator==(const Op& other) const;

  /**
   * Get the argument sort kind at index `i`.
   * @param i  The index of the argument sort kinds vector to query.
   * @return  The sort kind of the operator argument at given index.
   */
  SortKindSet get_arg_sort_kind(size_t i) const;

  /** The operator id, assigned in the order operators have been created. */
  uint64_t d_id = 0u;
  /** The operator kind. */
  const Kind& d_kind = UNDEFINED;
  /**
   * The arity (number of arguments) of this operator kind.
   *
   * Is #MURXLA_MK_TERM_N_ARGS for n-ary operators that expect at least
   * one argument, and #MURXLA_MK_TERM_N_ARGS_BIN for n-ary operators that
   * expect at least two arguments.
   */
  int32_t d_arity;
  /** The number of indices if indexed. */
  uint32_t d_nidxs;
  /**
   * The sort kind of a term of this kind.
   *
   * Will contain more than one sort kind for operators that can be of
   * SORT_ANY, which is expanded via get_all_sort_kinds_for_any() with all sort
   * kinds supported by the solver when operators are added to the
   * OpKindManager via OpKindManager::add_op_kind().
   *
   * May not contain SORT_ANY.
   */
  SortKindSet d_sort_kinds;
  /** The theory to which the operator belongs to. */
  Theory d_theory;

 private:
  /** The sort kind of the term arguments of this kind. */
  std::vector<SortKindSet> d_sort_kinds_args;

};

/* -------------------------------------------------------------------------- */

/** A std::vector of operator kinds. */
using OpKindVector = std::vector<Op::Kind>;
/** A std::unordered_set of operator kinds. */
using OpKindSet    = std::unordered_set<Op::Kind>;
/** A std::unordered_map mapping operator kind to operator. */
using OpKindMap    = std::unordered_map<Op::Kind, Op>;
/**
 * A std::unordered_map mapping sort kind of an operator to operator kinds of
 * that sort kind.
 */
using OpKinds = std::unordered_map<SortKind, OpKindVector>;

/* -------------------------------------------------------------------------- */

/**
 * The operator kinds manager.
 *
 * Maintains the current set of operator kinds, based on enabled theories
 * and unsupported operator kinds.
 */
class OpKindManager
{
 public:
  /**
   * Constructor.
   *
   * @param enabled_theories           The set of enabled theories.
   * @param enabled_sort_kinds         The enabled sort kinds. Maps sort kind
   *                                   to sort kind data.
   * @param disabled_op_kinds          The set of disabled operator kinds.
   * @param unsupported_op_kind_sorts  The unsupported sorts for operator kinds.
   *                                   Maps operator kind to set of unsupported
   *                                   sort kinds.
   * @param arith_linear               True to restrict arithmetic operators to
   *                                   linear fragment.
   * @param stats                      The associated statistics object.
   */
  OpKindManager(const TheorySet& enabled_theories,
                const SortKindMap& enabled_sort_kinds,
                const OpKindSet& disabled_op_kinds,
                const std::unordered_map<Op::Kind, SortKindSet>&
                    unsupported_op_kind_sorts,
                bool arith_linear,
                statistics::Statistics* stats)
      : d_enabled_theories(enabled_theories),
        d_disabled_op_kinds(disabled_op_kinds),
        d_unsupported_op_kind_sorts(unsupported_op_kind_sorts),
        d_arith_linear(arith_linear),
        d_stats(stats),
        d_op_undefined(0u, Op::UNDEFINED, 0, 0, {}, {}, THEORY_ALL)
  {
    for (const auto p : enabled_sort_kinds)
    {
      d_enabled_sort_kinds.insert(p.first);
    }
    add_op_kinds();
  }

  /**
   * Get operator of given kind.
   * Returns a reference to d_op_undefined if the op kind has not been added
   * to the op database.
   */
  Op& get_op(const Op::Kind& kind);

  /**
   * Add operator kind to operator kinds database.
   *
   * @param kind             The kind of the operator.
   * @param arity            The arity of the operator
   * @param nidxs            The number of indices of the operator.
   * @param sort_kind        The sort kind of the operator.
   * @param sort_kind_args   A vector of sorts of the operators' arguments. If
   *                         all or the remaining kinds are the same, it's
   *                         sufficient to only list it once.
   * @param theory           The associated theory.
   */
  void add_op_kind(const Op::Kind& kind,
                   int32_t arity,
                   uint32_t nidxs,
                   SortKind sort_kind,
                   const std::vector<SortKind>& sort_kind_args,
                   Theory theory);

  /**
   * Get a map of enabled operator kinds to their corresponding operator.
   * @return  A map mapping enabled operator kinds to their corresponding Op.
   */
  const OpKindMap& get_op_kinds() { return d_op_kinds; }

 private:
  /**
   * Populate operator kinds database with enabled operator kinds.
   * Operator kinds are enabled based on the set of enabled theories.
   */
  void add_op_kinds();

  /** The set of enabled operator kinds. Maps Op::Kind to Op. */
  OpKindMap d_op_kinds;
  /** The set of enabled theories. */
  TheorySet d_enabled_theories;
  /** Enabled sort kinds. */
  SortKindSet d_enabled_sort_kinds;
  /** The set of disabled operator kinds. */
  OpKindSet d_disabled_op_kinds;
  /** The map of unsupported sorts for operator kinds. */
  std::unordered_map<Op::Kind, SortKindSet> d_unsupported_op_kind_sorts;
  /** True to restrict arithmetic operators to linear fragment. */
  bool d_arith_linear = false;
  /** Statistics. */
  statistics::Statistics* d_stats;
  /**
   * Op representing kinds that are defined but not added as operator kind
   * to d_op_kinds, to be returned via get_op(). This is for operators that
   * are explicitly not added to the op kind database because they should not
   * be randomly picked but only created on demand. Examples are DT_MATCH_CASE
   * and DT_MATCH_BIND_CASE.
   **/
  Op d_op_undefined;
};

/* -------------------------------------------------------------------------- */
}  // namespace murxla

#endif
