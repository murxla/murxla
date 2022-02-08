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

  /** The operator kind representing an undefined kind. */
  inline static const Kind UNDEFINED = "OP_UNDEFINED";
  /** The operator kind representing an internal kind. */
  inline static const Kind INTERNAL = "OP_INTERNAL";

  //// Leaf kinds (only needed for Term::get_kind)
  /** The operator kind representing a first order constant. */
  inline static const Kind CONSTANT = "OP_CONSTANT";
  /** The operator kind representing a const array. */
  inline static const Kind CONST_ARRAY = "OP_CONST_ARRAY";
  /** The operator kind representing a value. */
  inline static const Kind VALUE = "OP_VALUE";
  /** The operator kind representing a variable. */
  inline static const Kind VARIABLE = "OP_VARIABLE";
  /** The operator kind representing a function. */
  inline static const Kind FUN = "OP_FUN";

  //// Special cases
  /**
   * The operator kind representing the distinct operator.
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
   * The operator kind representing the integer is integer tester operator.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (is_int <term>)
   * \endverbatim
   */
  inline static const Kind INT_IS_INT  = "OP_INT_IS_INT";
  /**
   * The operator kind representing the integer to real conversion operator.
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
  /** The operator kind representing the transcendentals constant pi. */
  inline static const Kind TRANS_PI = "OP_TRANS_PI";
  /** The operator kind representing the transcendentals sine operator. */
  inline static const Kind TRANS_SINE = "OP_TRANS_SINE";
  /** The operator kind representing the transcendentals cosine operator. */
  inline static const Kind TRANS_COSINE = "OP_TRANS_COSINE";
  /** The operator kind representing the transcendentals tangent operator. */
  inline static const Kind TRANS_TANGENT = "OP_TRANS_TANGENT";
  /** The operator kind representing the transcendentals cotangent operator. */
  inline static const Kind TRANS_COTANGENT = "OP_TRANS_COTANGENT";
  /** The operator kind representing the transcendentals secant operator. */
  inline static const Kind TRANS_SECANT = "OP_TRANS_SECANT";
  /** The operator kind representing the transcendentals secant operator. */
  inline static const Kind TRANS_COSECANT = "OP_TRANS_COSECANT";
  /** The operator kind representing the transcendentals arcsine operator. */
  inline static const Kind TRANS_ARCSINE = "OP_TRANS_ARCSINE";
  /** The operator kind representing the transcendentals arccosine operator. */
  inline static const Kind TRANS_ARCCOSINE = "OP_TRANS_ARCCOSINE";
  /** The operator kind representing the transcendentals arctangent operator. */
  inline static const Kind TRANS_ARCTANGENT = "OP_TRANS_ARCTANGENT";
  /** The operator kind representing the transcendentals arccosine operator. */
  inline static const Kind TRANS_ARCCOSECANT  = "OP_TRANS_ARCCOSECANT";
  /** The operator kind representing the transcendentals arcsecant operator. */
  inline static const Kind TRANS_ARCSECANT = "OP_TRANS_ARCSECANT";
  /**
   * The operator kind representing the transcendentals arccotangent operator.
   */
  inline static const Kind TRANS_ARCCOTANGENT = "OP_TRANS_ARCCOTANGENT";
  /**
   * The operator kind representing the transcendentals square root operator.
   */
  inline static const Kind TRANS_SQRT = "OP_TRANS_SQRT";

  //// UF
  /**
   * The operator kind representing the function application operator.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (<fun> <args...)
   * \endverbatim
   */
  inline static const Kind UF_APPLY = "OP_UF_APPLY";

  /* Operators of non-standardized theories. */
  //// Bags
  inline static const Kind BAG_UNION_MAX        = "OP_BAG_UNION_MAX";
  inline static const Kind BAG_UNION_DISJOINT   = "OP_BAG_UNION_DISJOINT";
  inline static const Kind BAG_INTERSECTION_MIN = "OP_BAG_INTERSECTION_MIN";
  inline static const Kind BAG_DIFFERENCE_SUBTRACT =
      "OP_BAG_DIFFERENCE_SUBTRACT";
  inline static const Kind BAG_DIFFERENCE_REMOVE = "OP_BAG_DIFFERENCE_REMOVE";
  inline static const Kind BAG_SUBBAG            = "OP_BAG_SUBBAG";
  inline static const Kind BAG_COUNT             = "OP_BAG_COUNT";
  inline static const Kind BAG_DUPLICATE_REMOVAL = "OP_BAG_DUPLICATE_REMOVAL";
  inline static const Kind BAG_MAKE              = "OP_BAG_MAKE";
  inline static const Kind BAG_EMPTY             = "OP_BAG_EMPTY";
  inline static const Kind BAG_CARD              = "OP_BAG_CARD";
  inline static const Kind BAG_CHOOSE            = "OP_BAG_CHOOSE";
  inline static const Kind BAG_IS_SINGLETON      = "OP_BAG_IS_SINGLETON";
  inline static const Kind BAG_FROM_SET          = "OP_BAG_FROM_SET";
  inline static const Kind BAG_TO_SET            = "OP_BAG_TO_SET";
  inline static const Kind BAG_MAP               = "OP_BAG_MAP";
  //// Sequences
  inline static const Kind SEQ_CONCAT      = "OP_SEQ_CONCAT";
  inline static const Kind SEQ_LENGTH      = "OP_SEQ_LENGTH";
  inline static const Kind SEQ_EXTRACT     = "OP_SEQ_EXTRACT";
  inline static const Kind SEQ_UPDATE      = "OP_SEQ_UPDATE";
  inline static const Kind SEQ_AT          = "OP_SEQ_AT";
  inline static const Kind SEQ_CONTAINS    = "OP_SEQ_CONTAINS";
  inline static const Kind SEQ_INDEXOF     = "OP_SEQ_INDEXOF";
  inline static const Kind SEQ_REPLACE     = "OP_SEQ_REPLACE";
  inline static const Kind SEQ_REPLACE_ALL = "OP_SEQ_REPLACE_ALL";
  inline static const Kind SEQ_REV         = "OP_SEQ_REV";
  inline static const Kind SEQ_PREFIX      = "OP_SEQ_PREFIX";
  inline static const Kind SEQ_SUFFIX      = "OP_SEQ_SUFFIX";
  inline static const Kind SEQ_UNIT        = "OP_SEQ_UNIT";
  inline static const Kind SEQ_NTH         = "OP_SEQ_NTH";
  //// Sets
  inline static const Kind SET_CARD          = "OP_SET_CARD";
  inline static const Kind SET_COMPLEMENT    = "OP_SET_COMPLEMENT";
  inline static const Kind SET_COMPREHENSION = "OP_SET_COMPREHENSION";
  inline static const Kind SET_CHOOSE        = "OP_SET_CHOOSE";
  inline static const Kind SET_INTERSECTION  = "OP_SET_INTERSECTION";
  inline static const Kind SET_INSERT        = "OP_SET_INSERT";
  inline static const Kind SET_IS_SINGLETON  = "OP_SET_IS_SINGLETON";
  inline static const Kind SET_UNION         = "OP_SET_UNION";
  inline static const Kind SET_MEMBER        = "OP_SET_MEMBER";
  inline static const Kind SET_MINUS         = "OP_SET_MINUS";
  inline static const Kind SET_SINGLETON     = "OP_SET_SINGLETON";
  inline static const Kind SET_SUBSET        = "OP_SET_SUBSET";
  //// Relations
  inline static const Kind REL_JOIN       = "OP_REL_JOIN";
  inline static const Kind REL_JOIN_IMAGE = "OP_REL_JOIN_IMAGE";
  inline static const Kind REL_IDEN       = "OP_REL_IDEN";
  inline static const Kind REL_PRODUCT    = "OP_REL_PRODUCT";
  inline static const Kind REL_TCLOSURE   = "OP_REL_TCLOSURE";
  inline static const Kind REL_TRANSPOSE  = "OP_REL_TRANSPOSE";

  Op(uint64_t id,
     const Kind& kind,
     int32_t arity,
     uint32_t nidxs,
     SortKindSet sort_kinds,
     const std::vector<SortKindSet>& sort_kinds_args,
     TheoryId theory);

  bool operator==(const Op& other) const;

  SortKindSet get_arg_sort_kind(size_t i) const;

  /** Op id, assigned in the order they have been created. */
  uint64_t d_id = 0u;
  /** The Kind. */
  const Kind& d_kind = UNDEFINED;
  /** The arity of this kind. */
  int32_t d_arity;
  /** The number of parameters if parameterized. */
  uint32_t d_nidxs;
  /** The sort kind of a term of this kind. */
  SortKindSet d_sort_kinds;
  /** The theory to which the operator belongs to. */
  TheoryId d_theory;

 private:
  /** The sort kind of the term arguments of this kind. */
  std::vector<SortKindSet> d_sort_kinds_args;

};

/* -------------------------------------------------------------------------- */

using OpKindVector = std::vector<Op::Kind>;
using OpKindSet    = std::unordered_set<Op::Kind>;
using OpKindMap    = std::unordered_map<Op::Kind, Op>;
using OpKinds = std::unordered_map<SortKind, OpKindVector>;

/* -------------------------------------------------------------------------- */

/**
 * The operator kind manager.
 *
 * Maintains the current set of operator kinds, based on enabled theories
 * and unsupported operator kinds.
 */
class OpKindManager
{
 public:
  /** Constructor. */
  OpKindManager(const TheoryIdSet& enabled_theories,
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
   * kind           : The operator kind
   * arity          : The arity of the operator
   * nparams        : The number of parameters of the operator
   * sort_kind      : The sort kind of the operator
   * sort_kind_args : A vector of sorts of the operators' arguments. if all or
   *                  the remaining kinds are the same, it's sufficient to only
   *                  list it once.
   */
  void add_op_kind(const Op::Kind& kind,
                   int32_t arity,
                   uint32_t nparams,
                   SortKind sort_kind,
                   const std::vector<SortKind>& sort_kind_args,
                   TheoryId theory);

  /** Get a map of enabled operator kinds to their corresponding Op. */
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
  TheoryIdSet d_enabled_theories;
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
   * and DT_MATCH_BIND_CASE. */
  Op d_op_undefined;
};

/* -------------------------------------------------------------------------- */
}  // namespace murxla

#endif
