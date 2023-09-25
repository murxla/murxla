/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__THEORY_H
#define __MURXLA__THEORY_H

#include <iostream>
#include <unordered_set>
#include <vector>

namespace murxla {

enum Theory
{
  /**
   * Theory of
   * <a href="https://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml">
   *   arrays with extensionality
   * </a>
   * as defined in SMT-LIB.
   */
  THEORY_ARRAY,
  /**
   * The not yet standardized theory of bags, mostly based on cvc5's theory
   * definition for bags.
   *
   * A bag (or multiset) @f$m@f$ is a function from the domain @f$D@f$ of its
   * elements to the set of natural numbers
   * (i.e., @f$m : D \longrightarrow \mathbb{N}@f$) where @f$m(e)@f$ represents
   * the multiplicity of element @f$e@f$ in bag @f$m@f$.
   */
  THEORY_BAG,
  /**
   * Theory of
   * <a href="https://smtlib.cs.uiowa.edu/theories-Core.shtml">
   *   Booleans
   * </a>
   * as defined in SMT-LIB as Core theory.
   */
  THEORY_BOOL,
  /**
   * Theory of
   * <a href="https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml">
   *   fixed-size bit-vectors
   * </a>
   * as defined in SMT-LIB.
   *
   * Includes extensions defined in the SMT-LIB logic of
   * <a href="https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV">
   *   quantifier-free bit-vectors (QF_BV)
   * </a>.
   */
  THEORY_BV,
  /**
   * The meta theory of algebraic datatypes.
   *
   * In SMT-LIB, support for algebraic datatypes is part of the language
   * definition rather than a theory definition. We introduce a meta theory for
   * datatypes in order to simplify handling solver-specific support for it
   * (most solvers don't support algebraic datatypes).
   */
  THEORY_DT,
  /**
   * Theory of finite-field arithmetic, as defined in 
   * <a href="https://eprint.iacr.org/2023/091">
   *   this paper
   * </a>.
   */
  THEORY_FF,
  /**
   * Theory of
   * <a href="https://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml">
   *   floating-point arithmetic
   * </a>
   * as defined in SMT-LIB.
   */
  THEORY_FP,
  /**
   * Theory of
   * <a href="https://smtlib.cs.uiowa.edu/theories-Ints.shtml">
   *   Ints
   * </a>
   * as defined in SMT-LIB.
   *
   * Includes extensions defined in the SMT-LIB theory of
   * <a href="https://smtlib.cs.uiowa.edu/theories-Reals_Ints.shtml">
   *   Reals_Ints
   * </a>.
   */
  THEORY_INT,
  /**
   * The meta theory of quantifiers.
   *
   * We only create quantified formulas when this theory is enabled.
   * Introducing quantifiers as a meta theory further simplifies the
   * configuration on solver-specific restrictions specific to quantifiers.
   */
  THEORY_QUANT,
  /**
   * Theory of
   * <a href="https://smtlib.cs.uiowa.edu/theories-Reals.shtml">
   *   Reals
   * </a>
   * as defined in SMT-LIB.
   * Includes extensions defined in the SMT-LIB theory of
   * <a href="https://smtlib.cs.uiowa.edu/theories-Reals_Ints.shtml">
   *   Reals_Ints
   * </a>.
   */
  THEORY_REAL,
  /**
   * The not yet standardized theory of sequences, mostly based on cvc5's
   * theory definition for sequences.
   *
   * A sequence is a finite list of elements that supports common operations
   * such as the extraction of subsequences, the concatenation of sequences,
   * the replacement of subsequences, and matching against regular expressions.
   */
  THEORY_SEQ,
  /**
   * The not yet standardized theory of bags, mostly based on
   * <a
   * href="https://cvc5.github.io/docs/cvc5-0.0.7/theories/sets-and-relations.html">
   *   cvc5's theory definition for bags
   * </a>.
   */
  THEORY_SET,
  /**
   * Theory of
   * <a href="https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml">
   *   strings
   * </a>
   * as defined in SMT-LIB.
   */
  THEORY_STRING,
  /**
   * The not yet standardized theory of transcendentals, mostly based on
   * <a
   * href="https://cvc5.github.io/docs/cvc5-0.0.7/theories/transcendentals.html">
   *   cvc5's theory definition for transcendentals
   * </a>.
   */
  THEORY_TRANSCENDENTAL,
  /**
   * The meta theory of uninterpreted functions.
   *
   * This theory introduces free sort and function symbols.
   * Introducing these as a meta theory simplifies the configuration on
   * solver-specific restrictions specific to uninterpreted sorts and
   * functions.
   */
  THEORY_UF,
  /** The meta theory representing all enabled theories. */
  THEORY_ALL, /* must be last */
};

/** A `std::vector` of theories. */
using TheoryVector = std::vector<Theory>;
/** A `std::unordered_set` of theories. */
using TheorySet = std::unordered_set<Theory>;

/**
 * Serialize a theory to given stream.
 *
 * @param out     The output stream.
 * @param theory  The theory to be serialized.
 * @return     The output stream.
 */
std::ostream& operator<<(std::ostream& out, Theory theory);

}  // namespace murxla
#endif
