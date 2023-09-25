/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__SORT_H
#define __MURXLA__SORT_H

#include <unordered_map>
#include <vector>

#include "theory.hpp"

namespace murxla {

/** The kind of a sort. */
enum SortKind
{
  SORT_ARRAY = 0,  ///< Array sort, parameterized over index and element sort.
  SORT_BAG,        ///< Bag sort, parameterized over element sort.
  SORT_BOOL,       ///< Boolean sort.
  SORT_BV,         ///< Bit-vector sort, parameterized over bit-width.
  SORT_DT,         ///< Datatype sort.
  SORT_FF,         ///< Finite-field sort, parameterized over field size.
  SORT_FP,         ///< Floating-point sort, parameterized over exponent and
                   ///< signifcand size.
  SORT_FUN,        ///< Function sort, parameterized over domain sorts.
  SORT_INT,        ///< Integer sort.
  SORT_REAL,       ///< Real sort.
  SORT_RM,         ///< RoundingMode sort.
  SORT_REGLAN,     ///< Regular language sort.
  SORT_SEQ,        ///< Sequence sort, parameterized over element sort.
  SORT_SET,        ///< Set sort, parameterized over element sort.
  SORT_STRING,     ///< String sort.
  SORT_UNINTERPRETED,  ///< Uninterpreted sort.
  // must be last
  SORT_ANY,  ///< The kind representing any sort kind. Used to
             ///< indicate, for example, that the operands of an
             ///< operator can be of any sort kind.
};

}  // namespace murxla

namespace std {

/** Specialization of `std::hash` for SortKind. */
template <>
struct hash<murxla::SortKind>
{
  /**
   * Operator overload to get the hash value of a sort kind.
   * @param k  The sort kind to compute the hash value for.
   * @return  The hash value of a sort kind.
   */
  size_t operator()(const murxla::SortKind& k) const;
};

}  // namespace std

namespace murxla {

/** Map sort kinds to their string representation. */
static std::unordered_map<SortKind, std::string> sort_kinds_to_str{
    {SORT_ARRAY, "SORT_ARRAY"},
    {SORT_BAG, "SORT_BAG"},
    {SORT_BOOL, "SORT_BOOL"},
    {SORT_BV, "SORT_BV"},
    {SORT_DT, "SORT_DT"},
    {SORT_FF, "SORT_FF"},
    {SORT_FP, "SORT_FP"},
    {SORT_FUN, "SORT_FUN"},
    {SORT_INT, "SORT_INT"},
    {SORT_REAL, "SORT_REAL"},
    {SORT_RM, "SORT_RM"},
    {SORT_SEQ, "SORT_SEQ"},
    {SORT_SET, "SORT_SET"},
    {SORT_REGLAN, "SORT_REGLAN"},
    {SORT_STRING, "SORT_STRING"},
    {SORT_UNINTERPRETED, "SORT_UNINTERPRETED"},
    {SORT_ANY, "SORT_ANY"}};

/**
 * The configuration data for a sort kind.
 * Maintains a sort kind's arity and associated theory.
 */
struct SortKindData
{
  /**
   * Constructor.
   *
   * @param kind    The sort kind.
   * @param arity   The number of sort parameters of this sort kind (not to be
   *                confused with integer paramters like for bit-vector and
   *                floating-point sorts).
   * @param theory  The associated theory.
   */
  SortKindData(SortKind kind = SORT_BOOL,
               int32_t arity = 0,
               Theory theory = THEORY_BOOL)
      : d_kind(kind), d_arity(arity), d_theory(theory)
  {
  }

  /** The sort kind. */
  SortKind d_kind;
  /** The arity of this kind. */
  int32_t d_arity;
  /** The theory of a sort of this kind. */
  Theory d_theory;
};

/** A `std::vector` of sort kinds. */
using SortKindVector = std::vector<SortKind>;
/** A `std::unordered_set` of sort kinds. */
using SortKindSet    = std::unordered_set<SortKind>;
/** A `std::unordered_map` mapping sort kind to its data. */
using SortKindMap    = std::unordered_map<SortKind, SortKindData>;

/**
 * Serialize a SortKind to given stream.
 *
 * @param out   The output stream.
 * @param kind  The sort kind to be serialized.
 * @return      The output stream.
 */
std::ostream& operator<<(std::ostream& out, SortKind kind);

/**
 * A helper to get all sort kinds to be included for SORT ANY. This includes
 * all defined sort kinds excluding the given sorts.
 *
 * @param excluded_sorts  The sorts to exclude from SORT_ANY.
 * @return  The set of sort kinds included for SORT_ANY.
 */
SortKindSet get_all_sort_kinds_for_any(const SortKindSet& excluded_sorts = {});
/**
 * Get the sort kind represented as the given string.
 * This is mainly used for untracing.
 *
 * @param s  The string representation of the sort kind.
 * @return  The sort kind.
 */
SortKind sort_kind_from_str(const std::string& s);

/**
 * Operator overload for equality over sort kinds.
 *
 * @param a  The sort kind to be compared with the other sort kind.
 * @param b  The other sort kind.
 * @return   True if both sort kinds are equal.
 */
bool operator==(const SortKindData& a, const SortKindData& b);

}  // namespace murxla

#endif
