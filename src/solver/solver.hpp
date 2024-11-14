/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__SOLVER_H
#define __MURXLA__SOLVER_H

#include <cassert>
#include <cstddef>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "op.hpp"
#include "rng.hpp"
#include "sort.hpp"

/* -------------------------------------------------------------------------- */

namespace murxla {
class FSM;
class SolverManager;

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

class AbsSort;

/** The Murxla-internal representation of a sort. */
using Sort = std::shared_ptr<AbsSort>;

/**
 * The abstract base class for sorts.
 *
 * A solver wrapper must implement a solver-specific sort wrapper class derived
 * from this class.
 */
class AbsSort
{
 public:
   /**
    * A map representation of the constructors of a datatype sort.
    * Maps constructor names to vectors of selectors, represented as pairs of
    * selector name and selector sort.
    */
  using DatatypeConstructorMap =
      std::unordered_map<std::string,
                         std::vector<std::pair<std::string, Sort>>>;

  /** Destructor. */
  virtual ~AbsSort(){};

  /* To be overriden, for testing the solver.                               */
  /* ---------------------------------------------------------------------- */

  /**
   * \addtogroup sort-must-override
   * @{
   */

  /**
   * Get the hash value of this sort.
   * @return  The hash value of this sort.
   */
  virtual size_t hash() const = 0;
  /**
   * Get the string representation of this sort.
   * @return  A string representation of this sort.
   */
  virtual std::string to_string() const = 0;
  /**
   * Determine if this sort is equal to the given sort.
   * @param other  The sort to compare this sort to.
   * @return  True if this sort is equal to the other sort.
   */
  virtual bool equals(const std::shared_ptr<AbsSort>& other) const = 0;

  /**
   * @}
   * \addtogroup sort-may-override
   * @{
   */

  /**
   * Determine if this sort is not equal to the given sort.
   * @param other  The sort to compare this sort to.
   * @return  True if this sort is not equal to the other sort.
   */
  virtual bool not_equals(const std::shared_ptr<AbsSort>& other) const;

  /**
   * Determine if this sort is an Array sort.
   * @return  True if this sort is an Array sort.
   */
  virtual bool is_array() const { return false; }
  /**
   * Determine if this sort is a Bag sort.
   * @return  True if this sort is a Bag sort.
   */
  virtual bool is_bag() const { return false; }
  /**
   * Determine if this sort is a Boolean sort.
   * @return  True if this sort is a Boolean sort.
   */
  virtual bool is_bool() const { return false; }
  /**
   * Determine if this sort is a bit-vector sort.
   * @return  True if this sort is a bit-vector sort.
   */
  virtual bool is_bv() const { return false; };
  /**
   * Determine if this sort is a datatype sort.
   * @return  True if this sort is a datatype sort.
   */
  virtual bool is_dt() const { return false; }
  /**
   * Determine if this sort is a parametric datatype sort.
   * @return  True if this sort is a parametric datatype sort.
   */
  virtual bool is_dt_parametric() const { return false; }
  /**
   * Determine if this sort is a finite-field sort.
   * @return  True if this sort is a finite-field sort.
   */
  virtual bool is_ff() const { return false; }
  /**
   * Determine if this sort is a floating-point sort.
   * @return  True if this sort is a floating-point sort.
   */
  virtual bool is_fp() const { return false; }
  /**
   * Determine if this sort is a function sort.
   * @return  True if this sort is a function sort.
   */
  virtual bool is_fun() const { return false; }
  /**
   * Determine if this sort is an integer sort.
   * @return  True if this sort is an Int sort.
   */
  virtual bool is_int() const { return false; }
  /**
   * Determine if this sort is a real sort.
   * @return  True if this sort is a Real sort.
   */
  virtual bool is_real() const { return false; }
  /**
   * Determine if this sort is a rounding mode sort.
   * @return  True if this sort is a RoundingMode sort.
   */
  virtual bool is_rm() const { return false; }
  /**
   * Determine if this sort is a regular language sort.
   * @return  True if this sort is a RegLan sort. */
  virtual bool is_reglan() const { return false; }
  /**
   * Determine if this sort is a sequence sort.
   * @return  True if this sort is a Sequence sort.
   */
  virtual bool is_seq() const { return false; }
  /**
   * Determine if this sort is a set sort.
   * @return  True if this sort is a Set sort.
   */
  virtual bool is_set() const { return false; }
  /**
   * Determine if this sort is a string sort.
   * @return  True if this sort is a String sort.
   */
  virtual bool is_string() const { return false; }
  /**
   * Determine if this sort is an uninterpreted sort.
   * @return  True if this sort is an uninterpreted sort.
   */
  virtual bool is_uninterpreted() const { return false; };

  /**
   * Determine if this datatype sort is well founded.
   *
   * We use this to filter out datatype sorts that are not well founded.
   * Default returns always true, must be overriden by solver to actually
   * check if the datatype sort is well founded. If not, this may trigger
   * (properly handled) errors in the solver due to non-well-foundedness.
   *
   * @return  True if this datatype sort is well founded.
   */
  virtual bool is_dt_well_founded() const;

  /**
   * Get the array index sort of this sort.
   * @return  The index sort of this array sort, or a nullptr by default.
   */
  virtual Sort get_array_index_sort() const;
  /**
   * Get the array element sort of this sort.
   * @return  The element sort of this array sort, or a nullptr by default.
   */
  virtual Sort get_array_element_sort() const;
  /**
   * Get the bag element sort of this sort.
   * @return  The element sort of this bag sort, or a nullptr by default.
   */
  virtual Sort get_bag_element_sort() const;
  /**
   * Get the bit-vector size of this sort.
   * @return  The size of this bit-vector sort, or 0 by default.
   */
  virtual uint32_t get_bv_size() const;
  /**
   * Get the datatype name of this sort.
   * @return  The name of this datatype sort, or an empty string by default.
   */
  virtual std::string get_dt_name() const;
  /**
   * Get the number of datatype constructors of this sort.
   * @return  The number of constructors of this datatype sort, or 0 by default.
   */
  virtual uint32_t get_dt_num_cons() const;
  /**
   * Get the datatype constructor names of this sort.
   * @return  A vector with the constructor names of this datatype sort, or an
   *          empty vector by default.
   */
  virtual std::vector<std::string> get_dt_cons_names() const;
  /**
   * Get the number of selectors of the given datatype constructor of this sort.
   * @return  The number of selectors of this datatype sort, or 0 by default.
   */
  virtual uint32_t get_dt_cons_num_sels(const std::string& name) const;
  /**
   * Get the selector names of the given datatype constructor of this sort.
   * @param name  The name of the constructor for which to get the selector
   *              names.
   * @return  A vector with the selector names of the given constructor of this
   *          datatype sort, or an empty vector by default.
   */
  virtual std::vector<std::string> get_dt_cons_sel_names(
      const std::string& name) const;
  /**
   * Get the size of this finite-field sort.
   * @return  The finite-field size of this finite-field sort, or 0 by default.
   */
  virtual std::string get_ff_size() const;
  /**
   * Get the floating-point exponent size of this sort.
   * @return  The exponent size of this floating-point sort, or 0 by default.
   */
  virtual uint32_t get_fp_exp_size() const;
  /**
   * Get the floating-point significand size of this sort.
   * @return The significand size of this floating-point sort, or 0 by default.
   */
  virtual uint32_t get_fp_sig_size() const;
  /**
   * Get the function arity of this sort.
   * @return The arity of this function sort, or 0 by default.
   */
  virtual uint32_t get_fun_arity() const;
  /**
   * Get the function codomain sort of this sort.
   * @return The codomain sort of this function sort, or a nullptr by default.
   */
  virtual Sort get_fun_codomain_sort() const;
  /**
   * Get the function domain sorts of this sort.
   * @return A vector with the domain sorts of this function sort, or an empty
   *         vector by default.
   */
  virtual std::vector<Sort> get_fun_domain_sorts() const;
  /**
   * Get the sequence element sort of this sort.
   * @return The element sort of this sequence sort, or a nullptr by default.
   */
  virtual Sort get_seq_element_sort() const;
  /**
   * Get the set element sort of this sort.
   * @return The element sort of this set sort, or a nullptr by default.
   */
  virtual Sort get_set_element_sort() const;

  /** @} */

  /* Only to be overriden in shadow solver, murxla level.                   */
  /* ---------------------------------------------------------------------- */

  /**
   * Set the kind of this sort.
   * @param sort_kind  The kind of this sort.
   */
  virtual void set_kind(SortKind sort_kind);

  /**
   * Set the sort parameters of this sort.
   *
   * The given vector `sorts` consists of the following sorts, depending on the
   * kind of this sort.
   *
   * - #SORT_ARRAY: A vector of size 2, with index and element sort.
   *
   * - #SORT_BAG:   A vector of size 1, with the element sort.
   *
   * - #SORT_DT (parametric):
   *   - *non-instantiated*: A vector of size n, with sorts of type ParamSort.
   *   - *instantiated*:     A vector of size n, with the sorts this sort is
   *                         instantiated with. May be of type ParamSort or
   *                         UnresolvedSort.
   *
   * - #SORT_FUN:   A vector of size n, with the function domain sorts.
   *
   * - #SORT_SEQ:   A vector of size 1, with the element sort.
   * - #SORT_SET:   A vector of size 1, with the element sort.
   *
   * - UnresolvedSort: A vector of size n, with the sorts this (parametric)
   *                   unresolved sort is to be instantiated with.
   *                   UnresolvedSorts only occur when constructing mutually
   *                   recursive datatype sorts.
   *
   *
   * @param sorts  The sort parameters of this sort.
   */
  virtual void set_sorts(const std::vector<Sort>& sorts);

  /**
   * Set the associated sort.
   *
   * This is for sorts of type ParamSort and UnresolvedSort to add a back
   * reference to the associated sort. For ParamSort, this is the sort this
   * sort has been assigned as a parameter to. For UnresolvedSort, this is the
   * resolved DT sort this unresolved sort stands in for.
   *
   * @note  For solver wrappers, only the associated sort of ParamSort will be
   *        relevant. The associated sort for UnresolvedSort is mainly required
   *        for book keeping on the Murxla level.
   *
   * @param sort  The associated sort.
   */
  virtual void set_associated_sort(Sort sort);

  /**
   * Set the constructor map of this datatype sort.
   *
   * The constructor map maps constructor names to lists of selectors, which
   * are represented as pairs of selector name and sort.
   *
   * @note  This is for book keeping on the Murxla level.
   *
   * @param ctors  The constructor map.
   */
  virtual void set_dt_ctors(const DatatypeConstructorMap& ctors);

  /**
   * Mark this parametric datatype sort as instantiated sort.
   *
   * @note  This is for book keeping on the Murxla level.
   *
   * @param value  True if this datatype sort is an instantiated sort.
   */
  virtual void set_dt_is_instantiated(bool value);

  /* Only to be overriden by ParamSort.                                     */
  /* ---------------------------------------------------------------------- */

  /**
   * Determine if this sort is of type ParamSort.
   * @return True if this sort is of type ParamSort.
   */
  virtual bool is_param_sort() const;

  /* Only to be overriden by UnresolvedSort.                                */
  /* ---------------------------------------------------------------------- */

  /**
   * Determine if this sort is of type UnresolvedSort.
   * @return True if this sort is of type UnresolvedSort.
   */
  virtual bool is_unresolved_sort() const;

  /* NOT to be overriden, murxla level.                                     */
  /* ---------------------------------------------------------------------- */

  /**
   * Set the (unique) id of this sort.
   * @param id  The id of this sort.
   */
  void set_id(uint64_t id);
  /**
   * Get the id of this sort.
   * @return The id of this sort.
   */
  uint64_t get_id() const;

  /**
   * Get the kind of this sort.
   * @return The kind of this sort.
   */
  SortKind get_kind() const;

  /**
   * Get the sort parameters of this sort (see set_sorts()).
   * @return The sort parameters of this sort.
   */
  const std::vector<Sort>& get_sorts() const;

  /**
   * Get the associated sort of this sort (see set_associated_sort()).
   * @return  The associated sort of this sort.
   */
  Sort get_associated_sort() const;

  /**
   * Get the constructor map of this datatype sort (see set_dt_ctors()).
   * @return  The datatype constructor map of this sort.
   */
  DatatypeConstructorMap& get_dt_ctors();
  /**
   * Get the list of constructor names of this sort, as recorded in the
   * datatype constructor map (this does not query the solver!).
   *
   * @return  The list of constructor names of this datatype sort as recorded
   *          on the Murxla level.
   */
  std::vector<std::string> get_dt_ctor_names() const;
  /**
   * Get the list of selector names of the given constructor, as recorded in
   * the datatype constructor map (this does not query the solver!).
   *
   * @param ctor  The constructor to retrieve the selector name list for.
   * @return  The selector names for the given constructor of this datatype
   *          sort.
   */
  std::vector<std::string> get_dt_sel_names(const std::string& ctor) const;
  /**
   * Get the sort of the selector of the given datatype constructor.
   *
   * @param dt_sort  The datatype sort this function is called on.
   * @param ctor  The name of the constructor.
   * @param sel   The name of the selector of the given constructor.
   * @return The sort of the given selector, or `dt_sort` in case of a self
   *         selector.
   *
   * @note  Sort `dt_sort` must be the sort that this function is called on.
   *        We need to pass this for handling the self selector case (where the
   *        selector codomain sort is a nullptr).
   */
  Sort get_dt_sel_sort(Sort dt_sort,
                       const std::string& ctor,
                       const std::string& sel) const;

  /**
   * Instantiate datatype constructor map of this parametric datatype sort
   * with the given vector of sorts.
   *
   * @note  This is only for book keeping on the Murxla level.
   *
   * @param sorts  The sorts to instantiate this parametric datatype with.
   * @return  The datatype constructor map of this sort instantiated with
   *          the given sorts.
   */
  DatatypeConstructorMap instantiate_dt_param_sort(
      const std::vector<Sort>& sorts) const;

  /**
   * Determine if this sort is an instantiated parametric datatype sort.
   * @return True if this is an instantiated parametric datatype sort.
   */
  bool is_dt_instantiated() const;

 protected:
  /** The (unique) id of this sort. */
  uint64_t d_id = 0u;
  /** The kind of this sort. */
  SortKind d_kind = SORT_ANY;
  /**
   * The sort parameters for sorts parameterized over sorts (see set_sorts()).
   * @note  If this is an UnresolvedSort that refers to a parametric datatype,
   *        this contains the set of sort parameters to instantiate the sort
   *        with.
   */
  std::vector<Sort> d_sorts;
  /**
   * The sort this sort is associated with.
   * This is only non-null for ParamSorts and UnresolvedSorts and refers to
   * their associated DT sort.
   */
  Sort d_associated_sort = nullptr;
  /**
   * The datatype constructors of this sort.
   *
   * This is only used for datatype sorts and required for book keeping on
   * the murxla level.
   * Maps constructor names to vectors of selectors, which are represented
   * as pairs of selector name and codomain sort.
   */
  DatatypeConstructorMap d_dt_ctors;
  /** True if this is an instantiated parametric datatype sort. */
  bool d_dt_is_instantiated = false;
};

/**
 * Operator overload for equality over Sorts.
 *
 * @param a  The sort to be compared with the other sort.
 * @param b  The other sort.
 * @return   True if AbsSort::equals() (which queries the solver) is true and
 *           the kinds (murxla::SortKind) of `a` and `b` are equal.
 */
bool operator==(const Sort& a, const Sort& b);
/**
 * Operator overload for disequality over Sorts.
 *
 * @param a  The sort to be compared with the other sort.
 * @param b  The other sort.
 * @return   True if AbsSort::not_equals() (which queries the solver) is true
 *           and the kinds (murxla::SortKind) of `a` and `b` are not equal.
 */
bool operator!=(const Sort& a, const Sort& b);

/**
 * Serialize a Sort to given stream.
 *
 * This represents a sort as 's' + its id and is mainly intended for tracing
 * purposes.  For a representation of a term as provided by the corresponding
 * solver, user AbsSort::to_string() insted.
 *
 * @param out  The output stream.
 * @param s    The sort to be serialized.
 * @return     The output stream.
 */
std::ostream& operator<<(std::ostream& out, const Sort s);
/**
 * Serialize a vector of Sorts to given stream.
 *
 * As above, a sort is represented as `s` + its id, so this will yield a list
 * of space separated `s<id>`s.
 *
 * @param out     The output stream.
 * @param vector  The vector of sorts to be serialized.
 * @return        The output stream.
 */
std::ostream& operator<<(std::ostream& out, const std::vector<Sort>& vector);

/**
 * Parameter sort.
 *
 * A parameter sort is a sort place holder representing a sort parameter for
 * parametric datatype sorts. Parameter sorts are *only* to be used for
 * parametric datatypes.
 *
 * ParamSort is explicitly not a wrapper around a solver sort type, but a
 * dedicated type that requires special handling in the solver wrapper.
 *
 * A back reference to the associated datatype sort is stored in
 * `d_associated_sort` and can be accessed via get_associated_sort().
 *
 * @note  Instances of ParamSort may never be added to the solver manager's
 *        sort database. No terms of ParamSort may ever be created.
 */
class ParamSort : public AbsSort
{
 public:
  /** Constructor. */
  ParamSort(const std::string& symbol) : d_symbol(symbol) {}

  size_t hash() const override;
  std::string to_string() const override;
  bool equals(const Sort& other) const override;
  bool is_array() const override { return false; }
  bool is_bag() const override { return false; }
  bool is_bool() const override { return false; }
  bool is_bv() const override { return false; }
  bool is_dt() const override { return false; }
  bool is_dt_parametric() const override { return false; }
  bool is_ff() const override { return false; }
  bool is_fp() const override { return false; }
  bool is_fun() const override { return false; }
  bool is_int() const override { return false; }
  bool is_real() const override { return false; }
  bool is_rm() const override { return false; }
  bool is_reglan() const override { return false; }
  bool is_seq() const override { return false; }
  bool is_set() const override { return false; }
  bool is_string() const override { return false; }

  bool is_param_sort() const override { return true; }

  /**
   * Get the symbol of this parameter sort.
   * @return The symbol.
   */
  const std::string& get_symbol() const { return d_symbol; }

 private:
  /** The symbol of this parameter sort. */
  std::string d_symbol;
};

/**
 * Unresolved sort.
 *
 * An unresolved sort is a sort place holder for yet unresolved datatype sorts
 * when constructing mutually recursive datatype sorts. Unresolved sorts are
 * *only* to be used for mutually recursive datatypes.
 *
 * UnresolvedSort is explicitly not a wrapper around a solver sort type, but a
 * dedicated type that requires special handling in the solver wrapper.
 *
 * A back reference to the associated datatype sort is stored in
 * `d_associated_sort` and can be accessed via get_associated_sort().
 *
 * @note  Instances of UnresolvedSort may never be added to the solver manager's
 *        sort database. No terms of UnresolvedSort may ever be created.
 */
class UnresolvedSort : public AbsSort
{
 public:
  /** Constructor. */
  UnresolvedSort(const std::string& symbol) : d_symbol(symbol) {}

  size_t hash() const override;
  std::string to_string() const override;
  bool equals(const Sort& other) const override;
  bool is_array() const override { return false; }
  bool is_bag() const override { return false; }
  bool is_bool() const override { return false; }
  bool is_bv() const override { return false; }
  bool is_dt() const override { return false; }
  bool is_dt_parametric() const override { return false; }
  bool is_ff() const override { return false; }
  bool is_fp() const override { return false; }
  bool is_fun() const override { return false; }
  bool is_int() const override { return false; }
  bool is_real() const override { return false; }
  bool is_rm() const override { return false; }
  bool is_reglan() const override { return false; }
  bool is_seq() const override { return false; }
  bool is_set() const override { return false; }
  bool is_string() const override { return false; }

  bool is_unresolved_sort() const override { return true; }

  /**
   * Get the symbol of this unresolved sort.
   * @return The symbol.
   */
  const std::string& get_symbol() const { return d_symbol; }

 private:
  /** The symbol of this unresolved sort. */
  std::string d_symbol;
};

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

/**
 * The abstract base class for terms.
 *
 * A solver wrapper must implement a solver-specific term wrapper class derived
 * from this class.
 */
class AbsTerm
{
 public:
  /**
   * The kind of a special value (see Solver::mk_special_value()).
   *
   * @note  This is an std::string rather than an enum to allow for solvers
   *        to extend the set of special value kinds.
   */
  using SpecialValueKind = std::string;

  /**
   * \addtogroup special-value-kinds
   * @{
   */

  /** The kind of a term that is not a special value. */
  inline static const SpecialValueKind SPECIAL_VALUE_NONE =
      "not-a-special-value";
  // Special Bag values
  /** The kind of a term representing the empty bag. */
  inline static const SpecialValueKind SPECIAL_VALUE_BAG_EMPTY = "bag.empty";
  // Special BV values
  /** The kind of a term representing a bit-vector zero value. */
  inline static const SpecialValueKind SPECIAL_VALUE_BV_ZERO = "bv.zero";
  /** The kind of a term representing a bit-vector one value. */
  inline static const SpecialValueKind SPECIAL_VALUE_BV_ONE  = "bv.one";
  /** The kind of a term representing a bit-vector ones value (all bits 1). */
  inline static const SpecialValueKind SPECIAL_VALUE_BV_ONES = "bv.ones";
  /** The kind of a term representing a bit-vector minimum signed value. */
  inline static const SpecialValueKind SPECIAL_VALUE_BV_MIN_SIGNED =
      "bv-min-signed";
  /** The kind of a term representing a bit-vector maximum signed value. */
  inline static const SpecialValueKind SPECIAL_VALUE_BV_MAX_SIGNED =
      "bv-max-signed";
  // Special FF values
  /** The kind of a term representing a finite-field zero value. */
  inline static const SpecialValueKind SPECIAL_VALUE_FF_ZERO     = "ff.zero";
  /** The kind of a term representing a finite-field zero value. */
  inline static const SpecialValueKind SPECIAL_VALUE_FF_ONE      = "ff.one";
  /** The kind of a term representing a finite-field zero value. */
  inline static const SpecialValueKind SPECIAL_VALUE_FF_NEG_ONE  = "ff.negone";
  // Special FP values
  /** The kind of a term representing a floating-point not a number value. */
  inline static const SpecialValueKind SPECIAL_VALUE_FP_NAN      = "nan";
  /**
   * The kind of a term representing a floating-point positive infinity value.
   */
  inline static const SpecialValueKind SPECIAL_VALUE_FP_POS_INF  = "+oo";
  /**
   * The kind of a term representing a floating-point negative infinity value.
   */
  inline static const SpecialValueKind SPECIAL_VALUE_FP_NEG_INF  = "-oo";
  /** The kind of a term representing a floating-point positive zero value. */
  inline static const SpecialValueKind SPECIAL_VALUE_FP_POS_ZERO = "+zero";
  /** The kind of a term representing a floating-point negative zero value. */
  inline static const SpecialValueKind SPECIAL_VALUE_FP_NEG_ZERO = "-zero";
  // Special RM values
  /**
   * The kind of a term representing a rounding mode round nearest ties to
   * away value.
   */
  inline static const SpecialValueKind SPECIAL_VALUE_RM_RNA = "rna";
  /**
   * The kind of a term representing a rounding mode round nearest ties to
   * even value.
   */
  inline static const SpecialValueKind SPECIAL_VALUE_RM_RNE = "rne";
  /**
   * The kind of a term representing a rounding mode round toward negative
   * value.
   */
  inline static const SpecialValueKind SPECIAL_VALUE_RM_RTN = "rtn";
  /**
   * The kind of a term representing a rounding mode round toward positive
   * value.
   */
  inline static const SpecialValueKind SPECIAL_VALUE_RM_RTP = "rtp";
  /**
   * The kind of a term representing a rounding mode round toward zero value.
   */
  inline static const SpecialValueKind SPECIAL_VALUE_RM_RTZ = "rtz";
  // Special Sequence values
  /** The kind of a term representing the empty sequence. */
  inline static const SpecialValueKind SPECIAL_VALUE_SEQ_EMPTY = "seq.empty";
  // Special Sets values
  /** The kind of a term representing the empty set. */
  inline static const SpecialValueKind SPECIAL_VALUE_SET_EMPTY = "set.empty";
  /** The kind of a term representing the universe set. */
  inline static const SpecialValueKind SPECIAL_VALUE_SET_UNIVERSE =
      "set.universe";

  /** @} */

  /** The leaf kind of a term. */
  enum LeafKind
  {
    NONE,
    CONSTANT,
    VALUE,
    VARIABLE,
  };

  /** Constructor. */
  AbsTerm(){};
  /** Destructor. */
  virtual ~AbsTerm(){};

  /* To be overriden, for testing the solver.                               */
  /* ---------------------------------------------------------------------- */

  /**
   * \addtogroup term-must-override
   * @{
   */

  /**
   * Get the hash value of this term.
   * @return  The hash value of this term.
   */
  virtual size_t hash() const = 0;
  /**
   * Get a string representation of this term.
   * @return  A string representation of this term.
   */
  virtual std::string to_string() const = 0;
  /**
   * Determine if this term is equal to the given term.
   * @param other  The term to compare this term to.
   * @return  True if this term is equal to the other term.
   */
  virtual bool equals(const std::shared_ptr<AbsTerm>& other) const = 0;

  /**
   * @}
   * \addtogroup term-may-override
   * @{
   */

  /**
   * Determine if this term is not equal to the given term.
   * @param other  The term to compare this term to.
   * @return  True if this term is not equal to the other term.
   */
  virtual bool not_equals(const std::shared_ptr<AbsTerm>& other) const;

  /**
   * Determine if this term is an Array term.
   * @return True if this term is an Array term.
   */
  virtual bool is_array() const;
  /**
   * Determine if this term is a Bag term.
   * @return True if this term is a Bag term.
   */
  virtual bool is_bag() const;
  /**
   * Determine if this term is a Boolean term.
   * @return True if this term is a Boolean term.
   */
  virtual bool is_bool() const;
  /**
   * Determine if this term is a bit-vector term.
   * @return True if this term is a bit-vector term.
   */
  virtual bool is_bv() const;
  /**
   * Determine if this term is a datatype term.
   * @return True if this term is a datatype term.
   */
  virtual bool is_dt() const;
  /**
   * Determine if this term is a finite-field term.
   * @return True if this term is a finite-field term.
   */
  virtual bool is_ff() const;
  /**
   * Determine if this term is a floating-point term.
   * @return True if this term is a floating-point term.
   */
  virtual bool is_fp() const;
  /**
   * Determine if this term is a function term.
   * @return True if this term is a function term.
   */
  virtual bool is_fun() const;
  /**
   * Determine if this term is an Int term.
   * @return True if this term is an Int term.
   */
  virtual bool is_int() const;
  /**
   * Determine if this term is a Real term.
   * @return True if this term is a Real term.
   */
  virtual bool is_real() const;
  /**
   * Determine if this term is a RoundingMode term.
   * @return True if this term is a RoundingMode term.
   */
  virtual bool is_rm() const;
  /**
   * Determine if this term is a RegLan term.
   * @return True if this term is a RegLan term.
   */
  virtual bool is_reglan() const;
  /**
   * Determine if this term is a Sequence term.
   * @return True if this term is a Sequence term.
   */
  virtual bool is_seq() const;
  /**
   * Determine if this term is a Set term.
   * @return True if this term is a Set term.
   */
  virtual bool is_set() const;
  /**
   * Determine if this term is a String term.
   * @return True if this term is a String term.
   */
  virtual bool is_string() const;
  /**
   * Determine if this term is an uninterpreted term.
   * @return True if this term is an uninterpreted term.
   */
  virtual bool is_uninterpreted() const;

  /**
   * Determine if this term is a Bag value.
   * @return True if this term is a Bag value.
   */
  virtual bool is_bag_value() const;
  /**
   * Determine if this term is a Boolean value.
   * @return True if this term is a Boolean value.
   */
  virtual bool is_bool_value() const;
  /**
   * Determine if this term is a bit-vector value.
   * @return True if this term is a bit-vector value.
   */
  virtual bool is_bv_value() const;
  /**
   * Determine if this term is a datatype value.
   * @return True if this term is a datatype value.
   */
  virtual bool is_dt_value() const;
  /**
   * Determine if this term is a finite-field value.
   * @return True if this term is a finite-field value.
   */
  virtual bool is_ff_value() const;
  /**
   * Determine if this term is a floating-point value.
   * @return True if this term is a floating-point value.
   */
  virtual bool is_fp_value() const;
  /**
   * Determine if this term is an integer value.
   * @return True if this term is an integer value.
   */
  virtual bool is_int_value() const;
  /**
   * Determine if this term is a real value.
   * @return True if this term is a real value.
   */
  virtual bool is_real_value() const;
  /**
   * Determine if this term is a RegLan value.
   * @return True if this term is a RegLan value.
   */
  virtual bool is_reglan_value() const;
  /**
   * Determine if this term is a rounding mode value.
   * @return True if this term is a rounding mode value.
   */
  virtual bool is_rm_value() const;
  /**
   * Determine if this term is a Sequence value.
   * @return True if this term is a Sequence value.
   */
  virtual bool is_seq_value() const;
  /**
   * Determine if this term is a Sequence value.
   * @return True if this term is a Sequence value.
   */
  virtual bool is_set_value() const;
  /**
   * Determine if this term is a string value.
   * @return True if this term is a string value.
   */
  virtual bool is_string_value() const;

  /**
   * Determine if this term is a special value of given kind.
   * @return True if this term is a special value of given kind.
   */
  virtual bool is_special_value(const SpecialValueKind& kind) const;

  /**
   * Determine if this term is a first-order constant.
   * @return True if this term is a first-order constant.
   */
  virtual bool is_const() const;
  /**
   * Determine if this term is a value.
   * @return True if this term is a value.
   */
  virtual bool is_value() const;
  /**
   * Determine if this term is a variable.
   * @return True if this term is a variable.
   */
  virtual bool is_var() const;

  /**
   * Get the kind of this term.
   *
   * This kind is not a kind we cache on creation, but the kind that the
   * solver reports. May be Op::UNDEFINED.
   *
   * Must be overriden and may not return Op::UNDEFINED if the solver supports
   * the theory of bags, sets and sequences (required for properly initializing
   * sorts that are implicitly created, e.g., sequence sorts for Op::SEQ_UNIT).
   *
   * @return The kind of this term.
   */
  virtual const Op::Kind& get_kind() const;

  /**
   * Get the children of this term.
   *
   * @note  As with Solver::mk_term, the returned terms are "raw" Terms, in the
   *        sense that they are only wrapped into a Term, with no additional
   *        book keeping information (all data members have default values).
   *
   * @return The children of this term.
   */
  virtual std::vector<std::shared_ptr<AbsTerm>> get_children() const;

  /**
   * Determine if this term is of an indexed operator kind.
   * @return True if this term is of an indexed operator kind.
   */
  virtual bool is_indexed() const;
  /**
   * Get the number of indices of a term with an indexed operator kind.
   * @return  The number of indices.
   */
  virtual size_t get_num_indices() const;
  /**
   * Get the indices of a term with an indexed operator kind.
   * @return The indinces of a term with an indexed operator kind.
   */
  virtual std::vector<std::string> get_indices() const;

  /**
   * Get the bit width of this term.
   * Asserts that it is a bit-vector term.
   * @return  The size of this bit-vector term.
   */
  virtual uint32_t get_bv_size() const;
  /**
   * Get the size of this finite-field term's field.
   * @return  The finite-field size of this finite-field term, or 0 by default.
   */
  virtual std::string get_ff_size() const;
  /**
   * Get the exponent bit width of this term.
   * Asserts that it is a floating-point term.
   * @return  The size of the exponent of this floating-point term.
   */
  virtual uint32_t get_fp_exp_size() const;
  /**
   * Get the significand bit width of this term.
   * Asserts that it is a floating-point term.
   * @return  The size of the signifcand of this floating-point term.
   */
  virtual uint32_t get_fp_sig_size() const;
  /**
   * Get the array index sort of this term.
   * Asserts that it is an array term.
   * @return  The index sort of this array term.
   */
  virtual Sort get_array_index_sort() const;
  /**
   * Get the array element sort of this term.
   * Asserts that it is an array term.
   * @return  The element sort of this array term.
   */
  virtual Sort get_array_element_sort() const;
  /**
   * Get the function arity of this term.
   * Asserts that it is an function term.
   * @return  The arity of this function term.
   */
  virtual uint32_t get_fun_arity() const;
  /**
   * Get the function codomain sort of this term.
   * Asserts that it is an function term.
   * @return  The codomain sort of this function term.
   */
  virtual Sort get_fun_codomain_sort() const;
  /**
   * Get the function domain sorts of this term.
   * Asserts that it is an function term.
   * @return  The domain sorts of this function term.
   */
  virtual std::vector<Sort> get_fun_domain_sorts() const;

  /** @} */

  /* Only to be overriden in shadow solver, murxla level.                   */
  /* ---------------------------------------------------------------------- */

  /**
   * Set the sort of this term.
   *
   * This is not to be overriden by any solver implementations except the
   * shadow solver.
   *
   * @param sort  The sort to be set.
   */
  virtual void set_sort(Sort sort);
  /**
   * Set leaf kind.
   *
   * Set to LeafKind::NONE if this term is not a leaf.
   *
   * @note  This is not to be overriden by any solver implementations except the
   *        shadow solver.
   *
   * @param kind  The leaf kind.
   */
  virtual void set_leaf_kind(LeafKind kind);
  /**
   * Set special value kind.
   *
   * Set to SPECIAL_VALUE_NONE if not a value or no special value.
   *
   * @note  This is not to be overriden by any solver implementations except the
   *        shadow solver.
   *
   * @param value_kind  The kind of the special value.
   */
  virtual void set_special_value_kind(const SpecialValueKind& value_kind);

  /* NOT to be overriden, murxla level.                                     */
  /* ---------------------------------------------------------------------- */

  /**
   * Set the id of this term.
   * @param id  The id to be set.
   */
  void set_id(uint64_t id);
  /**
   * Get the id of this term.
   * @return  The id of this term.
   */
  uint64_t get_id() const;

  /**
   * Get the sort of this term.
   * @return  The sort of this term.
   */
  Sort get_sort() const;

  /**
   * Get the leaf kind of this term.
   *
   * Kind is LeafKind::NONE if this term is not a leaf.
   *
   * @note  This is for Murxla level maintenance and not to be overriden with
   *        solver-specific implementations.
   *
   * @return  The leaf kind of this term.
   */
  LeafKind get_leaf_kind() const;

 protected:
  /** The id of this term. */
  uint64_t d_id = 0u;
  /** The sort of this term. */
  Sort d_sort = nullptr;

 private:
  /**
   * The leaf kind of this term.
   * LeafKind::NONE if this is not a leaf term.
   */
  LeafKind d_leaf_kind = LeafKind::NONE;
  /**
   * The special value kind of this term..
   * SPECIAL_VALUE_NONE if this term is not a value or no special value.
   */
  SpecialValueKind d_value_kind = SPECIAL_VALUE_NONE;
};

/** The Murxla-internal representation of a term. */
using Term = std::shared_ptr<AbsTerm>;

/**
 * Operator overload for equality over Terms.
 *
 * @param a  The term to be compared with the other term.
 * @param b  The other term.
 * @return   True if AbsTerm::equals() (which queries the solver) is true
 *           and the sorts of `a` and `b` are equal.
 */
bool operator==(const Term& a, const Term& b);
/**
 * @param a  The term to be compared with the other term.
 * @param b  The other term.
 * Operator overload for disequality over Terms.
 *
 * @return   True if AbsTerm::not_equals() (which queries the solver) is true
 *           and the sorts of `a` and `b` are not equal.
 */
bool operator!=(const Term& a, const Term& b);

/**
 * Serialize a Term to given stream.
 *
 * This represents a term as 't' + its id and is mainly intended for tracing
 * purposes.  For a representation of a term as provided by the corresponding
 * solver, use AbsTerm::to_string() instead.
 *
 * @param out  The output stream.
 * @param t    The term to be serialized.
 * @return     The output stream.
 */
std::ostream& operator<<(std::ostream& out, const Term t);
/**
 * Serialize a vector of Terms to given stream.
 *
 * As above, a term is represented as `t` + its id, so this will yield a list
 * of space separated `t<id>`s.
 *
 * @param out     The output stream.
 * @param vector  The vector of terms to be serialized.
 * @return        The output stream.
 */
std::ostream& operator<<(std::ostream& out, const std::vector<Term>& vector);

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

/**
 * The abstract base class for the solver implementation.
 *
 * A solver wrapper must implement a solver-specific solver wrapper class
 * derived from this class.
 */
class Solver
{
 public:
  /** Map operator kind to a set of sort kinds. */
  using OpKindSortKindMap = std::unordered_map<Op::Kind, SortKindSet>;

  /** The result of a satisfiability check. */
  enum Result
  {
    UNKNOWN,
    SAT,
    UNSAT,
  };

  /** The numerical base of a string representing a number. */
  enum Base
  {
    BIN = 2,    ///< binary
    DEC = 10,   ///< decimal
    HEX = 16,   ///< hexa-decimal
  };

  /**
   * Constructor.
   * @param sng  The associated solver seed generator.
   */
  Solver(SolverSeedGenerator& sng);
  /** Default constructor is deleted. */
  Solver()          = delete;
  /** Default destructor is deleted. */
  virtual ~Solver() = default;

  /* To be overriden, for testing the solver.                               */
  /* ---------------------------------------------------------------------- */

  /**
   * \addtogroup solver-must-override
   * @{
   */

  /** Create and initialize wrapped solver. */
  virtual void new_solver() = 0;
  /** Delete wrapped solver. */
  virtual void delete_solver() = 0;
  /**
   * Determine if the wrapped solver is initialized.
   * @return True if wrapped solver is initialized.
   */
  virtual bool is_initialized() const = 0;
  /**
   * Get the name of the wrapped solver.
   * @return  The solver name.
   */
  virtual const std::string get_name() const = 0;

  /**
   * Create variable.
   *
   * @param sort  The sort of the variable.
   * @param name  The name of the variable.
   * @return  The variable.
   */
  virtual Term mk_var(Sort sort, const std::string& name)   = 0;

  /**
   * Create first order constant.
   *
   * @param sort  The sort of the constant.
   * @param name  The name of the constant.
   * @return  The constant.
   */
  virtual Term mk_const(Sort sort, const std::string& name) = 0;

  /**
   * Create function.
   *
   * @param name  The name of the function.
   * @param args  The function arguments.
   * @param body  The function body.
   * @return  The function.
   */
  virtual Term mk_fun(const std::string& name,
                      const std::vector<Term>& args,
                      Term body) = 0;

  /**
   * Create sort with no additional arguments.
   *
   * Examples are sorts of kind #SORT_BOOL, #SORT_INT, #SORT_REAL, #SORT_RM,
   * #SORT_REGLAN, and #SORT_STRING.
   *
   * @param kind  The kind of the sort.
   * @return  The created sort.
   */
  virtual Sort mk_sort(SortKind kind) = 0;

  /**
   * Create sort with given sort arguments.
   *
   * The sort arguments are given as:
   *
   * - #SORT_ARRAY: `{<index sort>, <element sort>}`
   *
   * - #SORT_BAG: `{<element sort>}`
   *
   * - #SORT_FUN: `{<domain sort_1>, ..., <domain sort_n>, <codomain sort>}`
   *
   * - #SORT_SET: `{<element sort>}`
   *
   * - #SORT_SEQ: `{<element sort>}`
   *
   * @param kind  The kind of the sort.
   * @param sorts  The sort arguments.
   * @return  The created sort.
   */
  virtual Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) = 0;

  /**
   * Create term with given term arguments and indices.
   *
   * @param kind  The kind of the term (Op::Kind).
   * @param args  The argument terms.
   * @param indices  The index arguments.
   * @return  The created term.
   */
  virtual Term mk_term(const Op::Kind& kind,
                       const std::vector<Term>& args,
                       const std::vector<uint32_t>& indices) = 0;

  /**
   * Create term with given string and term arguments.
   *
   * This is mainly intended for Op::DT_APPLY_SEL, Op::DT_APPLY_TESTER and
   * Op::DT_APPLY_UPDATER.
   *
   * The string arguments identify constructors and selectors by name and
   * are given for the following kinds as follows:
   * - Op::DT_APPLY_SEL: `{<constructor name>, <selector name>}`
   * - Op::DT_APPLY_TESTER: `{<constructor name>}`
   * - Op::DT_APPLY_UPDATER: `{<constructor name>, <selector name>}`
   *
   * @param kind  The kind of the term (Op::Kind).
   * @param str_args  The names of constructors/selectors as indicated above.
   * @param args  The argument terms.
   */
  virtual Term mk_term(const Op::Kind& kind,
                       const std::vector<std::string>& str_args,
                       const std::vector<Term>& args);
  /**
   * Create term with given Sort, string and term arguments.
   *
   * This is mainly intended for Op::DT_APPLY_CONS, Op::DT_MATCH_BIND_CASE and
   * Op::DT_MATCH_CASE.
   *
   * The string arguments identify constructors and selectors by name and
   * are given for the following kinds as follows:
   * - Op::DT_APPLY_CONS: `{<constructor name>}`
   * - Op::DT_MATCH_BIND_CASE: `{<constructor name>}`
   * - Op::DT_MATCH_CASE: `{<constructor name>}`
   *
   * @param kind  The kind of the term (Op::Kind).
   * @param sort  The datatype sort to apply the given kind on.
   * @param str_args  The names of constructors/selectors as indicated above.
   * @param args  The argument terms.
   */
  virtual Term mk_term(const Op::Kind& kind,
                       Sort sort,
                       const std::vector<std::string>& str_args,
                       const std::vector<Term>& args);

  /**
   * Get a freshly wrapped solver sort of the given term.
   *
   * This is used for querying the sort of a freshly created term while
   * delegating sort inference to the solver. The returned sort will have
   * sort kind #SORT_ANY and id 0 (will be assigned in the FSM, before adding
   * the sort to the sort database). Given sort kind is typically unused, but
   * needed by the Smt2Solver.
   *
   * @param term       The term to query for its sort.
   * @param sort_kind  The kind of the term's sort.
   * @return  The sort of the given term.
   */
  virtual Sort get_sort(Term term, SortKind sort_kind) = 0;

  /**
   * Get the string representation that identifies the solver configuration
   * option for enabling/disabling incremental solving.
   *
   * @return  Return the string representation of the solver option for
   *          enabling/disabling incremental solving.
   */
  virtual std::string get_option_name_incremental() const = 0;
  /**
   * Get the string representation that identifies the solver configuration
   * option for enabling/disabling model production.
   *
   * @return  Return the string representation of the solver option for
   *          enabling/disabling model production.
   */
  virtual std::string get_option_name_model_gen() const = 0;
  /**
   * Get the string representation that identifies the solver configuration
   * option for enabling/disabling unsat assumptions production.
   *
   * @return  Return the string representation of the solver option for
   *          enabling/disabling unsat assumption production.
   */
  virtual std::string get_option_name_unsat_assumptions() const = 0;
  /**
   * Get the string representation that identifies the solver configuration
   * option for enabling/disabling unsat cores production.
   *
   * @return  Return the string representation of the solver option for
   *          enabling/disabling unsat core production.
   */
  virtual std::string get_option_name_unsat_cores() const = 0;

  /**
   * Determine if incremental solving is currently enabled.
   * @return  True if incremental solving is currently enabled.
   */
  virtual bool option_incremental_enabled() const = 0;
  /**
   * Determine if model production is currently enabled.
   * @return  True if model production is currently enabled.
   */
  virtual bool option_model_gen_enabled() const = 0;
  /**
   * Determine if unsat assumptions production is currently enabled.
   * @return  True if unsat assumptions production is currently enabled.
   */
  virtual bool option_unsat_assumptions_enabled() const = 0;
  /**
   * Determine if unsat cores production is currently enabled.
   * @return  True if unsat cores production is currently enabled.
   */
  virtual bool option_unsat_cores_enabled() const = 0;

  /**
   * Determine if given term is an unsat assumption.
   * @return  True if given term is an unsat assumption.
   */
  virtual bool is_unsat_assumption(const Term& t) const = 0;

  /**
   * Assert given formula.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (assert <term>)
   * \endverbatim
   *
   * @param t  The formula to assert.
   */
  virtual void assert_formula(const Term& t) = 0;

  /**
   * Check satisfiability of currently asserted formulas.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (check-sat)
   * \endverbatim
   * @return  The satisfiability Result.
   */
  virtual Result check_sat() = 0;
  /**
   * Check satisfiability of currently asserted formulas under the given set of
   * assumptions.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (check-sat-assuming)
   * \endverbatim
   *
   * @param assumptions  The set of assumptions.
   * @return  The satisfiability Result.
   */
  virtual Result check_sat_assuming(const std::vector<Term>& assumptions) = 0;

  /**
   * Get the current set of unsat assumptions.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (get-unsat-assumptions)
   * \endverbatim
   *
   * @return  The current set of unsat assumptions. */
  virtual std::vector<Term> get_unsat_assumptions() = 0;

  /**
   * Push the given number of assertion levels.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (push <n>)
   * \endverbatim
   *
   * @param n_levels  The number of assertion levels to push.
   */
  virtual void push(uint32_t n_levels) = 0;

  /**
   * Pop the given number of assertion levels.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (pop <n>)
   * \endverbatim
   *
   * @param n_levels  The number of assertion levels to pop.
   */
  virtual void pop(uint32_t n_levels)  = 0;

  /**
   * Print model after a sat check-sat call.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (get-unsat-core)
   * \endverbatim
   */
  virtual void print_model() = 0;

  /**
   * Reset solver.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (reset)
   * \endverbatim
   */
  virtual void reset() = 0;

  /**
   * Reset assertion stack.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (reset-assertions)
   * \endverbatim
   */
  virtual void reset_assertions() = 0;

  /**
   * Configure solver option.
   *
   * Should throw a MurxlaSolverOptionException if opt=value is not valid with
   * the currently configured options.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (set-option :<option> <value>)
   * \endverbatim
   *
   * @param opt  A string identifying the solver configuration option.
   * @param value  A string representation of the option value to configure.
   */
  virtual void set_opt(const std::string& opt, const std::string& value) = 0;

  /**
   * Get a term representation of the values of the given terms after a
   * sat check-sat query.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (get-value (<term_1>... <term_n>)
   * \endverbatim
   *
   * @param terms  The terms to query the value for.
   * @return  A set of terms representing the values of the given terms.
   */
  virtual std::vector<Term> get_value(const std::vector<Term>& terms) = 0;

  /**
   * @}
   * \addtogroup solver-may-override
   * @{
   */

  /** Return solver profile JSON string. */
  virtual const std::string get_profile() const { return "{}"; };

  /**
   * Configure the FSM with solver-specific extensions.
   *
   * This is for adding solver-specific actions, states and transitions.
   * Override for solver-specific configuration of the FSM.
   *
   * Does nothing by default.
   *
   * @param fsm  The fsm to configure with extensions.
   */
  virtual void configure_fsm(FSM* fsm) const {}

  /**
   * Disable unsupported actions of the base FSM configuration.
   *
   * Does nothing by default.
   *
   * @param fsm  The fsm to disable actions in.
   */
  virtual void disable_unsupported_actions(FSM* fsm) const {}

  /**
   * Configure the operator kind manager with solver-specific extensions.
   *
   * This is for adding and configuring solver-specific operator kinds.
   *
   * Does nothing by default.
   *
   * @param opmgr  The operator kind manager to configure.
   */
  virtual void configure_opmgr(OpKindManager* opmgr) const {}

  /**
   * Configure solver configuration options.
   *
   * This is for adding and configuring solver options (see
   * SolverManager::add_option()).
   *
   * Does nothing by default.
   *
   * @param smgr  The solver manager maintaining the solver options to
   *              configure.
   */
  virtual void configure_options(SolverManager* smgr) const {}

  /**
   * Reset solver state into assert mode.
   *
   * After this call, calling
   *   - get_model()
   *   - get_unsat_assumptions()
   *   - get_unsat_core() and
   *   - get_proof()
   * is not possible until after the next SAT call.
   */
  virtual void reset_sat();

  /**
   * Create value from Boolean value.
   *
   * This is mainly used for creating Boolean values.
   *
   * @param sort   The sort of the value.
   * @param value  The value.
   * @return  A term representing the value of given sort.
   */
  virtual Term mk_value(Sort sort, bool value) = 0;

  /**
   * Create value from string.
   *
   * This is mainly used for floating-point, integer, real, regular language
   * and string values.
   *
   * @param sort  The sort of the value.
   * @param value  The string representation of the value.
   * @return  A term representing the value of given sort.
   */
  virtual Term mk_value(Sort sort, const std::string& value);

  /**
   * Create rational value.
   *
   * @param sort  The sort of the value.
   * @param num   A decimal string representing the numerator.
   * @param den   A decimal string representing the denominator.
   * @return  A term representing the rational value.
   */
  virtual Term mk_value(Sort sort,
                        const std::string& num,
                        const std::string& den);

  /**
   * Create value from string given in a specific base.
   *
   * This is mainly used for creating bit-vector values.
   *
   * @param sort   The sort of the value.
   * @param value  The string representation of the value.
   * @param base   The numerical base the `value` string is given in.
   * @return  A term representing the value.
   */
  virtual Term mk_value(Sort sort, const std::string& value, Base base);

  /**
   * Create a special value (as defined in SMT-LIB, or as added as
   * solver-specific special values).
   *
   * @param sort   The sort of the special value.
   * @param value  The kind of the special value.
   * @return  A term representing the special value.
   */
  virtual Term mk_special_value(Sort sort,
                                const AbsTerm::SpecialValueKind& value);

  /**
   * Create uninterpreted sort.
   *
   * @param name  The name of the uninterpreted sort.
   * @return  An uninterpreted sort.
   */
  virtual Sort mk_sort(const std::string& name) { return nullptr; }

  /**
   * Create sort with one string argument.
   *
   * This is mainly for creating finite-field sorts.
   *
   * @param kind  The kind of the sort.
   * @param size  The size of the finite-field sort.
   * @return  The created sort.
   */
  virtual Sort mk_sort(SortKind kind, const std::string& size);

  /**
   * Create sort with one unsigned integer argument.
   *
   * This is mainly for creating bit-vector sorts.
   *
   * @param kind  The kind of the sort.
   * @param size  The size of the bit-vector sort.
   * @return  The created sort.
   */
  virtual Sort mk_sort(SortKind kind, uint32_t size);
  /**
   * Create sort with two unsigned integer arguments.
   *
   * This is mainly for creating floating-point sorts.
   *
   * @param kind  The kind of the sort.
   * @param esize  The size of the exponent.
   * @param ssize  The size of the significand.
   * @return  The created sort.
   */
  virtual Sort mk_sort(SortKind kind, uint32_t esize, uint32_t ssize);
  /**
   * Create one or more datatype sorts.
   *
   * Selectors may return a term of
   * 1. a regular Sort
   * 2. a parameter sort (ParamSort)
   * 3. a yet unresolved dataype sort (UnresolvedSort)
   * 4. the sort that is currently being created, indicated by passing a
   *    `nullptr` for the selector codomain sort
   *
   * ParamSort and UnresolvedSort do not wrap actual sorts but are sort
   * placeholders. Thus, solvers must special case cases 1-3 accordingly.
   *
   * ParamSort keeps a back reference to the associated datatype sort in
   * ParamSort::d_sorts (inherited from AbsSort, see AbsSort::get_sorts()).
   *
   * For mutually recursive datatypes, we use instances of UnresolvedSort as
   * place holders. These instances are not unique, we create a new instance of
   * UnresolvedSort for every occurence of an unresolved sort.  Solvers must
   * distinguish these sorts via their names (see UnresolvedSort::get_symbol()).
   *
   * If the mutually recursive datatypes are parametric, then we specify sorts
   * for instantiating these parameters, and store them in
   * UnresolvedSort::d_sorts (inherited from AbsSort). These sorts can be
   * retrieved via UnresolvedSort::get_sorts() (inherited).
   *
   * @param kind          The kind of the sort.
   * @param dt_names      A vector with the names of the datatypes.
   * @param param_sorts   A vector with the lists of parameter sorts in case of
   *                      parametric datatype sorts. The list of parameter
   *                      sorts for a datatype may be empty.
   * @param constructors  A vector with the lists of datatype constructors,
   *                      wich are given as maps of constructor name to vector
   *                      of selectors (which are given as a pair of name and
   *                      sort).
   * @return  The created sort.
   */
  virtual std::vector<Sort> mk_sort(
      SortKind kind,
      const std::vector<std::string>& dt_names,
      const std::vector<std::vector<Sort>>& param_sorts,
      const std::vector<AbsSort::DatatypeConstructorMap>& constructors);

  /**
   * Instantiate parametric sort `param_sort` with given sorts
   * @param param_sort  The parametric sort to be instantiated.
   * @param sorts       The sorts to instantiate the sort parameters of
   *                    `param_sort` with.
   * @return  The instantiated sort.
   */
  virtual Sort instantiate_sort(Sort param_sort,
                                const std::vector<Sort>& sorts);

  /**
   * Set the logic.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (set-logic <logic>)
   * \endverbatim
   *
   * Does nothing by default.
   *
   * @param logic  A string representing the logic to configure, as defined
   *               in the SMT-LIB standard.
   */
  virtual void set_logic(const std::string& logic) {}

  /**
   * Retrieve the unsat core after an unsat check-sat call.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (get-unsat-core)
   * \endverbatim
   *
   * @return  A set of terms representing the unsat core. Returns an empty
   *          vector by default.
   *
   * @note Do not override if solver does not support unsat cores.
   */
  virtual std::vector<Term> get_unsat_core();

  /**
   * Solver-specific term checks.
   * @param term  The term to perform solver-specific checks for.
   */
  virtual void check_term(Term term) {}
  /**
   * Solver-specific term checks.
   * @param term      The term to perform solver-specific checks for.
   * @param str_args  The string arguments used to create `term`
   *                  (see
   *                    Solver::mk_term(const Op::Kind&,
   *                            Sort,
   *                            const std::vector<std::string>&,
   *                            const std::vector<Term>&)
   *                   and
   *                    Solver::mk_term(const Op::Kind& kind,
   *                            const std::vector<std::string>& str_args,
   *                            const std::vector<Term>& args).
   */
  virtual void check_term(Term term, const std::vector<std::string>& str_args)
  {
  }

  /**
   * Solver-specific value checks.
   * @param term  The value term to perform solver-specific checks for.
   */
  virtual void check_value(Term term) {}

  /**
   * Solver-specific sort checks.
   * @param sort  The sort to perform solver-specific checks for.
   */
  virtual void check_sort(Sort sort) {}

  /**
   * Query solver options that need to be enabled for a given theory.
   * @param theory  The theory for which to query solver options for.
   * @return  A map from option string to option value string of enabled
   *          options for a given theory.
   */
  virtual std::unordered_map<std::string, std::string> get_required_options(
      Theory theory) const
  {
    return {};
  }

  /** @} */

  /* NOT to be overriden, murxla level.                                     */
  /* ---------------------------------------------------------------------- */

  /**
   * Get the random number generator of this solver.
   * @return  The RNG of this solver.
   */
  RNGenerator& get_rng() { return d_rng; }

  /**
   * Add solver-specific special value kind.
   *
   * @note  As a style convention, solver-specific special value kinds should
   *        be defined in the solver-specific implementation of AbsTerm.
   *
   * @param sort_kind  The sort kind of a term of given special value kind.
   * @param kind       The solver-specific special value kind to add.
   */
  void add_special_value(SortKind sort_kind,
                         const AbsTerm::SpecialValueKind& kind);

  /**
   * Get the set of special value kinds registered with this solver for a given
   * sort kind.
   *
   * @return  The special values for given sort kind. If no special values are
   *           defined, return an empty set.
   */
  const std::unordered_set<AbsTerm::SpecialValueKind>& get_special_values(
      SortKind sort_kind) const;

  /**
   * Get the sort kinds for which special value kinds are registered with this
   * solver.
   * @return  The set of sort kinds for which this solver has special value
   *          kinds defined.
   */
  const SortKindSet& get_special_values_sort_kinds() const;

 protected:
  /**
   * The random number generator instance of this solver.
   *
   * This RNG is independent from the main RNG (FSM::d_rng, the RNG associated
   * with the FSM). It is seeded in each action by a seed from a dedicated
   * SolverSeedGenerator (SolverManager::d_sng, the SolverSeedGenerator
   * associated with the SolverManager).
   *
   * This RNG is seeded when the action is executed (Action::run()) via
   * macro MURXLA_TRACE, which must always be called first in Action::run().
   */
  RNGenerator d_rng;

  /**
   * Map sort kind to special value kinds.
   *
   * By default, this includes special values defined in SMT-LIB, and common
   * special values for BV (which don't have an SMT-LIB equivalent). The entry
   * for #SORT_ANY is a dummy entry for sort kinds with no special values.
   *
   * @note Special values for BV must be converted to binary, decimal or
   *       hexadecimal strings or integer values if the solver does not provide
   *       dedicated API functions to generate these values. Utility functions
   *       for these conversions are provided in src/util.hpp.
   *
   * This map can be extended with solver-specific special values.
   */
  std::unordered_map<SortKind, std::unordered_set<AbsTerm::SpecialValueKind>>
      d_special_values = {
          {SORT_BAG, {AbsTerm::SPECIAL_VALUE_BAG_EMPTY}},
          {SORT_BV,
           {AbsTerm::SPECIAL_VALUE_BV_ZERO,
            AbsTerm::SPECIAL_VALUE_BV_ONE,
            AbsTerm::SPECIAL_VALUE_BV_ONES,
            AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED,
            AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED}},
          {SORT_FF,
           {AbsTerm::SPECIAL_VALUE_FF_ZERO,
            AbsTerm::SPECIAL_VALUE_FF_ONE,
            AbsTerm::SPECIAL_VALUE_FF_NEG_ONE}},
          {SORT_FP,
           {
               AbsTerm::SPECIAL_VALUE_FP_NAN,
               AbsTerm::SPECIAL_VALUE_FP_POS_INF,
               AbsTerm::SPECIAL_VALUE_FP_NEG_INF,
               AbsTerm::SPECIAL_VALUE_FP_POS_ZERO,
               AbsTerm::SPECIAL_VALUE_FP_NEG_ZERO,
           }},
          {SORT_RM,
           {AbsTerm::SPECIAL_VALUE_RM_RNE,
            AbsTerm::SPECIAL_VALUE_RM_RNA,
            AbsTerm::SPECIAL_VALUE_RM_RTN,
            AbsTerm::SPECIAL_VALUE_RM_RTP,
            AbsTerm::SPECIAL_VALUE_RM_RTZ}},
          {SORT_SEQ, {AbsTerm::SPECIAL_VALUE_SEQ_EMPTY}},
          {SORT_SET,
           {AbsTerm::SPECIAL_VALUE_SET_EMPTY,
            AbsTerm::SPECIAL_VALUE_SET_UNIVERSE}},
          {SORT_ANY, {}},
  };

  /**
   * Contains all sort kinds for have special value kinds have been registered.
   */
  SortKindSet d_special_values_sort_kinds;
};

/**
 * Serialize a solver result to given stream.
 *
 * @param out  The output stream.
 * @param r    The solver result to be serialized.
 * @return     The output stream.
 */
std::ostream& operator<<(std::ostream& out, const Solver::Result& r);

/* -------------------------------------------------------------------------- */

}  // namespace murxla

namespace std {

/** Specialization of std::hash for Sort. */
template <>
struct hash<murxla::Sort>
{
  /**
   * Operator overload to get the hash value of a sort.
   * @param s  The sort to compute the hash value for.
   * @return  The hash value of a sort.
   */
  size_t operator()(const murxla::Sort& s) const;
};

/** Specialization of std::hash for Term. */
template <>
struct hash<murxla::Term>
{
  /**
   * Operator overload to get the hash value of a term.
   * @param t  The term to compute the hash value for.
   * @return  The hash value of a term.
   */
  size_t operator()(const murxla::Term& t) const;
};

}  // namespace std

#endif
