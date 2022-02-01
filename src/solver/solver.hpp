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
   * Return true if this datatype sort is well founded.
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
   * @Note  If this is an UnresolvedSort that refers to a parametric datatype,
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
   * Determine if this term is not equal to the given term.
   * @param other  The term to compare this term to.
   * @return  True if this term is not equal to the other term.
   */
  virtual bool not_equals(const std::shared_ptr<AbsTerm>& other) const;

  /**
   * Determine if this term is an Array term.
   * @return true if this term is an Array term.
   */
  virtual bool is_array() const;
  /**
   * Determine if this term is a Bag term.
   * @return true if this term is a Bag term.
   */
  virtual bool is_bag() const;
  /**
   * Determine if this term is a Boolean term.
   * @return true if this term is a Boolean term.
   */
  virtual bool is_bool() const;
  /**
   * Determine if this term is a bit-vector term.
   * @return true if this term is a bit-vector term.
   */
  virtual bool is_bv() const;
  /**
   * Determine if this term is a datatype term.
   * @return true if this term is a datatype term.
   */
  virtual bool is_dt() const;
  /**
   * Determine if this term is a floating-point term.
   * @return true if this term is a floating-point term.
   */
  virtual bool is_fp() const;
  /**
   * Determine if this term is a function term.
   * @return true if this term is a function term.
   */
  virtual bool is_fun() const;
  /**
   * Determine if this term is an Int term.
   * @return true if this term is an Int term.
   */
  virtual bool is_int() const;
  /**
   * Determine if this term is a Real term.
   * @return true if this term is a Real term.
   */
  virtual bool is_real() const;
  /**
   * Determine if this term is a RoundingMode term.
   * @return true if this term is a RoundingMode term.
   */
  virtual bool is_rm() const;
  /**
   * Determine if this term is a RegLan term.
   * @return true if this term is a RegLan term.
   */
  virtual bool is_reglan() const;
  /**
   * Determine if this term is a Sequence term.
   * @return true if this term is a Sequence term.
   */
  virtual bool is_seq() const;
  /**
   * Determine if this term is a Set term.
   * @return true if this term is a Set term.
   */
  virtual bool is_set() const;
  /**
   * Determine if this term is a String term.
   * @return true if this term is a String term.
   */
  virtual bool is_string() const;
  /**
   * Determine if this term is an uninterpreted term.
   * @return true if this term is an uninterpreted term.
   */
  virtual bool is_uninterpreted() const;

  /**
   * Determine if this term is a Bag value.
   * @return true if this term is a Bag value.
   */
  virtual bool is_bag_value() const;
  /**
   * Determine if this term is a Boolean value.
   * @return true if this term is a Boolean value.
   */
  virtual bool is_bool_value() const;
  /**
   * Determine if this term is a bit-vector value.
   * @return true if this term is a bit-vector value.
   */
  virtual bool is_bv_value() const;
  /**
   * Determine if this term is a datatype value.
   * @return true if this term is a datatype value.
   */
  virtual bool is_dt_value() const;
  /**
   * Determine if this term is a floating-point value.
   * @return true if this term is a floating-point value.
   */
  virtual bool is_fp_value() const;
  /**
   * Determine if this term is an integer value.
   * @return true if this term is an integer value.
   */
  virtual bool is_int_value() const;
  /**
   * Determine if this term is a real value.
   * @return true if this term is a real value.
   */
  virtual bool is_real_value() const;
  /**
   * Determine if this term is a RegLan value.
   * @return true if this term is a RegLan value.
   */
  virtual bool is_reglan_value() const;
  /**
   * Determine if this term is a rounding mode value.
   * @return true if this term is a rounding mode value.
   */
  virtual bool is_rm_value() const;
  /**
   * Determine if this term is a Sequence value.
   * @return true if this term is a Sequence value.
   */
  virtual bool is_seq_value() const;
  /**
   * Determine if this term is a Sequence value.
   * @return true if this term is a Sequence value.
   */
  virtual bool is_set_value() const;
  /**
   * Determine if this term is a string value.
   * @return true if this term is a string value.
   */
  virtual bool is_string_value() const;

  /**
   * Determine if this term is a special value of given kind.
   * @return true if this term is a special value of given kind.
   */
  virtual bool is_special_value(const SpecialValueKind& kind) const;

  /**
   * Determine if this term is a first-order constant.
   * @return true if this term is a first-order constant.
   */
  virtual bool is_const() const;
  /**
   * Determine if this term is a value.
   * @return true if this term is a value.
   */
  virtual bool is_value() const;
  /**
   * Determine if this term is a variable.
   * @return true if this term is a variable.
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
   * Set the sort of this term.
   *
   * This is not to be overriden by any solver implementations except the
   * shadow solver.
   *
   * @param sort  The sort to be set.
   */
  virtual void set_sort(Sort sort);
  /**
   * Get the sort of this term.
   * @return  The sort of this term.
   */
  Sort get_sort() const;

  /**
   * Get the bit width of this term.
   * Asserts that it is a bit-vector term.
   * @return  The size of this bit-vector term.
   */
  virtual uint32_t get_bv_size() const;
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

  void set_levels(const std::vector<uint64_t>& levels);
  const std::vector<uint64_t>& get_levels() const;

  /**
   * Set leaf kind. Set to LeafKind::NONE if this term is not a leaf.
   *
   * This is not to be overriden by any solver implementations except the
   * shadow solver.
   */
  virtual void set_leaf_kind(LeafKind kind);
  /**
   * Set special value kind.
   * SPECIAL_VALUE_NONE if not a value or no special value.
   *
   * This is not to be overriden by any solver implementations except the
   * shadow solver.
   */
  virtual void set_special_value_kind(const SpecialValueKind& value_kind);
  /**
   * Return leaf kind of this term.
   * Kind is LeafKind::NONE if this term is not a leaf.
   *
   * This is for Murxla level maintenance and not to be overriden with
   * solver-specific implementations.
   */
  LeafKind get_leaf_kind() const;

 protected:
  /** The id of this term. */
  uint64_t d_id = 0u;
  /** The sort of this term. */
  Sort d_sort = nullptr;

 private:
  /** True if this term is a value. */
  LeafKind d_leaf_kind = LeafKind::NONE;
  /**
   * Special value kind.
   * SPECIAL_VALUE_NONE if not a value or no special value.
   */
  SpecialValueKind d_value_kind = SPECIAL_VALUE_NONE;
  /* Stores (sorted) list of unique scope levels of all subterms. */
  std::vector<uint64_t> d_levels = {};
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

class Solver
{
 public:
  enum Result
  {
    UNKNOWN,
    SAT,
    UNSAT,
  };

  enum Base
  {
    BIN = 2,
    DEC = 10,
    HEX = 16,
  };

  using OpKindSortKindMap = std::unordered_map<Op::Kind, SortKindSet>;

  Solver(SolverSeedGenerator& sng);
  Solver()          = delete;
  virtual ~Solver() = default;

  /** Create and initialize wrapped solver. */
  virtual void new_solver() = 0;
  /** Delete wrapped solver. */
  virtual void delete_solver() = 0;
  /** Return true if wrapped solver is initialized. */
  virtual bool is_initialized() const = 0;
  /** Return solver name. */
  virtual const std::string get_name() const = 0;

  /** Get the RNG of this solver. */
  RNGenerator& get_rng() { return d_rng; }

  /** Return true if solver supports given theory. */
  bool supports_theory(TheoryId theory) const;
  /** Get the set of supported theories. */
  virtual TheoryIdVector get_supported_theories() const;
  /**
   * Get the set of theories that are unsupported when THEORY_QUANT is selected.
   * This allows to restrict quantified formulas to a specific subset of the
   * enabled theories.
   */
  virtual TheoryIdVector get_unsupported_quant_theories() const;
  /** Get the set of unsupported operator kinds. */
  virtual OpKindSet get_unsupported_op_kinds() const;
  /** Get the set of unsupported sort kinds. */
  virtual SortKindSet get_unsupported_sort_kinds() const;

  /**
   * Get operator sort restrictions.
   * Maps operator kind to a set of excluded sort kinds. This is only relevant
   * for operators that allow kind SORT_ANY.
   * By default, this is configured to exclude sorts to not generate higher
   * order terms.
   */
  virtual OpKindSortKindMap get_unsupported_op_sort_kinds() const;

  /**
   * Get the set of sorts that are unsupported for quantified variables.
   * Note: This is different from get_unsupported_quant_sort_kinds in that it
   *       only disallows quantified variables of that sort. Other terms of
   *       that sort may occur in quantified formulas.
   */
  virtual SortKindSet get_unsupported_var_sort_kinds() const;
  /**
   * Get the set of sort kinds that are unsupported as parameter for other
   * sorts (e.g., for parametric datatype sorts).
   */
  virtual SortKindSet get_unsupported_sort_param_sort_kinds() const;
  /**
   * Get the set of sort kinds that are unsupported as datatype
   * selectorcodomain sort.
   */
  virtual SortKindSet get_unsupported_dt_sel_codomain_sort_kinds() const;
  /**
   * Get the set of sort kinds that are unsupported as sort of match terms
   * for operator DT_MATCH.
   */
  virtual SortKindSet get_unsupported_dt_match_sort_kinds() const;
  /**
   * Get set of unsupported domain sort kinds for function sorts.
   */
  virtual SortKindSet get_unsupported_fun_sort_domain_sort_kinds() const;
  /**
   * Get set of unsupported codomain sort kinds for function sorts.
   */
  virtual SortKindSet get_unsupported_fun_sort_codomain_sort_kinds() const;
  /**
   * Get set of unsupported domain sort kinds for functions (mk_fun).
   */
  virtual SortKindSet get_unsupported_fun_domain_sort_kinds() const;
  /**
   * Get set of unsupported codomain sort kinds for functions.
   */
  virtual SortKindSet get_unsupported_fun_codomain_sort_kinds() const;
  /**
   * Get the set of sort kinds that are unsupported as array index sort.
   */
  virtual SortKindSet get_unsupported_array_index_sort_kinds() const;
  /**
   * Get the set of sort kinds that are unsupported as array element sort.
   */
  virtual SortKindSet get_unsupported_array_element_sort_kinds() const;
  /**
   * Get the set of sort kinds that are unsupported as bag element sort.
   */
  virtual SortKindSet get_unsupported_bag_element_sort_kinds() const;
  /**
   * Get the set of sort kinds that are unsupported as sequence element sort.
   */
  virtual SortKindSet get_unsupported_seq_element_sort_kinds() const;
  /**
   * Get the set of sort kinds that are unsupported as set element sort.
   */
  virtual SortKindSet get_unsupported_set_element_sort_kinds() const;
  /**
   * Get the set of sort kinds that are unsupported for get-value.
   */
  virtual SortKindSet get_unsupported_get_value_sort_kinds() const;

  virtual void configure_fsm(FSM* fsm) const;
  virtual void disable_unsupported_actions(FSM* fsm) const;
  virtual void configure_smgr(SolverManager* smgr) const;
  virtual void configure_opmgr(OpKindManager* opmgr) const;
  virtual void configure_options(SolverManager* smgr) const {};
  void add_special_value(SortKind sort_kind,
                         const AbsTerm::SpecialValueKind& kind);

  /** Set logic string. */
  virtual void set_logic(const std::string& logic){};

  /** Reset solver.  */
  virtual void reset() = 0;

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

  virtual Term mk_var(Sort sort, const std::string& name)   = 0;
  virtual Term mk_const(Sort sort, const std::string& name) = 0;
  /** Create function `name` of sort `sort`. */
  virtual Term mk_fun(const std::string& name,
                      const std::vector<Term>& args,
                      Term body) = 0;

  virtual Term mk_value(Sort sort, bool value) = 0;
  virtual Term mk_value(Sort sort, const std::string& value);
  virtual Term mk_value(Sort sort,
                        const std::string& num,
                        const std::string& den);
  virtual Term mk_value(Sort sort, const std::string& value, Base base);

  /**
   * Make special value (as defined in SMT-LIB, or as added as solver-specific
   * special values).
   */
  virtual Term mk_special_value(Sort sort,
                                const AbsTerm::SpecialValueKind& value);

  /**
   * Create uninterpreted sort.
   */
  virtual Sort mk_sort(const std::string& name) { return nullptr; }

  /**
   * Create sort of given sort kind with no additional arguments.
   * Examples are sorts of kind SORT_BOOL, SORT_INT, SORT_REAL, SORT_RM,
   * SORT_REGLAN, and SORT_STRING.
   */
  virtual Sort mk_sort(SortKind kind) = 0;
  /**
   * Create sort of given kind with given size argument.
   * This is mainly for creating bit-vector sorts.
   */
  virtual Sort mk_sort(SortKind kind, uint32_t size);
  /**
   * Create sort of given kind with given size arguments.
   * This is mainly for creating floating-point sorts.
   */
  virtual Sort mk_sort(SortKind kind, uint32_t esize, uint32_t ssize);
  /**
   * Create sort with given sort arguments.
   *
   * SORT_ARRAY: First sort is index sort, second sort is element sort.
   *
   * SORT_FUN: First n - 1 sorts represent the domain, last (nth) sort is the
   *           codomain.
   */
  virtual Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) = 0;

  /**
   * Create one or more datatype sorts.
   *
   *
   * dt_names    : A vector with the names of the datatypes.
   * param_sorts : A vector with the lists of parameter sorts in case of
   *               parametric datatype sorts. The list of parameter sorts for a
   *               datatype may be empty.
   * constructors: A vector with the lists of datatype constructors, wich are
   *               given as maps of constructor name to vector of selectors
   *               (which are given as a pair of name and sort).
   *
   * Note: Selectors may return a term of the sort that is currently be
   *       created. We indicate this by passing a nullptr for the selector
   *       codomain sort. Solvers must special case this accordingly.
   *
   *       Parameter sorts keep a back reference to the associated DT sort
   *       in ParamSort::d_sorts (inherited from AbsSort).
   *
   *       For mutually recursive datatypes, we use instances of UnresolvedSort
   *       as place holders. These instances are not unique, we create a new
   *       instance of UnresolvedSort for every occurence of an unresolved sort.
   *       Solvers must distinguish these sorts via their names
   *       (see UnresolvedSort::get_symbol()).
   *
   *       If the mutually recursive datatypes are parametric, then
   *       we specify sorts for instantiating these parameters, and store them
   *       in UnresolvedSort::d_sorts (inherited from AbsSort). These sorts can
   *       be retrieved via UnresolvedSort::get_sorts() (inherited).
   */
  virtual std::vector<Sort> mk_sort(
      SortKind kind,
      const std::vector<std::string>& dt_names,
      const std::vector<std::vector<Sort>>& param_sorts,
      const std::vector<AbsSort::DatatypeConstructorMap>& constructors);

  /** Instantiate parametric sort 'param_sort' with given sorts. */
  virtual Sort instantiate_sort(Sort param_sort,
                                const std::vector<Sort>& sorts);

  /**
   * Create term with given term arguments and indices.
   */
  virtual Term mk_term(const Op::Kind& kind,
                       const std::vector<Term>& args,
                       const std::vector<uint32_t>& indices) = 0;

  /**
   * Create term with given string and term arguments.
   * This is mainly intended for Op::DT_APPLY_SEL, Op::DT_APPLY_TESTER and
   * Op::DT_APPLY_UPDATER.
   */
  virtual Term mk_term(const Op::Kind& kind,
                       const std::vector<std::string>& str_args,
                       const std::vector<Term>& args);
  /**
   * Create term with given Sort, string and term arguments.
   * This is mainly intended for Op::DT_APPLY_CONS.
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
   * sort kind SORT_ANY and id 0 (will be assigned in the FSM, before adding
   * the sort to the sort database). Given sort kind is typically unused, but
   * needed by the Smt2Solver.
   */
  virtual Sort get_sort(Term term, SortKind sort_kind) const = 0;

  const std::vector<Base>& get_bases() const;

  /**
   * Return special values for given sort kind.
   * If not special values are defined, return empty set.
   */
  const std::unordered_set<AbsTerm::SpecialValueKind>& get_special_values(
      SortKind sort_kind) const;

  /** Return all sort kinds for which we have special values. */
  const SortKindSet& get_special_values_sort_kinds() const;

  /**
   * Return a string representation that identifies the solver configuration
   * for enabling/disabling incremental solving.
   */
  virtual std::string get_option_name_incremental() const = 0;
  /**
   * Return a string representation that identifies the solver configuration
   * for enabling/disabling model production.
   */
  virtual std::string get_option_name_model_gen() const = 0;
  /**
   * Return a string representation that identifies the solver configuration
   * for enabling/disabling unsat assumptions production.
   */
  virtual std::string get_option_name_unsat_assumptions() const = 0;
  /**
   * Return a string representation that identifies the solver configuration
   * for enabling/disabling unsat cores production.
   */
  virtual std::string get_option_name_unsat_cores() const = 0;

  /** Return true if incremental solving is currently enabled. */
  virtual bool option_incremental_enabled() const = 0;
  /** Return true if model production is currently enabled. */
  virtual bool option_model_gen_enabled() const = 0;
  /** Return true if unsat assumptions production is currently enabled. */
  virtual bool option_unsat_assumptions_enabled() const = 0;
  /** Return true if unsat cores production is currently enabled. */
  virtual bool option_unsat_cores_enabled() const = 0;

  /** Return true if given term is an unsat assumption. */
  virtual bool is_unsat_assumption(const Term& t) const = 0;

  /**
   * SMT-LIB: (assert <term>)
   *
   * Assert given formula.
   */
  virtual void assert_formula(const Term& t) = 0;

  /**
   * SMT-LIB: (check-sat)
   *
   * Check satisfiability of currently asserted formulas.
   */
  virtual Result check_sat() = 0;
  /**
   * SMT-LIB: (check-sat-assuming)
   *
   * Check satisfiability of currently asserted formulas under the given set of
   * assumptions.
   */
  virtual Result check_sat_assuming(const std::vector<Term>& assumptions) = 0;

  /** Return the current set of unsat assumptions. */
  virtual std::vector<Term> get_unsat_assumptions() = 0;

  /**
   * SMT-LIB: (get-unsat-core)
   *
   * Retrieve the unsat core after an unsat check-sat call.
   *
   * Returns an empty vector by default. Do not override if solver does not
   * support unsat cores.
   */
  virtual std::vector<Term> get_unsat_core();

  virtual void push(uint32_t n_levels) = 0;
  virtual void pop(uint32_t n_levels)  = 0;

  virtual void print_model() = 0;

  virtual void reset_assertions() = 0;

  /**
   * Should throw a MurxlaSolverOptionException if opt=value is not valid with
   * the currently set options.
   */
  virtual void set_opt(const std::string& opt, const std::string& value) = 0;

  virtual std::vector<Term> get_value(const std::vector<Term>& terms) = 0;

  //
  // get_model()
  // get_proof()
  //
  //

  /** Solver-specific term checks. */
  virtual void check_term(Term term) {}
  virtual void check_term(Term term, const std::vector<std::string>& str_args)
  {
  }

  /** Solver-specific value checks. */
  virtual void check_value(Term term) {}

  /** Solver-specific sort checks. */
  virtual void check_sort(Sort sort) {}

  /** Query solver options that need to be enabled for a given theory. */
  virtual std::unordered_map<std::string, std::string> get_required_options(
      TheoryId theory) const
  {
    return {};
  }

 protected:
  RNGenerator d_rng;

  std::vector<Base> d_bases = {Base::BIN, Base::DEC, Base::HEX};

  /**
   * Map sort kind to special values.
   *
   * By default, this includes special values defined in SMT-LIB, and common
   * special values for BV (which don't have an SMT-LIB equivalent). The entry
   * for SORT_ANY is a dummy entry for sort kinds with no special values.
   *
   * Note that special values for BV must be converted to binary, decimal or
   * hexadecimal strings or integer values if the solver does not provide
   * dedicated API functions to generate these values. Utility functions for
   * these conversions are provided in src/util.hpp.
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

  /** Contains all sort kinds for which we have special values. */
  SortKindSet d_special_values_sort_kinds;
};

/** Serialize a solver result to given stream.  */
std::ostream& operator<<(std::ostream& out, const Solver::Result& r);

/* -------------------------------------------------------------------------- */

}  // namespace murxla

namespace std {

template <>
struct hash<murxla::Sort>
{
  size_t operator()(const murxla::Sort& s) const;
};

template <>
struct hash<murxla::Term>
{
  size_t operator()(const murxla::Term& t) const;
};

}  // namespace std

#endif
