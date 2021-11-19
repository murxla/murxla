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

using Sort = std::shared_ptr<AbsSort>;

class AbsSort
{
 public:
  virtual ~AbsSort(){};

  /** Get the hash value of this sort. */
  virtual size_t hash() const                                      = 0;
  /** Get a string representation of this sort. */
  virtual std::string to_string() const                            = 0;
  /** Return true if this sort is equal to the other sort. */
  virtual bool equals(const std::shared_ptr<AbsSort>& other) const = 0;
  /** Return true if this sort is not equal to the other sort. */
  virtual bool not_equals(const std::shared_ptr<AbsSort>& other) const;

  /** Return true if this sort is an Array sort. */
  virtual bool is_array() const = 0;
  /** Return true if this sort is a Bag sort. */
  virtual bool is_bag() const = 0;
  /** Return true if this sort is a Boolean sort. */
  virtual bool is_bool() const = 0;
  /** Return true if this sort is a bit-vector sort. */
  virtual bool is_bv() const   = 0;
  /** Return true if this sort is a datatype sort. */
  virtual bool is_dt() const = 0;
  /** Return true if this sort is a floating-point sort. */
  virtual bool is_fp() const   = 0;
  /** Return true if this sort is a function sort. */
  virtual bool is_fun() const  = 0;
  /** Return true if this sort is an Int sort. */
  virtual bool is_int() const  = 0;
  /**
   * Return true if this sort is a Real sort.
   * Note: We consider sort Int as a subtype of sort Real. Hence, this must
   *       return true for Int sorts.
   */
  virtual bool is_real() const = 0;
  /** Return true if this sort is a RoundingMode sort. */
  virtual bool is_rm() const   = 0;
  /** Return true if this sort is a RegLan sort. */
  virtual bool is_reglan() const = 0;
  /** Return true if this sort is a Sequence sort. */
  virtual bool is_seq() const = 0;
  /** Return true if this sort is a Set sort. */
  virtual bool is_set() const = 0;
  /** Return true if this sort is a String sort. */
  virtual bool is_string() const = 0;

  /**
   * Get the array index sort of this sort.
   * Returns nullptr by default.
   */
  virtual Sort get_array_index_sort() const;
  /**
   * Get the array element sort of this sort.
   * Returns nullptr by default.
   */
  virtual Sort get_array_element_sort() const;
  /**
   * Get the bag element sort of this sort.
   * Returns nullptr by default.
   */
  virtual Sort get_bag_element_sort() const;
  /**
   * Get the bit-vector size of this sort.
   * Returns 0 by default.
   */
  virtual uint32_t get_bv_size() const;
  /**
   * Get the datatype constructor name of this sort.
   * Returns an empty string by default.
   */
  virtual std::string get_dt_name() const;
  /**
   * Get the number of datatype constructors of this sort.
   * Returns 0 by default.
   */
  virtual uint32_t get_dt_num_cons() const;
  /**
   * Get the datatype constructor names of this sort.
   * Returns an empty vector by default.
   */
  virtual std::vector<std::string> get_dt_cons_names() const;
  /**
   * Get the floating-point exponent size of this sort.
   * Returns 0 by default.
   */
  virtual uint32_t get_fp_exp_size() const;
  /**
   * Get the floating-point significand size of this sort.
   * Returns 0 by default.
   */
  virtual uint32_t get_fp_sig_size() const;
  /**
   * Get the function arity of this sort.
   * Returns 0 by default.
   */
  virtual uint32_t get_fun_arity() const;
  /**
   * Get the function codomain sort of this sort.
   * Returns nullptr by default.
   */
  virtual Sort get_fun_codomain_sort() const;
  /**
   * Get the function domain sorts of this sort.
   * Returns an empty vector by default.
   */
  virtual std::vector<Sort> get_fun_domain_sorts() const;
  /**
   * Get the sequence element sort of this sort.
   * Returns nullptr by default.
   */
  virtual Sort get_seq_element_sort() const;
  /**
   * Get the set element sort of this sort.
   * Returns nullptr by default.
   */
  virtual Sort get_set_element_sort() const;

  void set_id(uint64_t id);
  uint64_t get_id() const;

  virtual void set_kind(SortKind sort_kind);
  SortKind get_kind();

  virtual void set_sorts(const std::vector<Sort>& sorts);
  const std::vector<Sort>& get_sorts() const;

 protected:
  uint64_t d_id   = 0u;
  SortKind d_kind = SORT_ANY;
  std::vector<Sort> d_sorts;
};

bool operator==(const Sort& a, const Sort& b);
bool operator!=(const Sort& a, const Sort& b);

/**
 * Serialize a Sort to given stream.
 *
 * This represents a sort as 's' + its id and is mainly intended for tracing
 * purposes.  For a representation of a term as provided by the corresponding
 * solver, user AbsSort::to_string() insted.
 */
std::ostream& operator<<(std::ostream& out, const Sort s);

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

class AbsTerm
{
 public:
  using SpecialValueKind = std::string;

  inline static const SpecialValueKind SPECIAL_VALUE_NONE =
      "not-a-special-value";
  /** Special Bag values. */
  inline static const SpecialValueKind SPECIAL_VALUE_BAG_EMPTY = "bag.empty";
  /** Special BV values. */
  inline static const SpecialValueKind SPECIAL_VALUE_BV_ZERO = "bv.zero";
  inline static const SpecialValueKind SPECIAL_VALUE_BV_ONE  = "bv.one";
  inline static const SpecialValueKind SPECIAL_VALUE_BV_ONES = "bv.ones";
  inline static const SpecialValueKind SPECIAL_VALUE_BV_MIN_SIGNED =
      "bv-min-signed";
  inline static const SpecialValueKind SPECIAL_VALUE_BV_MAX_SIGNED =
      "bv-max-signed";
  /** Special FP values. */
  inline static const SpecialValueKind SPECIAL_VALUE_FP_NAN      = "nan";
  inline static const SpecialValueKind SPECIAL_VALUE_FP_POS_INF  = "+oo";
  inline static const SpecialValueKind SPECIAL_VALUE_FP_NEG_INF  = "-oo";
  inline static const SpecialValueKind SPECIAL_VALUE_FP_POS_ZERO = "+zero";
  inline static const SpecialValueKind SPECIAL_VALUE_FP_NEG_ZERO = "-zero";
  /** Special RM values. */
  inline static const SpecialValueKind SPECIAL_VALUE_RM_RNA = "rna";
  inline static const SpecialValueKind SPECIAL_VALUE_RM_RNE = "rne";
  inline static const SpecialValueKind SPECIAL_VALUE_RM_RTN = "rtn";
  inline static const SpecialValueKind SPECIAL_VALUE_RM_RTP = "rtp";
  inline static const SpecialValueKind SPECIAL_VALUE_RM_RTZ = "rtz";
  /** Special Sequence values. */
  inline static const SpecialValueKind SPECIAL_VALUE_SEQ_EMPTY = "seq.empty";
  /** Special Sets values. */
  inline static const SpecialValueKind SPECIAL_VALUE_SET_EMPTY = "set.empty";
  inline static const SpecialValueKind SPECIAL_VALUE_SET_UNIVERSE =
      "set.universe";

  enum LeafKind
  {
    NONE,
    CONSTANT,
    VALUE,
    VARIABLE,
  };

  AbsTerm(){};
  virtual ~AbsTerm(){};

  /** Get the hash value of this term. */
  virtual size_t hash() const                                      = 0;
  /** Get a string representation of this term. */
  virtual std::string to_string() const                            = 0;
  /** Return true if this term is equal to the other term. */
  virtual bool equals(const std::shared_ptr<AbsTerm>& other) const = 0;
  /** Return true if this term is not equal to the other term. */
  virtual bool not_equals(const std::shared_ptr<AbsTerm>& other) const;

  /** Return true if this term is an Array term. */
  virtual bool is_array() const;
  /** Return true if this term is a Bag term. */
  virtual bool is_bag() const;
  /** Return true if this term is a Boolean term. */
  virtual bool is_bool() const;
  /** Return true if this term is a bit-vector term. */
  virtual bool is_bv() const;
  /** Return true if this term is a datatype term. */
  virtual bool is_dt() const;
  /** Return true if this term is a floating-point term. */
  virtual bool is_fp() const;
  /** Return true if this term is a function term. */
  virtual bool is_fun() const;
  /** Return true if this term is an Int term. */
  virtual bool is_int() const;
  /** Return true if this term is a Real term. */
  virtual bool is_real() const;
  /** Return true if this term is a RoundingMode term. */
  virtual bool is_rm() const;
  /** Return true if this term is a RegLan term. */
  virtual bool is_reglan() const;
  /** Return true if this term is a Sequence term. */
  virtual bool is_seq() const;
  /** Return true if this term is a Set term. */
  virtual bool is_set() const;
  /** Return true if this term is a String term. */
  virtual bool is_string() const;

  /** Return true if this term is a Bag value. */
  virtual bool is_bag_value() const;
  /** Return true if this term is a Boolean value. */
  virtual bool is_bool_value() const;
  /** Return true if this term is a bit-vector value. */
  virtual bool is_bv_value() const;
  /** Return true if this term is a datatype value. */
  virtual bool is_dt_value() const;
  /** Return true if this term is a floating-point value. */
  virtual bool is_fp_value() const;
  /** Return true if this term is an integer value. */
  virtual bool is_int_value() const;
  /** Return true if this term is a real value. */
  virtual bool is_real_value() const;
  /** Return true if this term is a RegLan value. */
  virtual bool is_reglan_value() const;
  /** Return true if this term is a rounding mode value. */
  virtual bool is_rm_value() const;
  /** Return true if this term is a Sequence value. */
  virtual bool is_seq_value() const;
  /** Return true if this term is a Sequence value. */
  virtual bool is_set_value() const;
  /** Return true if this term is a string value. */
  virtual bool is_string_value() const;

  /** Return true if this term is a special value of given kind. */
  virtual bool is_special_value(const SpecialValueKind& kind) const;

  /** Return true if this term is a first-order constant. */
  virtual bool is_const() const;
  /** Return true if this term is a value. */
  virtual bool is_value() const;
  /** Return true if this term is a variable. */
  virtual bool is_var() const;

  /**
   * Return the kind of the current term.
   *
   * This kind is not a kind we cache on creation, but the kind that the
   * solver reports. May be Op::UNDEFINED.
   *
   * Must be overriden and may not return Op::UNDEFINED if the solver supports
   * the theory of sequences (required for properly initializing sequence sorts
   * for Op::SEQ_UNIT).
   */
  virtual const Op::Kind& get_kind() const;

  /**
   * Return the children of the current term.
   * Note: As with Solver::mk_term, the returned terms are "raw" Terms, in the
   *       sense that they are only wrapped into a Term, with no additional
   *       book keeping information (all data members have default values).
   */
  virtual std::vector<std::shared_ptr<AbsTerm>> get_children() const;

  /** Return true if this term is of an indexed operator kind. */
  virtual bool is_indexed() const;
  /** Get the number of indices of a term with an indexed operator kind. */
  virtual size_t get_num_indices() const;
  /** Get the indices of a term with an indexed operator kind. */
  virtual std::vector<std::string> get_indices() const;

  /** Set the id of this term. */
  void set_id(uint64_t id);
  /** Get the id of this term. */
  uint64_t get_id() const;

  /**
   * Set the sort of this term.
   *
   * This is not to be overriden by any solver implementations except the
   * shadow solver.
   */
  virtual void set_sort(Sort sort);
  /** Get the sort of this term. */
  Sort get_sort() const;

  /**
   * Get the bit width of this term.
   * Asserts that it is a bit-vector term.
   */
  virtual uint32_t get_bv_size() const;
  /**
   * Get the exponent bit width of this term.
   * Asserts that it is a floating-point term.
   */
  virtual uint32_t get_fp_exp_size() const;
  /**
   * Get the significand bit width of this term.
   * Asserts that it is a floating-point term.
   */
  virtual uint32_t get_fp_sig_size() const;
  /**
   * Get the array index sort of this term.
   * Asserts that it is an array term.
   */
  virtual Sort get_array_index_sort() const;
  /**
   * Get the array element sort of this term.
   * Asserts that it is an array term.
   */
  virtual Sort get_array_element_sort() const;
  /**
   * Get the function arity of this term.
   * Asserts that it is an function term.
   */
  virtual uint32_t get_fun_arity() const;
  /**
   * Get the function codomain sort of this term.
   * Asserts that it is an function term.
   */
  virtual Sort get_fun_codomain_sort() const;
  /**
   * Get the function domain sorts of this term.
   * Asserts that it is an function term.
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
  SpecialValueKind d_value_kind  = SPECIAL_VALUE_NONE;
  std::vector<uint64_t> d_levels = {};
};

using Term = std::shared_ptr<AbsTerm>;

bool operator==(const Term& a, const Term& b);
bool operator!=(const Term& a, const Term& b);

/**
 * Serialize a Term to given stream.
 *
 * This represents a term as 't' + its id and is mainly intended for tracing
 * purposes.  For a representation of a term as provided by the corresponding
 * solver, user AbsTerm::to_string() insted.
 */
std::ostream& operator<<(std::ostream& out, const Term t);
/**
 * Serialize a vector of Terms to given stream.
 *
 * As above, a term is represented as 't' + its id, so this will yield a list
 * of space separated ids.
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

  Solver(SolverSeedGenerator& sng) : d_rng(sng.seed()) {}
  Solver() = delete;
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
   * Get the set of sort kinds that are unsupported as function domain sort.
   */
  virtual SortKindSet get_unsupported_fun_domain_sort_kinds() const;
  /**
   * Get the set of sort kinds that are unsupported as function codomain sort.
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
  virtual Term mk_fun(Sort sort, const std::string& name)   = 0;

  virtual Term mk_value(Sort sort, bool value) = 0;
  virtual Term mk_value(Sort sort, std::string value);
  virtual Term mk_value(Sort sort, std::string num, std::string den);
  virtual Term mk_value(Sort sort, std::string value, Base base);

  /**
   * Make special value (as defined in SMT-LIB, or as added as solver-specific
   * special values).
   */
  virtual Term mk_special_value(Sort sort,
                                const AbsTerm::SpecialValueKind& value);

  virtual Sort mk_sort(const std::string name, uint32_t arity) = 0;
  /**
   * Create sort of given sort kind with no additional arguments.
   * Examples are sorts of kind SORT_BOOL, SORT_INT, SORT_REAL, SORT_RM,
   * SORT_REGLAN, and SORT_STRING.
   */
  virtual Sort mk_sort(SortKind kind)                          = 0;
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
   * Create datatype sort.
   *
   * name: The name of the datatype.
   * ctors: The list of datatype constructors, given as a map of constructor
   *        name to vector of selectors (which are given as a pair of name and
   *        sort).
   */
  virtual Sort mk_sort(
      SortKind kind,
      const std::string& name,
      const std::unordered_map<std::string,
                               std::vector<std::pair<std::string, Sort>>>&
          ctors);

  virtual Term mk_term(const Op::Kind& kind,
                       const std::vector<Term>& args,
                       const std::vector<uint32_t>& params) = 0;

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

  virtual std::string get_option_name_incremental() const       = 0;
  virtual std::string get_option_name_model_gen() const         = 0;
  virtual std::string get_option_name_unsat_assumptions() const = 0;
  virtual std::string get_option_name_unsat_cores() const       = 0;

  virtual bool option_incremental_enabled() const       = 0;
  virtual bool option_model_gen_enabled() const         = 0;
  virtual bool option_unsat_assumptions_enabled() const = 0;
  virtual bool option_unsat_cores_enabled() const       = 0;

  virtual bool is_unsat_assumption(const Term& t) const = 0;

  virtual void assert_formula(const Term& t) = 0;

  virtual Result check_sat()                                        = 0;
  virtual Result check_sat_assuming(std::vector<Term>& assumptions) = 0;

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

  virtual std::vector<Term> get_value(std::vector<Term>& terms) = 0;

  //
  // get_model()
  // get_proof()
  //
  //

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
