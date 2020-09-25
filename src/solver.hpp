#ifndef __SMTMBT__SOLVER_H
#define __SMTMBT__SOLVER_H

#include <cassert>
#include <cstddef>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "op.hpp"
#include "sort.hpp"
#include "util.hpp"

/* -------------------------------------------------------------------------- */

namespace smtmbt {
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
  virtual size_t hash() const                                      = 0;
  virtual bool equals(const std::shared_ptr<AbsSort>& other) const = 0;

  /** Return true if this sort is an Array sort. */
  virtual bool is_array() const = 0;
  /** Return true if this sort is a Boolean sort. */
  virtual bool is_bool() const = 0;
  /** Return true if this sort is a bit-vector sort. */
  virtual bool is_bv() const   = 0;
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
  /** Return true if this sort is a String sort. */
  virtual bool is_string() const = 0;
  /** Return true if this sort is a RegLan sort. */
  virtual bool is_reglan() const = 0;

  virtual uint32_t get_bv_size() const;
  virtual uint32_t get_fp_exp_size() const;
  virtual uint32_t get_fp_sig_size() const;

  void set_id(uint64_t id);
  uint64_t get_id() const;

  void set_kind(SortKind sort_kind);
  SortKind get_kind();

  void set_sorts(const std::vector<Sort>& sorts);
  const std::vector<Sort>& get_sorts() const;

 protected:
  uint64_t d_id   = 0u;
  SortKind d_kind = SORT_ANY;
  std::vector<Sort> d_sorts;
};

bool operator==(const Sort& a, const Sort& b);

std::ostream& operator<<(std::ostream& out, const Sort s);

struct HashSort
{
  std::size_t operator()(const Sort s) const;
};

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

class AbsTerm
{
 public:
  AbsTerm(){};
  virtual ~AbsTerm(){};
  virtual size_t hash() const                                      = 0;
  virtual bool equals(const std::shared_ptr<AbsTerm>& other) const = 0;

  /** Return true if this term is an Array term. */
  virtual bool is_array() const = 0;
  /** Return true if this term is a Boolean term. */
  virtual bool is_bool() const = 0;
  /** Return true if this term is a bit-vector term. */
  virtual bool is_bv() const = 0;
  /** Return true if this term is a floating-point term. */
  virtual bool is_fp() const = 0;
  /** Return true if this term is a function term. */
  virtual bool is_fun() const = 0;
  /** Return true if this term is an Int term. */
  virtual bool is_int() const = 0;
  /**
   * Return true if this term is a Real term.
   * Note: We consider sort Int as a subtype of sort Real. Hence, this must
   *       return true for Int terms.
   */
  virtual bool is_real() const = 0;
  /** Return true if this term is a RoundingMode term. */
  virtual bool is_rm() const = 0;
  /** Return true if this term is a String term. */
  virtual bool is_string() const = 0;
  /** Return true if this term is a RegLan term. */
  virtual bool is_reglan() const = 0;

  void set_id(uint64_t id);
  uint64_t get_id() const;

  void set_sort(Sort sort);
  Sort get_sort() const;

  void set_levels(const std::vector<uint64_t>& levels);
  const std::vector<uint64_t>& get_levels() const;

  void set_is_value(bool is_value);
  bool is_value();

 protected:
  uint64_t d_id = 0u;
  Sort d_sort = nullptr;

 private:
  bool d_is_value                = false;
  std::vector<uint64_t> d_levels = {};
};

using Term = std::shared_ptr<AbsTerm>;

bool operator==(const Term& a, const Term& b);

std::ostream& operator<<(std::ostream& out, const Term t);
std::ostream& operator<<(std::ostream& out, const std::vector<Term>& vector);

struct HashTerm
{
  size_t operator()(const Term t) const;
};

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

  using SpecialValueKind = std::string;

  /** Special BV values. */
  static const SpecialValueKind SPECIAL_VALUE_BV_ZERO;
  static const SpecialValueKind SPECIAL_VALUE_BV_ONE;
  static const SpecialValueKind SPECIAL_VALUE_BV_ONES;
  static const SpecialValueKind SPECIAL_VALUE_BV_MIN_SIGNED;
  static const SpecialValueKind SPECIAL_VALUE_BV_MAX_SIGNED;
  /** Special FP values. */
  static const SpecialValueKind SPECIAL_VALUE_FP_NAN;
  static const SpecialValueKind SPECIAL_VALUE_FP_POS_INF;
  static const SpecialValueKind SPECIAL_VALUE_FP_NEG_INF;
  static const SpecialValueKind SPECIAL_VALUE_FP_POS_ZERO;
  static const SpecialValueKind SPECIAL_VALUE_FP_NEG_ZERO;
  /** Special RM values. */
  static const SpecialValueKind SPECIAL_VALUE_RM_RNE;
  static const SpecialValueKind SPECIAL_VALUE_RM_RNA;
  static const SpecialValueKind SPECIAL_VALUE_RM_RTN;
  static const SpecialValueKind SPECIAL_VALUE_RM_RTP;
  static const SpecialValueKind SPECIAL_VALUE_RM_RTZ;
  /** Special String values. */
  static const SpecialValueKind SPECIAL_VALUE_RE_NONE;
  static const SpecialValueKind SPECIAL_VALUE_RE_ALL;
  static const SpecialValueKind SPECIAL_VALUE_RE_ALLCHAR;

  Solver(RNGenerator& rng) : d_rng(rng) {}
  Solver() = delete;
  virtual ~Solver() = default;

  virtual void new_solver() = 0;
  virtual void delete_solver() = 0;
  virtual bool is_initialized() const = 0;

  bool supports_theory(TheoryId theory) const;
  virtual TheoryIdVector get_supported_theories() const;
  virtual OpKindSet get_unsupported_op_kinds() const;
  virtual SortKindSet get_unsupported_var_sort_kinds() const;

  virtual void configure_fsm(FSM* fsm) const;
  virtual void configure_smgr(SolverManager* smgr) const;
  void add_special_value(SortKind sort_kind, const SpecialValueKind& kind);

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
  virtual Term mk_special_value(Sort sort, const SpecialValueKind& value);

  virtual Sort mk_sort(const std::string name, uint32_t arity) = 0;
  virtual Sort mk_sort(SortKind kind)                          = 0;
  virtual Sort mk_sort(SortKind kind, uint32_t size);
  virtual Sort mk_sort(SortKind kind, uint32_t esize, uint32_t ssize);
  virtual Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) = 0;

  virtual Term mk_term(const OpKind& kind,
                       std::vector<Term>& args,
                       std::vector<uint32_t>& params) = 0;

  /**
   * Get a freshly wrapped solver sort of the given term.
   *
   * This is used for querying the sort of a freshly created term while
   * delegating sort inference to the solver. The returned sort will have
   * sort kind SORT_ANY and id 0 (will be assigned in the FSM, before adding
   * the sort to the sort databse). Given sort kind is typically unused, but
   * needed by the Smt2Solver.
   */
  virtual Sort get_sort(Term term, SortKind sort_kind) const = 0;

  const std::vector<Base>& get_bases() const;

  /**
   * Return special values for given sort kind.
   * If not special values are defined, return empty set.
   */
  const std::unordered_set<SpecialValueKind>& get_special_values(
      SortKind sort_kind) const;

  virtual std::string get_option_name_incremental() const       = 0;
  virtual std::string get_option_name_model_gen() const         = 0;
  virtual std::string get_option_name_unsat_assumptions() const = 0;

  virtual bool option_incremental_enabled() const       = 0;
  virtual bool option_model_gen_enabled() const         = 0;
  virtual bool option_unsat_assumptions_enabled() const = 0;

  virtual bool check_failed_assumption(const Term& t) const = 0;

  virtual void assert_formula(const Term& t) = 0;

  virtual Result check_sat()                                        = 0;
  virtual Result check_sat_assuming(std::vector<Term>& assumptions) = 0;

  virtual std::vector<Term> get_unsat_assumptions() = 0;

  virtual void push(uint32_t n_levels) = 0;
  virtual void pop(uint32_t n_levels)  = 0;

  virtual void print_model() = 0;

  virtual void reset_assertions() = 0;

  virtual void set_opt(const std::string& opt, const std::string& value) = 0;

  virtual std::vector<Term> get_value(std::vector<Term>& terms) = 0;

  //
  // get_model()
  // get_proof()
  // get_unsat_core()
  //
  //

 protected:
  RNGenerator& d_rng;

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
  std::unordered_map<SortKind,
                     std::unordered_set<SpecialValueKind>,
                     SortKindHashFunction>
      d_special_values = {
          {SORT_BV,
           {SPECIAL_VALUE_BV_ZERO,
            SPECIAL_VALUE_BV_ONE,
            SPECIAL_VALUE_BV_ONES,
            SPECIAL_VALUE_BV_MIN_SIGNED,
            SPECIAL_VALUE_BV_MAX_SIGNED}},
          {SORT_FP,
           {
               SPECIAL_VALUE_FP_NAN,
               SPECIAL_VALUE_FP_POS_INF,
               SPECIAL_VALUE_FP_NEG_INF,
               SPECIAL_VALUE_FP_POS_ZERO,
               SPECIAL_VALUE_FP_NEG_ZERO,
           }},
          {SORT_RM,
           {SPECIAL_VALUE_RM_RNE,
            SPECIAL_VALUE_RM_RNA,
            SPECIAL_VALUE_RM_RTN,
            SPECIAL_VALUE_RM_RTP,
            SPECIAL_VALUE_RM_RTZ}},
          {SORT_REGLAN,
           {SPECIAL_VALUE_RE_NONE,
            SPECIAL_VALUE_RE_ALL,
            SPECIAL_VALUE_RE_ALLCHAR}},
          {SORT_ANY, {}},
  };
};

/** Serialize a solver result to given stream.  */
std::ostream& operator<<(std::ostream& out, const Solver::Result& r);

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt

#endif
