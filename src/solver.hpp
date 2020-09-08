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

  virtual bool is_bool() const = 0;
  virtual bool is_bv() const   = 0;
  virtual bool is_fp() const   = 0;
  virtual bool is_int() const  = 0;
  /**
   * Return true if this sort is a Real sort.
   * Note: We consider sort Int as a subtype of sort Real. Hence, this must
   *       return true for Int sorts.
   */
  virtual bool is_real() const = 0;
  virtual bool is_rm() const   = 0;
  virtual bool is_string() const = 0;
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

  enum SpecialValueBV
  {
    SMTMBT_BV_ZERO,
    SMTMBT_BV_ONE,
    SMTMBT_BV_ONES,
    SMTMBT_BV_MIN_SIGNED,
    SMTMBT_BV_MAX_SIGNED,
  };

  enum SpecialValueFP
  {
    SMTMBT_FP_NAN,
    SMTMBT_FP_POS_INF,
    SMTMBT_FP_NEG_INF,
    SMTMBT_FP_POS_ZERO,
    SMTMBT_FP_NEG_ZERO,
  };

  enum SpecialValueRM
  {
    SMTMBT_FP_RNE,
    SMTMBT_FP_RNA,
    SMTMBT_FP_RTN,
    SMTMBT_FP_RTP,
    SMTMBT_FP_RTZ,
  };

  enum SpecialValueString
  {
    SMTMBT_RE_NONE,
    SMTMBT_RE_ALL,
    SMTMBT_RE_ALLCHAR,
  };

  Solver(RNGenerator& rng);
  Solver() = delete;
  virtual ~Solver() = default;

  virtual void new_solver() = 0;
  virtual void delete_solver() = 0;
  virtual bool is_initialized() const = 0;

  bool supports_theory(TheoryId theory) const;
  virtual TheoryIdVector get_supported_theories() const;
  virtual OpKindSet get_supported_op_kinds() const;
  virtual OpKindSet get_unsupported_op_kinds() const;
  virtual SortKindSet get_unsupported_var_sort_kinds() const;
  virtual void configure_fsm(FSM* fsm) const;
  virtual void configure_smgr(SolverManager* smgr) const;
  virtual void reset_sat();

  virtual Term mk_var(Sort sort, const std::string& name)   = 0;
  virtual Term mk_const(Sort sort, const std::string& name) = 0;
  virtual Term mk_fun(Sort sort, const std::string& name)   = 0;

  virtual Term mk_value(Sort sort, bool value) = 0;
  virtual Term mk_value(Sort sort, std::string value);
  virtual Term mk_value(Sort sort, std::string num, std::string den);
  virtual Term mk_value(Sort sort, std::string value, Base base);
  virtual Term mk_value(Sort sort, SpecialValueFP value);
  virtual Term mk_value(Sort sort, SpecialValueRM value);
  virtual Term mk_value(Sort sort, SpecialValueString value);

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
  const std::vector<SpecialValueBV>& get_special_values_bv() const;

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

  static const std::unordered_map<std::string, SpecialValueFP>
      s_special_values_fp;
  static const std::unordered_map<std::string, SpecialValueRM>
      s_special_values_rm;
  static const std::unordered_map<std::string, SpecialValueString>
      s_special_values_string;

 protected:
  RNGenerator& d_rng;

  std::vector<Base> d_bases = {Base::BIN, Base::DEC, Base::HEX};

  std::vector<SpecialValueBV> d_special_values_bv = {
      SpecialValueBV::SMTMBT_BV_ZERO,
      SpecialValueBV::SMTMBT_BV_ONE,
      SpecialValueBV::SMTMBT_BV_ONES,
      SpecialValueBV::SMTMBT_BV_MIN_SIGNED,
      SpecialValueBV::SMTMBT_BV_MAX_SIGNED};
};

/** Serialize a special BV value to given stream.  */
std::ostream& operator<<(std::ostream& out, const Solver::SpecialValueBV val);
/** Serialize a special FP value to given stream.  */
std::ostream& operator<<(std::ostream& out, const Solver::SpecialValueFP val);
/** Serialize a special RM value to given stream.  */
std::ostream& operator<<(std::ostream& out, const Solver::SpecialValueRM val);
/** Serialize a special String value to given stream.  */
std::ostream& operator<<(std::ostream& out,
                         const Solver::SpecialValueString val);

/** Serialize a solver result to given stream.  */
std::ostream& operator<<(std::ostream& out, const Solver::Result& r);

/* -------------------------------------------------------------------------- */

}  // namespace smtmbt

#endif
