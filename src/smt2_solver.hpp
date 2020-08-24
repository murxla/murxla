#ifndef __SMTMBT__SMT2_SOLVER_H
#define __SMTMBT__SMT2_SOLVER_H

#include "fsm.hpp"
#include "solver.hpp"
#include "theory.hpp"

/* -------------------------------------------------------------------------- */

namespace smtmbt {
namespace smt2 {

/* -------------------------------------------------------------------------- */
/* Smt2Sort                                                                   */
/* -------------------------------------------------------------------------- */

class Smt2Sort : public AbsSort
{
 public:
  Smt2Sort(std::string repr, uint32_t bv_size = 0, uint32_t sig_size = 0)
      : d_repr(repr), d_bv_size(bv_size), d_sig_size(sig_size)
  {
  }
  ~Smt2Sort(){};
  size_t hash() const override;
  bool equals(const Sort& other) const override;

  bool is_bool() const override;
  bool is_bv() const override;
  bool is_fp() const override;
  bool is_int() const override;
  bool is_rm() const override;
  uint32_t get_bv_size() const override;
  uint32_t get_fp_exp_size() const override;
  uint32_t get_fp_sig_size() const override;
  const std::string& get_repr() const;

 private:
  std::string d_repr;
  uint32_t d_bv_size  = 0; /* doubles as exponent size for FP sorts */
  uint32_t d_sig_size = 0;
};

/* -------------------------------------------------------------------------- */
/* Smt2Term                                                                   */
/* -------------------------------------------------------------------------- */

class Smt2Term : public AbsTerm
{
 public:
  enum LeafKind
  {
    NONE,
    CONST,
    VALUE,
    VAR,
  };

  Smt2Term(OpKind kind,
           std::vector<Term> args,
           std::vector<uint32_t> params,
           LeafKind leaf_kind,
           std::string repr)
      : d_kind(kind),
        d_args(args),
        d_params(params),
        d_leaf_kind(leaf_kind),
        d_repr(repr)
  {
  }
  ~Smt2Term(){};
  size_t hash() const override;
  bool equals(const Term& other) const override;
  const OpKind get_kind() const;
  const std::vector<Term>& get_args() const;
  const std::vector<uint32_t>& get_params() const;
  const std::string get_repr() const;

 private:
  OpKind d_kind;
  std::vector<Term> d_args;
  std::vector<uint32_t> d_params;
  LeafKind d_leaf_kind = LeafKind::NONE;
  std::string d_repr;

  std::unordered_map<OpKind, std::string> d_op_kind_to_str = {
      {OP_DISTINCT, "distinct"},
      {OP_EQUAL, "="},
      {OP_ITE, "ite"},

      /* Boolean */
      {OP_AND, "and"},
      {OP_IFF, "="},
      {OP_IMPLIES, "=>"},
      {OP_NOT, "not"},
      {OP_OR, "or"},
      {OP_XOR, "xor"},

      /* Arrays */
      {OP_ARRAY_SELECT, "select"},
      {OP_ARRAY_STORE, "store"},

      /* BV */
      {OP_BV_EXTRACT, "extract"},
      {OP_BV_REPEAT, "repeat"},
      {OP_BV_ROTATE_LEFT, "rotate_left"},
      {OP_BV_ROTATE_RIGHT, "rotate_right"},
      {OP_BV_SIGN_EXTEND, "sign_extend"},
      {OP_BV_ZERO_EXTEND, "zero_extend"},

      {OP_BV_ADD, "bvadd"},
      {OP_BV_AND, "bvand"},
      {OP_BV_ASHR, "bvashr"},
      {OP_BV_COMP, "bvcomp"},
      {OP_BV_CONCAT, "concat"},
      {OP_BV_LSHR, "bvlshr"},
      {OP_BV_MULT, "bvmul"},
      {OP_BV_NAND, "bvnand"},
      {OP_BV_NEG, "bvneg"},
      {OP_BV_NOR, "bvnor"},
      {OP_BV_NOT, "bvnot"},
      {OP_BV_OR, "bvor"},
      //{OP_BV_REDAND, "unsupported"},
      //{OP_BV_REDOR, "unsupported"},
      //{OP_BV_SADDO, "unsupported"},
      {OP_BV_SDIV, "bvsdiv"},
      //{OP_BV_SDIVO, "unsupported"},
      {OP_BV_SGE, "bvsge"},
      {OP_BV_SGT, "bvsgt"},
      {OP_BV_SHL, "bvshl"},
      {OP_BV_SLE, "bvsle"},
      {OP_BV_SLT, "bvslt"},
      {OP_BV_SMOD, "bvsmod"},
      //{OP_BV_SMULO, "unsupported"},
      {OP_BV_SREM, "bvsrem"},
      //{OP_BV_SSUBO, "unsupported"},
      {OP_BV_SUB, "bvsub"},
      //{OP_BV_UADDO, "unsupported"},
      {OP_BV_UDIV, "bvudiv"},
      {OP_BV_UGE, "bvuge"},
      {OP_BV_UGT, "bvugt"},
      {OP_BV_ULE, "bvule"},
      {OP_BV_ULT, "bvult"},
      //{OP_BV_UMULO, "unsupported"},
      {OP_BV_UREM, "bvurem"},
      //{OP_BV_USUBO, "unsupported},
      {OP_BV_XNOR, "bvxnor"},
      {OP_BV_XOR, "bvxor"},
      //{OP_BV_INC, "unsupported"},
      //{OP_BV_DEC, "unsupported"},
      //{OP_BV_REDXOR, "unsupported"},

      /* FP */
      {OP_FP_TO_FP_FROM_BV, "to_fp"},
      {OP_FP_TO_FP_FROM_INT_BV, "to_fp"},
      {OP_FP_TO_FP_FROM_FP, "to_fp"},
      {OP_FP_TO_FP_FROM_UINT_BV, "to_fp_unsigned"},
      {OP_FP_TO_FP_FROM_REAL, "to_fp"},
      {OP_FP_TO_SBV, "fp.to_sbv"},
      {OP_FP_TO_UBV, "fp.to_ubv"},

      {OP_FP_ABS, "fp.abs"},
      {OP_FP_ADD, "fp.add"},
      {OP_FP_DIV, "fp.div"},
      {OP_FP_EQ, "fp.eq"},
      {OP_FP_FMA, "fp.fma"},
      {OP_FP_FP, "fp"},
      {OP_FP_IS_NORMAL, "fp.isNormal"},
      {OP_FP_IS_SUBNORMAL, "fp.isSubnormal"},
      {OP_FP_IS_INF, "fp.isInfinite"},
      {OP_FP_IS_NAN, "fp.isNaN"},
      {OP_FP_IS_NEG, "fp.isNegative"},
      {OP_FP_IS_POS, "fp.isPositive"},
      {OP_FP_IS_ZERO, "fp.isZero"},
      {OP_FP_LT, "fp.lt"},
      {OP_FP_LTE, "fp.leq"},
      {OP_FP_GT, "fp.gt"},
      {OP_FP_GTE, "fp.geq"},
      {OP_FP_MAX, "fp.max"},
      {OP_FP_MIN, "fp.min"},
      {OP_FP_MUL, "fp.mul"},
      {OP_FP_NEG, "fp.neg"},
      {OP_FP_REM, "fp.rem"},
      {OP_FP_RTI, "fp.roundToIntegral"},
      {OP_FP_SQRT, "fp.sqrt"},
      {OP_FP_SUB, "fp.sub"},
      {OP_FP_TO_REAL, "fp.to_real"},

      /* Ints */
      {OP_INT_IS_DIV, "divisible"},
      {OP_INT_NEG, "-"},
      {OP_INT_SUB, "-"},
      {OP_INT_ADD, "+"},
      {OP_INT_MUL, "*"},
      {OP_INT_DIV, "div"},
      {OP_INT_MOD, "mod"},
      {OP_INT_ABS, "abs"},
      {OP_INT_LT, "<"},
      {OP_INT_LTE, "<="},
      {OP_INT_GT, ">"},
      {OP_INT_GTE, ">="},

      /* Quantifiers */
      {OP_FORALL, "forall"},
      {OP_EXISTS, "exists"},
  };
};

/* -------------------------------------------------------------------------- */
/* Smt2Solver                                                                 */
/* -------------------------------------------------------------------------- */

class Smt2Solver : public Solver
{
 public:
  Smt2Solver(
      RNGenerator& rng, std::ostream& out, bool online, FILE* to, FILE* from);
  ~Smt2Solver() override{};

  void new_solver() override;
  void delete_solver() override;
  bool is_initialized() const override;

  OpKindSet get_unsupported_op_kinds() const override;

  Term mk_var(Sort sort, const std::string& name) override;
  Term mk_const(Sort sort, const std::string& name) override;
  Term mk_fun(Sort sort, const std::string& name) override;

  Term mk_value(Sort sort, bool value) override;
  Term mk_value(Sort sort, std::string value) override;
  Term mk_value(Sort sort, std::string value, Base base) override;
  Term mk_value(Sort sort, SpecialValueFP value) override;
  Term mk_value(Sort sort, SpecialValueRM value) override;

  Sort mk_sort(const std::string name, uint32_t arity) override;
  Sort mk_sort(SortKind kind) override;
  Sort mk_sort(SortKind kind, uint32_t size) override;
  Sort mk_sort(SortKind kind, uint32_t esize, uint32_t ssize) override;
  Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) override;

  Term mk_term(const OpKind& kind,
               std::vector<Term>& args,
               std::vector<uint32_t>& params) override;

  Sort get_sort(Term term, SortKind sort_kind) const override;

  void assert_formula(const Term& t) const override;

  Result check_sat() const override;
  Result check_sat_assuming(std::vector<Term>& assumptions) const override;

  std::vector<Term> get_unsat_assumptions() const override;

  void push(uint32_t n_levels) const override;
  void pop(uint32_t n_levels) const override;

  void print_model() const override;

  void reset_assertions() const override;

  void set_opt(const std::string& opt, const std::string& value) override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;
  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;

  bool check_failed_assumption(const Term& t) const override;

  std::vector<Term> get_value(std::vector<Term>& terms) const override;

 private:
  enum ResponseKind
  {
    SMT2_SUCCESS,
    SMT2_SAT,
    SMT2_SEXPR,
  };

  void push_to_external(std::string s) const;
  std::string get_from_external() const;
  void dump_smt2(std::string s) const;
  std::ostream& d_out = std::cout;
  bool d_online       = false;
  FILE* d_file_to     = nullptr;
  FILE* d_file_from   = nullptr;

  bool d_initialized          = false;
  bool d_incremental          = false;
  bool d_model_gen            = false;
  bool d_unsat_assumptions    = false;
  uint32_t d_n_unnamed_consts = 0;
  uint32_t d_n_unnamed_vars   = 0;
  ResponseKind d_response     = SMT2_SUCCESS;
};

/* -------------------------------------------------------------------------- */

}  // namespace smt2
}  // namespace smtmbt

#endif
