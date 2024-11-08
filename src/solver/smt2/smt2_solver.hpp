/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__SMT2_SOLVER_H
#define __MURXLA__SMT2_SOLVER_H

#include "fsm.hpp"
#ifdef MURXLA_USE_CVC5
#include "solver/cvc5/cvc5_solver.hpp"
#endif
#ifdef MURXLA_USE_BITWUZLA
#include "solver/bitwuzla/bitwuzla_solver.hpp"
#endif
#include "solver/solver.hpp"
#include "theory.hpp"

/* -------------------------------------------------------------------------- */

namespace murxla {
namespace smt2 {

/* -------------------------------------------------------------------------- */
/* Smt2Sort                                                                   */
/* -------------------------------------------------------------------------- */

class Smt2Sort : public AbsSort
{
 public:
  /** Get a fresh sort symbol. Only used for function sorts. */
  static std::string get_next_symbol();

  Smt2Sort(std::string repr, uint32_t bv_size = 0, uint32_t sig_size = 0)
      : d_repr(repr), d_bv_size(bv_size), d_sig_size(sig_size)
  {
  }
  Smt2Sort(std::string repr, const std::string& ff_size)
      : d_repr(repr), d_ff_size(ff_size)
  {
  }
  ~Smt2Sort(){};
  size_t hash() const override;
  bool equals(const Sort& other) const override;
  std::string to_string() const override;
  bool is_array() const override;
  bool is_bag() const override;
  bool is_bool() const override;
  bool is_bv() const override;
  bool is_dt() const override;
  bool is_dt_parametric() const override;
  bool is_fp() const override;
  bool is_fun() const override;
  bool is_int() const override;
  bool is_real() const override;
  bool is_rm() const override;
  bool is_seq() const override;
  bool is_set() const override;
  bool is_string() const override;
  bool is_uninterpreted() const override;
  bool is_reglan() const override;
  uint32_t get_bv_size() const override;
  std::string get_dt_name() const override;
  std::string get_ff_size() const override;
  uint32_t get_fp_exp_size() const override;
  uint32_t get_fp_sig_size() const override;
  Sort get_array_index_sort() const override;
  Sort get_array_element_sort() const override;
  uint32_t get_fun_arity() const override;
  Sort get_fun_codomain_sort() const override;
  std::vector<Sort> get_fun_domain_sorts() const override;
  Sort get_bag_element_sort() const override;
  Sort get_seq_element_sort() const override;
  Sort get_set_element_sort() const override;

  const std::string& get_repr() const;
  void set_symbol(const std::string& symbol);

 private:
  /**
   * The counter of sort symbols that have been freshly introduced. Used to
   * generate a unique sort string for function sorts.
   */
  inline static uint32_t s_symbol_cnt = 0;
  /** The representation of this sort. */
  std::string d_repr;
  /**
   * The bit-vector size of this sort.
   * Doubles as exponent size for FP sorts.
   */
  uint32_t d_bv_size = 0;
  /** The floating-point significand size of this sort. */
  uint32_t d_sig_size = 0;
  /** The symbol of this sort. Only for function sorts. */
  std::string d_symbol;
  /** The finite field size of this sort. */
  std::string d_ff_size;
};

/* -------------------------------------------------------------------------- */
/* Smt2Term                                                                   */
/* -------------------------------------------------------------------------- */

class Smt2Term : public AbsTerm
{
 public:
  Smt2Term(Op::Kind kind,
           std::vector<std::string> str_args,
           std::vector<Term> args,
           std::vector<uint32_t> indices,
           std::string repr)
      : d_kind(kind),
        d_str_args(str_args),
        d_args(args),
        d_indices(indices),
        d_repr(repr)
  {
  }
  ~Smt2Term(){};
  size_t hash() const override;
  bool equals(const Term& other) const override;
  std::string to_string() const override;

  const std::string& get_kind() const override;
  std::vector<Term> get_children() const override;
  const std::vector<Term>& get_args() const;
  const std::vector<std::string>& get_str_args() const;
  const std::vector<uint32_t>& get_indices_uint32() const;
  const std::string get_repr() const;

 private:
  /** The operator kind of this term. */
  Op::Kind d_kind;
  /** The string arguments of this term. Only needed for DT operator kinds. */
  std::vector<std::string> d_str_args;
  /** The arguments (children) of this term. */
  std::vector<Term> d_args;
  /** The indices of this term. */
  std::vector<uint32_t> d_indices;
  /** The smt2 representation of this term. */
  std::string d_repr;

  std::unordered_map<std::string, std::string> d_op_kind_to_str = {
      {Op::DISTINCT, "distinct"},
      {Op::EQUAL, "="},
      {Op::ITE, "ite"},

      /* Boolean */
      {Op::AND, "and"},
      {Op::IFF, "="},
      {Op::IMPLIES, "=>"},
      {Op::NOT, "not"},
      {Op::OR, "or"},
      {Op::XOR, "xor"},

      /* Arrays */
      {Op::ARRAY_SELECT, "select"},
      {Op::ARRAY_STORE, "store"},

      /* Bags */
      {Op::BAG_UNION_MAX, "bag.union_max"},
      {Op::BAG_UNION_DISJOINT, "bag.union_disjoint"},
      {Op::BAG_INTERSECTION_MIN, "bag.inter_min"},
      {Op::BAG_DIFFERENCE_SUBTRACT, "bag.difference_subtract"},
      {Op::BAG_DIFFERENCE_REMOVE, "bag.difference_remove"},
      {Op::BAG_SUBBAG, "bag.subbag"},
      {Op::BAG_COUNT, "bag.count"},
      {Op::BAG_DUPLICATE_REMOVAL, "bag.duplicate_removal"},
      {Op::BAG_MAKE, "bag"},
      {Op::BAG_EMPTY, "bag.empty"},
      {Op::BAG_CARD, "bag.card"},
      {Op::BAG_CHOOSE, "bag.choose"},
      {Op::BAG_IS_SINGLETON, "bag.is_singleton"},
      {Op::BAG_FROM_SET, "bag.from_set"},
      {Op::BAG_TO_SET, "bag.to_set"},
      {Op::BAG_MAP, "bag.map"},

      /* BV */
      {Op::BV_EXTRACT, "extract"},
      {Op::BV_REPEAT, "repeat"},
      {Op::BV_ROTATE_LEFT, "rotate_left"},
      {Op::BV_ROTATE_RIGHT, "rotate_right"},
      {Op::BV_SIGN_EXTEND, "sign_extend"},
      {Op::BV_ZERO_EXTEND, "zero_extend"},

      {Op::BV_ADD, "bvadd"},
      {Op::BV_AND, "bvand"},
      {Op::BV_ASHR, "bvashr"},
      {Op::BV_COMP, "bvcomp"},
      {Op::BV_CONCAT, "concat"},
      {Op::BV_LSHR, "bvlshr"},
      {Op::BV_MULT, "bvmul"},
      {Op::BV_NAND, "bvnand"},
      {Op::BV_NEG, "bvneg"},
      {Op::BV_NOR, "bvnor"},
      {Op::BV_NOT, "bvnot"},
      {Op::BV_OR, "bvor"},
      {Op::BV_SDIV, "bvsdiv"},
      {Op::BV_SGE, "bvsge"},
      {Op::BV_SGT, "bvsgt"},
      {Op::BV_SHL, "bvshl"},
      {Op::BV_SLE, "bvsle"},
      {Op::BV_SLT, "bvslt"},
      {Op::BV_SMOD, "bvsmod"},
      {Op::BV_SREM, "bvsrem"},
      {Op::BV_SUB, "bvsub"},
      {Op::BV_UDIV, "bvudiv"},
      {Op::BV_UGE, "bvuge"},
      {Op::BV_UGT, "bvugt"},
      {Op::BV_ULE, "bvule"},
      {Op::BV_ULT, "bvult"},
      {Op::BV_UREM, "bvurem"},
      {Op::BV_XNOR, "bvxnor"},
      {Op::BV_XOR, "bvxor"},

      /* Datatypes */
      {Op::DT_APPLY_TESTER, "is"},
      {Op::DT_APPLY_UPDATER, "update"},
      {Op::DT_MATCH, "match"},
      {Op::DT_MATCH_BIND_CASE, ""},
      {Op::DT_MATCH_CASE, ""},

      /* FF */
      {Op::FINITE_FIELD_ADD, "ff.add"},
      {Op::FINITE_FIELD_MULT, "ff.mul"},
      {Op::FINITE_FIELD_NEG, "ff.neg"},

      /* FP */
      {Op::FP_TO_FP_FROM_BV, "to_fp"},
      {Op::FP_TO_FP_FROM_SBV, "to_fp"},
      {Op::FP_TO_FP_FROM_FP, "to_fp"},
      {Op::FP_TO_FP_FROM_UBV, "to_fp_unsigned"},
      {Op::FP_TO_FP_FROM_REAL, "to_fp"},
      {Op::FP_TO_SBV, "fp.to_sbv"},
      {Op::FP_TO_UBV, "fp.to_ubv"},

      {Op::FP_ABS, "fp.abs"},
      {Op::FP_ADD, "fp.add"},
      {Op::FP_DIV, "fp.div"},
      {Op::FP_EQ, "fp.eq"},
      {Op::FP_FMA, "fp.fma"},
      {Op::FP_FP, "fp"},
      {Op::FP_IS_NORMAL, "fp.isNormal"},
      {Op::FP_IS_SUBNORMAL, "fp.isSubnormal"},
      {Op::FP_IS_INF, "fp.isInfinite"},
      {Op::FP_IS_NAN, "fp.isNaN"},
      {Op::FP_IS_NEG, "fp.isNegative"},
      {Op::FP_IS_POS, "fp.isPositive"},
      {Op::FP_IS_ZERO, "fp.isZero"},
      {Op::FP_LT, "fp.lt"},
      {Op::FP_LEQ, "fp.leq"},
      {Op::FP_GT, "fp.gt"},
      {Op::FP_GEQ, "fp.geq"},
      {Op::FP_MAX, "fp.max"},
      {Op::FP_MIN, "fp.min"},
      {Op::FP_MUL, "fp.mul"},
      {Op::FP_NEG, "fp.neg"},
      {Op::FP_REM, "fp.rem"},
      {Op::FP_RTI, "fp.roundToIntegral"},
      {Op::FP_SQRT, "fp.sqrt"},
      {Op::FP_SUB, "fp.sub"},
      {Op::FP_TO_REAL, "fp.to_real"},

      /* Ints */
      {Op::INT_IS_DIV, "divisible"},
      {Op::INT_NEG, "-"},
      {Op::INT_SUB, "-"},
      {Op::INT_ADD, "+"},
      {Op::INT_MUL, "*"},
      {Op::INT_DIV, "div"},
      {Op::INT_MOD, "mod"},
      {Op::INT_ABS, "abs"},
      {Op::INT_LT, "<"},
      {Op::INT_LTE, "<="},
      {Op::INT_GT, ">"},
      {Op::INT_GTE, ">="},

      /* Reals */
      {Op::REAL_NEG, "-"},
      {Op::REAL_SUB, "-"},
      {Op::REAL_ADD, "+"},
      {Op::REAL_MUL, "*"},
      {Op::REAL_DIV, "/"},
      {Op::REAL_LT, "<"},
      {Op::REAL_LTE, "<="},
      {Op::REAL_GT, ">"},
      {Op::REAL_GTE, ">="},
      {Op::REAL_IS_INT, "is_int"},

      /* Reals and Ints */
      {Op::INT_TO_REAL, "to_real"},
      {Op::REAL_IS_INT, "is_int"},
      {Op::REAL_TO_INT, "to_int"},

      /* Quantifiers */
      {Op::FORALL, "forall"},
      {Op::EXISTS, "exists"},

      /* Sequences */
      {Op::SEQ_CONCAT, "seq.++"},
      {Op::SEQ_LENGTH, "seq.len"},
      {Op::SEQ_EXTRACT, "seq.extract"},
      {Op::SEQ_UPDATE, "seq.update"},
      {Op::SEQ_AT, "seq.at"},
      {Op::SEQ_CONTAINS, "seq.contains"},
      {Op::SEQ_INDEXOF, "seq.indexof"},
      {Op::SEQ_REPLACE, "seq.replace"},
      {Op::SEQ_REPLACE_ALL, "seq.replace_all"},
      {Op::SEQ_REV, "seq.rev"},
      {Op::SEQ_PREFIX, "seq.prefixof"},
      {Op::SEQ_SUFFIX, "seq.suffixof"},
      {Op::SEQ_UNIT, "seq.unit"},
      {Op::SEQ_NTH, "seq.nth"},

      /* Sets */
      {Op::SET_CARD, "set.card"},
      {Op::SET_COMPLEMENT, "set.complement"},
      {Op::SET_COMPREHENSION, "set.comprehension"},
      {Op::SET_CHOOSE, "set.choose"},
      {Op::SET_INTERSECTION, "set.inter"},
      {Op::SET_INSERT, "set.insert"},
      {Op::SET_IS_SINGLETON, "set.is_singleton"},
      {Op::SET_UNION, "set.union"},
      {Op::SET_MEMBER, "set.member"},
      {Op::SET_MINUS, "set.minus"},
      {Op::SET_SINGLETON, "set.singleton"},
      {Op::SET_SUBSET, "set.subset"},
      /* Strings */
      {Op::STR_CONCAT, "str.++"},
      {Op::STR_LEN, "str.len"},
      {Op::STR_LT, "str.<"},
      {Op::STR_TO_RE, "str.to_re"},
      {Op::STR_IN_RE, "str.in_re"},
      {Op::STR_LE, "str.<="},
      {Op::STR_AT, "str.at"},
      {Op::STR_SUBSTR, "str.substr"},
      {Op::STR_PREFIXOF, "str.prefixof"},
      {Op::STR_SUFFIXOF, "str.suffixof"},
      {Op::STR_CONTAINS, "str.contains"},
      {Op::STR_INDEXOF, "str.indexof"},
      {Op::STR_REPLACE, "str.replace"},
      {Op::STR_REPLACE_ALL, "str.replace_all"},
      {Op::STR_REPLACE_RE, "str.replace_re"},
      {Op::STR_REPLACE_RE_ALL, "str.replace_re_all"},
      {Op::STR_IS_DIGIT, "str.is_digit"},
      {Op::STR_TO_CODE, "str.to_code"},
      {Op::STR_FROM_CODE, "str.from_code"},
      {Op::STR_TO_INT, "str.to_int"},
      {Op::STR_FROM_INT, "str.from_int"},
      {Op::RE_ALL, "re.all"},
      {Op::RE_ALLCHAR, "re.allchar"},
      {Op::RE_CONCAT, "re.++"},
      {Op::RE_COMP, "re.comp"},
      {Op::RE_DIFF, "re.diff"},
      {Op::RE_INTER, "re.inter"},
      {Op::RE_LOOP, "re.loop"},
      {Op::RE_NONE, "re.none"},
      {Op::RE_OPT, "re.opt"},
      {Op::RE_PLUS, "re.+"},
      {Op::RE_POW, "re.^"},
      {Op::RE_RANGE, "re.range"},
      {Op::RE_STAR, "re.*"},
      {Op::RE_UNION, "re.union"},
      /* Transcendentals */
      {Op::TRANS_PI, "real.pi"},
      {Op::TRANS_SINE, "sin"},
      {Op::TRANS_COSINE, "cos"},
      {Op::TRANS_TANGENT, "tan"},
      {Op::TRANS_COTANGENT, "cot"},
      {Op::TRANS_SECANT, "sec"},
      {Op::TRANS_COSECANT, "csc"},
      {Op::TRANS_ARCSINE, "arcsin"},
      {Op::TRANS_ARCCOSINE, "arccos"},
      {Op::TRANS_ARCTANGENT, "arctan"},
      {Op::TRANS_ARCCOSECANT, "arccsc"},
      {Op::TRANS_ARCSECANT, "arcsec"},
      {Op::TRANS_ARCCOTANGENT, "arccot"},
      {Op::TRANS_SQRT, "sqrt"},
      /* UF */
      {Op::UF_APPLY, ""},
#ifdef MURXLA_USE_BITWUZLA
      /* bitwuzla-specific operator kinds */
      {bitwuzla::BitwuzlaTerm::OP_BV_DEC, "bvdec"},
      {bitwuzla::BitwuzlaTerm::OP_BV_INC, "bvinc"},
      {bitwuzla::BitwuzlaTerm::OP_BV_REDAND, "bvredand"},
      {bitwuzla::BitwuzlaTerm::OP_BV_REDOR, "bvredor"},
      {bitwuzla::BitwuzlaTerm::OP_BV_REDXOR, "bvredxor"},
      {bitwuzla::BitwuzlaTerm::OP_BV_ROL, "bvrol"},
      {bitwuzla::BitwuzlaTerm::OP_BV_ROR, "bvror"},
      {bitwuzla::BitwuzlaTerm::OP_BV_SADDO, "bvsaddo"},
      {bitwuzla::BitwuzlaTerm::OP_BV_SDIVO, "bvsdivo"},
      {bitwuzla::BitwuzlaTerm::OP_BV_SMULO, "bvsmulo"},
      {bitwuzla::BitwuzlaTerm::OP_BV_SSUBO, "bvssubo"},
      {bitwuzla::BitwuzlaTerm::OP_BV_UADDO, "bvuaddo"},
      {bitwuzla::BitwuzlaTerm::OP_BV_UMULO, "bvumulo"},
      {bitwuzla::BitwuzlaTerm::OP_BV_USUBO, "bvusubo"},
      {bitwuzla::BitwuzlaTerm::OP_FP_TO_FP_FROM_REAL, "to_fp"},
      {bitwuzla::BitwuzlaTerm::OP_IFF, "="},
#endif
#ifdef MURXLA_USE_CVC5
      /* cvc5-specific operator kinds */
      {cvc5::Cvc5Term::OP_BV_REDAND, "bvredand"},
      {cvc5::Cvc5Term::OP_BV_REDOR, "bvredor"},
      {cvc5::Cvc5Term::OP_INT_TO_BV, "int2bv"},
      {cvc5::Cvc5Term::OP_BV_TO_NAT, "bv2nat"},
      {cvc5::Cvc5Term::OP_INT_IAND, "iand"},
      {cvc5::Cvc5Term::OP_INT_POW2, "int.pow2"},
      {cvc5::Cvc5Term::OP_STRING_UPDATE, "str.update"},
      {cvc5::Cvc5Term::OP_STRING_TOLOWER, "str.tolower"},
      {cvc5::Cvc5Term::OP_STRING_TOUPPER, "str.toupper"},
      {cvc5::Cvc5Term::OP_STRING_REV, "str.rev"},
#endif
  };
};

/* -------------------------------------------------------------------------- */
/* Smt2Solver                                                                 */
/* -------------------------------------------------------------------------- */

class Smt2Solver : public Solver
{
 public:
  Smt2Solver(SolverSeedGenerator& sng,
             std::ostream& out,
             const std::string& solver_binary);
  ~Smt2Solver() override;

  void new_solver() override;
  void delete_solver() override;
  bool is_initialized() const override;
  const std::string get_name() const override;
  const std::string get_profile() const override;

  Term mk_var(Sort sort, const std::string& name) override;
  Term mk_const(Sort sort, const std::string& name) override;
  Term mk_fun(const std::string& name,
              const std::vector<Term>& args,
              Term body) override;

  Term mk_value(Sort sort, bool value) override;
  Term mk_value(Sort sort, const std::string& value) override;
  Term mk_value(Sort sort,
                const std::string& num,
                const std::string& den) override;
  Term mk_value(Sort sort, const std::string& value, Base base) override;

  Term mk_special_value(Sort sort,
                        const AbsTerm::SpecialValueKind& value) override;

  Sort mk_sort(const std::string& name) override;
  Sort mk_sort(SortKind kind) override;
  Sort mk_sort(SortKind kind, const std::string& size) override;
  Sort mk_sort(SortKind kind, uint32_t size) override;
  Sort mk_sort(SortKind kind, uint32_t esize, uint32_t ssize) override;
  Sort mk_sort(SortKind kind, const std::vector<Sort>& sorts) override;
  std::vector<Sort> mk_sort(SortKind kind,
                            const std::vector<std::string>& dt_names,
                            const std::vector<std::vector<Sort>>& param_sorts,
                            const std::vector<AbsSort::DatatypeConstructorMap>&
                                constructors) override;

  Sort instantiate_sort(Sort param_sort,
                        const std::vector<Sort>& sorts) override;

  Term mk_term(const Op::Kind& kind,
               const std::vector<Term>& args,
               const std::vector<uint32_t>& indices) override;
  Term mk_term(const Op::Kind& kind,
               const std::vector<std::string>& str_args,
               const std::vector<Term>& args) override;
  Term mk_term(const Op::Kind& kind,
               Sort sort,
               const std::vector<std::string>& str_args,
               const std::vector<Term>& args) override;

  Sort get_sort(Term term, SortKind sort_kind) override;

  std::string get_option_name_incremental() const override;
  std::string get_option_name_model_gen() const override;
  std::string get_option_name_unsat_assumptions() const override;
  std::string get_option_name_unsat_cores() const override;
  bool option_incremental_enabled() const override;
  bool option_model_gen_enabled() const override;
  bool option_unsat_assumptions_enabled() const override;
  bool option_unsat_cores_enabled() const override;

  bool is_unsat_assumption(const Term& t) const override;

  void assert_formula(const Term& t) override;

  Result check_sat() override;
  Result check_sat_assuming(const std::vector<Term>& assumptions) override;

  std::vector<Term> get_unsat_assumptions() override;

  std::vector<Term> get_unsat_core() override;

  void push(uint32_t n_levels) override;
  void pop(uint32_t n_levels) override;

  void print_model() override;

  void set_logic(const std::string& logic) override;

  void reset() override;
  void reset_assertions() override;

  void set_opt(const std::string& opt, const std::string& value) override;

  std::vector<Term> get_value(const std::vector<Term>& terms) override;

 private:
  enum ResponseKind
  {
    SMT2_SUCCESS,
    SMT2_SAT,
    SMT2_SEXPR,
  };

  void push_to_external(std::string s, ResponseKind expected);
  std::string get_from_external() const;
  void dump_smt2(std::string s,
                 ResponseKind expected = ResponseKind::SMT2_SUCCESS);
  std::ostream& d_out = std::cout;
  bool d_online       = false;
  FILE* d_file_to     = nullptr;
  FILE* d_file_from   = nullptr;

  bool d_initialized               = false;
  bool d_incremental               = false;
  bool d_model_gen                 = false;
  bool d_unsat_assumptions         = false;
  bool d_unsat_cores               = false;
  uint32_t d_n_unnamed_consts      = 0;
  uint32_t d_n_unnamed_ufs         = 0;
  uint32_t d_n_unnamed_vars        = 0;
  uint64_t d_define_sort_param_cnt = 0;
  Solver::Result d_last_result     = Solver::Result::UNKNOWN;

  static constexpr int32_t SMT2_READ_END  = 0;
  static constexpr int32_t SMT2_WRITE_END = 1;

  pid_t d_online_pid = 0;
  std::string d_solver_call;
  std::unordered_map<std::string, std::string> d_sort_fun_map;
};

/* -------------------------------------------------------------------------- */

}  // namespace smt2
}  // namespace murxla

#endif
