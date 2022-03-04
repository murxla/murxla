/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__SOLVER_PROFILE_H
#define __MURXLA__SOLVER_PROFILE_H

#include <nlohmann/json.hpp>
#include <string>
#include <unordered_set>

#include "op.hpp"
#include "theory.hpp"

namespace murxla {

class SolverProfile
{
 public:
  using OpKindSortKindMap = std::unordered_map<Op::Kind, SortKindSet>;

  SolverProfile(const std::string& json_str);
  ~SolverProfile() = default;

  static std::string merge(const std::string& json_str1,
                           const std::string& json_str2);

  /**
   * Get the set of supported theories of the wrapped solver.
   * @return  A vector with the set of supported theories.
   */
  TheoryVector get_supported_theories() const;

  /** Get list of unsupported theory combinations. */
  /**
   * Get unsupported theory combinations.
   *
   * This allows to restrict the combination of certain theories.
   *
   * @return  A map of theories to a list of unsupported theory combinations.
   */
  std::unordered_map<Theory, std::vector<Theory>>
  get_unsupported_theory_combinations() const;

  /**
   * Get the set of unsupported operator kinds (see Op::Kind).
   * @return  A vector with the set of unsupported operator kinds.
   */
  OpKindSet get_unsupported_op_kinds() const;

  /**
   * Get operator sort restrictions.
   *
   * Maps operator kind to a set of excluded sort kinds. This is only relevant
   * for operators that allow kind #SORT_ANY.
   *
   * By default, this is configured to exclude sort kinds that would allow
   * to create higher-order terms.
   *
   * @return  A map from operator kind (Op::Kind) to a set of excluded sort
   *          kinds (murxla::SortKind).
   */
  OpKindSortKindMap get_unsupported_op_sort_kinds() const;

  /**
   * Get the set of unsupported sort kinds (see murxla::SortKind).
   * @return  A vector with the set of unsupported sort kinds.
   */
  SortKindSet get_unsupported_sort_kinds() const;

  /**
   * Get the set of sort kinds that are unsupported for quantified variables.
   *
   * @note  This is different from get_unsupported_quant_sort_kinds() in that
   *        it only disallows quantified variables of these sort kinds.
   *        Other terms of these sort kinds may occur in quantified formulas.
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported for
   *          quantified variables.
   */
  SortKindSet get_unsupported_var_sort_kinds() const;

  /**
   * Get the set of sort kinds that are unsupported as index sort of array
   * sorts (see mk_sort()).
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          as array index sort.
   */
  SortKindSet get_unsupported_array_index_sort_kinds() const;

  /**
   * Get the set of sort kinds that are unsupported as element sort of
   * array sorts (see mk_sort()).
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          as array element sort.
   */
  SortKindSet get_unsupported_array_element_sort_kinds() const;

  /**
   * Get the set of sort kinds that are unsupported as element sort of
   * bag sorts (see mk_sort()).
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          as bag element sort.
   */
  SortKindSet get_unsupported_bag_element_sort_kinds() const;

  /**
   * Get the set of sort kinds that are unsupported as sort of match terms
   * for operator Op::DT_MATCH.
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          for match terms of operator Op::DT_MATCH.
   */
  SortKindSet get_unsupported_dt_match_sort_kinds() const;

  /**
   * Get the set of sort kinds that are unsupported as datatype
   * selector codomain sort.
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          for datatype selector codomain sorts.
   */
  SortKindSet get_unsupported_dt_sel_codomain_sort_kinds() const;

  /**
   * Get set of unsupported codomain sort kinds for functions (see mk_fun()).
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          as codomain sorts for function terms.
   */
  SortKindSet get_unsupported_fun_codomain_sort_kinds() const;

  /**
   * Get set of unsupported domain sort kinds for functions (see mk_fun()).
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          as domain sorts for function terms.
   */
  SortKindSet get_unsupported_fun_domain_sort_kinds() const;

  /**
   * Get set of unsupported codomain sort kinds for function sorts
   * (see mk_sort()).
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          as codomain sort for function sorts.
   */
  SortKindSet get_unsupported_fun_sort_codomain_sort_kinds() const;

  /**
   * Get set of unsupported domain sort kinds for function sorts
   * (see mk_sort()).
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          as domain sorts for function sorts.
   */
  SortKindSet get_unsupported_fun_sort_domain_sort_kinds() const;

  /**
   * Get the set of sort kinds that are unsupported for get-value
   * (see ActionGetValue).
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          when querying the value of a term.
   */
  SortKindSet get_unsupported_get_value_sort_kinds() const;

  /**
   * Get the set of sort kinds that are unsupported as element sort of
   * sequence sorts (see mk_sort()).
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          as sequence element sort.
   */
  SortKindSet get_unsupported_seq_element_sort_kinds() const;

  /**
   * Get the set of sort kinds that are unsupported as element sort for
   * set sorts.
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported
   *          as set element sort.
   */
  SortKindSet get_unsupported_set_element_sort_kinds() const;

  /**
   * Get the set of sort kinds that are unsupported as sort parameters
   * (e.g., for parametric datatype sorts).
   *
   * @return  A set of sort kinds (murxla::SortKind) that are unsupported for
   *          sort parameters.
   */
  SortKindSet get_unsupported_sort_param_sort_kinds() const;

  /** Get list of errors to be filtered out (ignored).*/
  std::vector<std::string> get_excluded_errors() const;

  /** Get list of error filters.*/
  std::vector<std::string> get_error_filters() const;

 private:
  static inline const std::string KEY_THEORIES = "theories";
  static inline const std::string KEY_THEORY_COMBINATIONS =
      "exclude-combinations";
  static inline const std::string KEY_OPERATORS  = "operators";
  static inline const std::string KEY_SORT_RESTR = "sort-restrictions";
  static inline const std::string KEY_SORTS      = "sorts";
  static inline const std::string KEY_ERRORS     = "errors";

  /* Exclude sorts that would create higher order terms. */
  OpKindSortKindMap d_default_unsupported_op_sort_kinds = {
      {Op::DISTINCT, {SORT_FUN}},
      {Op::EQUAL, {SORT_FUN}},
      {Op::ITE, {SORT_FUN}}};

  void parse();

  bool has_key(const std::string& key) const;

  Theory to_theory(const std::string& str) const;
  SortKind to_sort_kind(const std::string& str) const;

  std::vector<std::string> get_array(const std::vector<std::string>& keys,
                                     bool required = false) const;

  SortKindSet get_sort_kinds(const std::vector<std::string>& keys,
                             bool required = false) const;

  std::string d_json_str;
  nlohmann::json d_json;

  std::unordered_map<std::string, Theory> d_str_to_theory;
  std::unordered_map<std::string, SortKind> d_str_to_sort_kind;
};

}  // namespace murxla

#endif
