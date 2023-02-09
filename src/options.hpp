/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__OPTIONS_H
#define __MURXLA__OPTIONS_H

#include <cstdint>
#include <nlohmann/json.hpp>
#include <string>

#include "theory.hpp"

namespace murxla {

using SolverKind              = std::string;
const SolverKind SOLVER_BTOR  = "btor";
const SolverKind SOLVER_BITWUZLA = "bitwuzla";
const SolverKind SOLVER_CVC5  = "cvc5";
const SolverKind SOLVER_SMT2  = "smt2";
const SolverKind SOLVER_YICES = "yices";

struct Options
{
  /** The seed for the random number generator. */
  uint64_t seed = 0;
  /** The verbosity level. */
  uint32_t verbosity = 0;
  /** The time limit for one test run (one API sequence). */
  double time = 1;
  /** The maximum number of test runs to perform. */
  uint32_t max_runs = 0;

  /** True if seed is provided by user. */
  bool is_seeded = false;
  /** True to use simple instead of completely random symbols for inputs. */
  bool simple_symbols = true;
  /** True to only generate SMT-LIB compliant API traces. */
  bool smtlib_compliant = false;
  /** True to print statistics. */
  bool print_stats = false;
  /** True to print FSM configuration. */
  bool print_fsm = false;
  /** Restrict arithmetic operators to linear fragment. */
  bool arith_linear = false;
  /** True to enable option fuzzing. */
  bool fuzz_options = true;
  std::string fuzz_options_filter;

  /** The directory for tmp files (default: current). */
  std::string tmp_dir = "/tmp";
  /** The directory for output files (default: current). */
  std::string out_dir = "";

  /** The selected solver to test. */
  SolverKind solver;
  /** The path to the solver binary to test when --smt2 is enabled. */
  std::string solver_binary;
  /** The file to trace the API call sequence to. */
  std::string api_trace_file_name;
  /** The API trace file to replay. */
  std::string untrace_file_name;
  /** The file to dump the SMT-LIB2 representation of the current trace to. */
  std::string smt2_file_name;

  /**
   * True if the API trace of the current run should be reduced by means of
   * delta-debugging.
   * If seeded or when untracing, current trace will be reduced no matter if
   * it triggers an error or not. In continuous mode, only error inducing
   * traces are reduced.
   */
  bool dd = false;
  /** Ignore output on stdout when delta debugging. */
  bool dd_ignore_out = false;
  /** Ignore output on stderr when delta debugging. */
  bool dd_ignore_err = false;
  /**
   * Check for occurrence of this string in stdout output (rather than
   * matching against the whole stderr output) when delta debugging.
   */
  std::string dd_match_out;
  /**
   * Check for occurrence of this string in stderr output (rather than
   * matching against the whole stderr output) when delta debugging.
   */
  std::string dd_match_err;
  /** The file to write the reduced API trace to. */
  std::string dd_trace_file_name;

  /** The name of the solver to cross-check given solver with. */
  std::string cross_check;

  /** The name of the solver to use for checking. */
  std::string check_solver_name;
  /** Whether unsat core/unsat assumptions/model checking is enabled. */
  bool check_solver = false;

  /** Command line options that need to be set for enabled solver. */
  std::vector<std::pair<std::string, std::string>> solver_options;

  /** The list of currently enabled theories. */
  TheoryVector enabled_theories;
  /** The list of currently disabled theories. */
  TheorySet disabled_theories;

  /** Command line options to be traced. */
  std::string cmd_line_trace;

  /** Solver profile filename. */
  std::string solver_profile_filename;

  /** Output file for exporting errors in JSON format. */
  std::string export_errors_filename = "";

  /** Print native solver API trace. */
  bool solver_trace = false;
};
}  // namespace murxla
#endif
