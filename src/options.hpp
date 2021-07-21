#ifndef __MURXLA__OPTIONS_H
#define __MURXLA__OPTIONS_H

#include <cstdint>
#include <string>

#include "theory.hpp"

namespace murxla {

struct Options
{
  /** The seed for the random number generator. */
  uint32_t seed = 0;
  /** The verbosity level. */
  uint32_t verbosity = 0;
  /** The time limit for one test run (one API sequence). */
  double time = 0;
  /** The maximum number of test runs to perform. */
  uint32_t max_runs = 0;

  /** True if seed is provided by user. */
  bool is_seeded = false;
  /** True to include state of RNG in every step of the API trace. */
  bool trace_seeds = false;
  /** True to use simple instead of completely random symbols for inputs. */
  bool simple_symbols = true;
  /** True to only generate SMT-LIB compliant API traces. */
  bool smt = false;
  /** True to print statistics. */
  bool print_stats = false;
  /** Restrict arithmetic operators to linear fragment. */
  bool arith_linear = false;

  /** The directory for tmp files (default: current). */
  std::string tmp_dir = "/tmp";
  /** The directory for output files (default: current). */
  std::string out_dir = "";

  /** The selected solver to test. */
  std::string solver;
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

  /** The name of the options file of the enabled solver. */
  std::string solver_options_file;

  /** The list of currently enabled theories. */
  TheoryIdVector enabled_theories;
};
}  // namespace murxla
#endif
