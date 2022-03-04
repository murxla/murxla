/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__MURXLA_H
#define __MURXLA__MURXLA_H

#include <cstdint>
#include <string>

#include "action.hpp"
#include "options.hpp"
#include "result.hpp"
#include "solver/solver_profile.hpp"
#include "solver_option.hpp"
#include "theory.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

namespace statistics {
struct Statistics;
};
class Solver;

/* -------------------------------------------------------------------------- */

struct ErrorInfo
{
  ErrorInfo(uint64_t id,
            const std::string& errmsg,
            const std::vector<uint64_t>& seeds)
      : id(id), errmsg(errmsg), seeds(seeds){};

  uint64_t id;
  std::string errmsg;
  std::vector<uint64_t> seeds;
};

class Murxla
{
 public:
  using ErrorMap = std::unordered_map<std::string, ErrorInfo>;

  enum TraceMode
  {
    NONE,
    TO_STDOUT,
    TO_FILE,
  };

  inline static const std::string API_TRACE = "tmp-api.trace";
  inline static const std::string SMT2_FILE = "tmp-smt2.smt2";

  /** Constructor. */
  Murxla(statistics::Statistics* stats,
         const Options& options,
         SolverOptions* solver_options,
         ErrorMap* error_map,
         const std::string& tmp_dir);

  /**
   * A single test run.
   *
   * seed               : The current seed for the RNG.
   * double             : The time limit for one test run.
   * file_out           : The file to write stdout output of a test run to.
   * file_err           : The file to write stderr output of a test run to.
   * api_trace_file_name: When non-empty, trace is immediately written to file
   *                      if 'run_forked' is false. Else, 'api_trace_file_name'
   *                      is set to the name of the temp trace file name and
   *                      its contents are copied to the final trace file in
   *                      run(), after run_aux() is finished.
   * untrace_file_name  : When non-empty, the name of the trace file to replay.
   * run_forked         : True if test run is executed in a child process.
   * record_stats       : True if statistics for this test run should be
   *                      recorded. This should only be true for main test
   *                      runs, not for replayed runs or delta debugging runs.
   * trace_mode         : The trace mode for this run.
   *
   * Returns a result that indicates the status of the test run.
   */
  Result run(uint64_t seed,
             double time,
             const std::string& file_out,
             const std::string& file_err,
             const std::string& api_trace_file_name,
             const std::string& untrace_file_name,
             bool run_forked,
             bool record_stats,
             TraceMode trace_mode);

  /** Continuous test run. */
  void test();

  /** Print the current configuration of the FSM to stdout. */
  void print_fsm() const;

  /**
   * Create solver.
   *
   * This creates an instance of a solver of the kind configured in d_options.
   *
   * sng        : The associated solver seed generator.
   * smt2_out   : The output stream for the SMT-LIB output in case of
   *              SOLVER_SMT2.
   */
  Solver* create_solver(SolverSeedGenerator& sng,
                        std::ostream& smt2_out = std::cout) const;

  /** The set of configuration options. */
  const Options& d_options;
  /** The set of configured solver options. */
  SolverOptions* d_solver_options;
  /** The directory for temp files. */
  std::string d_tmp_dir;
  /**
   * The cached error message in case that an exception was thrown when running
   * forked.
   */
  std::string d_error_msg;

 private:
  enum class ErrorKind
  {
    DUPLICATE, /* Error message is a duplicate since it was already reported. */
    ERROR,     /* Error message is new. */
    FILTER,    /* Error message filtered out. */
  };

  /**
   * Create solver.
   *
   * This creates an instance of one of the base solvers, that is, a solver
   * that does not wrap other solver instances.
   *
   * sng        : The associated solver seed generator.
   * solver_kind: The kind of the solver to be created.
   * smt2_out   : The output stream for the SMT-LIB output in case of
   *              SOLVER_SMT2.
   */
  Solver* new_solver(SolverSeedGenerator& sng,
                     const SolverKind& solver_kind,
                     std::ostream& smt2_out = std::cout) const;

  /**
   * Create FSM.
   * rng         : The global random number generator.
   * sng         : The solver seed generator.
   * trace       : The outputstream for the API trace.
   * smt2_out    : The output stream for SMT-LIB output, if enabled.
   * record_stats: True to record statistics.
   */
  FSM create_fsm(RNGenerator& rng,
                 SolverSeedGenerator& sng,
                 std::ostream& trace,
                 std::ostream& smt2_out,
                 bool record_stats,
                 bool in_untrace_replay_mode) const;

  /**
   * Auxiliary helper for run().
   * Forks in case that we run forked (continuous testing, delta debugging).
   *
   * seed               : The current seed for the RNG.
   * double             : The time limit for one test run.
   * file_out           : The file to write stdout output of a test run to.
   * file_err           : The file to write stderr output of a test run to.
   * api_trace_file_name: When non-empty, trace is immediately written to file
   *                      if 'run_forked' is false. Else, 'api_trace_file_name'
   *                      is set to the name of the temp trace file name and
   *                      its contents are copied to the final trace file in
   *                      run(), after run_aux() is finished.
   * untrace_file_name  : When non-empty, the name of the trace file to replay.
   * run_forked         : True if test run is executed in a child process.
   * record_stats       : True if statistics for this test run should be
   *                      recorded. This should only be true for main test
   *                      runs, not for replayed runs or delta debugging runs.
   * trace_mode         : The trace mode for this run.
   *
   * Returns a result that indicates the status of the test run.
   */
  Result run_aux(uint64_t seed,
                 double time,
                 const std::string& file_out,
                 const std::string& file_err,
                 std::string& api_trace_file_name,
                 const std::string& untrace_file_name,
                 bool run_forked,
                 bool record_stats,
                 TraceMode trace_mode,
                 std::string& error_msg);

  /**
   * Replay a single test run.
   *
   * seed               : The current seed for the RNG.
   * out_file_name      : The name of the file to write stdout output to.
   * err_file_name      : The name of the file to write stderr output to.
   * api_trace_file_name: The name of the file to write the API trace to.
   * untrace_file_name  : The name of the trace file to replay.
   *
   * Returns a result that indicates the status of the test run.
   */
  Result replay(uint64_t seed,
                const std::string& out_file_name,
                const std::string& err_file_name,
                const std::string& api_trace_file_name,
                const std::string& untrace_file_name);

  /** Filter error messages based on filter regex provided in solver profile. */
  std::string filter_error(const std::string& err);

  /** Register error to d_errors. */
  std::tuple<Murxla::ErrorKind, const std::string, uint64_t, uint64_t>
  add_error(const std::string& err, uint64_t seed);

  /** Load solver profile of currently configured solver. */
  void load_solver_profile();

  std::string get_smt2_file_name(uint64_t seed,
                                 const std::string& untrace_file_name) const;

  /** Statistics of current test run(s). */
  statistics::Statistics* d_stats;
  /** Map normalized error message to pair (original error message, seeds). */
  ErrorMap* d_errors;

  std::unordered_set<std::string> d_exclude_errors;
  std::vector<std::string> d_error_filters;

  std::unique_ptr<SolverProfile> d_solver_profile;

  /** Stores error messages to be exported when --export-errors is enabled. */
  std::vector<std::string> d_export_errors;
};

/* -------------------------------------------------------------------------- */

}  // namespace murxla
#endif
