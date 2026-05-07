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

#include <atomic>
#include <cstdint>
#include <regex>
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

/**
 * Per-process aggregation counters for `-j/--jobs` parallel fuzzing.
 *
 * Lives in MAP_ANONYMOUS|MAP_SHARED memory so all worker processes and the
 * coordinator see the same counters. Workers `fetch_add` after each iteration;
 * the coordinator reads to render the aggregate status line.
 */
struct Aggregate
{
  std::atomic<uint64_t> num_runs;
  std::atomic<uint64_t> num_timeouts;
  std::atomic<uint64_t> last_seed;
};

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

  enum class ErrorKind
  {
    DUPLICATE, /* Error message is a duplicate since it was already reported. */
    ERROR,     /* Error message is new. */
    FILTER,    /* Error message filtered out. */
  };

  enum TraceMode
  {
    NONE,
    TO_STDOUT,
    TO_FILE,
  };

  /**
   * Role of this Murxla instance with respect to `-j/--jobs` parallel fuzzing.
   *
   * SOLO        : Single-process mode (default; behavior identical to before
   *               the -j flag was added).
   * COORDINATOR : This is the coordinator process; it owns the canonical
   *               error map and stdout, and serves RPC requests from workers.
   *               `Murxla::test()` is NOT called on a coordinator instance.
   * WORKER      : Worker process forked from the coordinator. Runs its own
   *               `test()` loop; reports errors and log lines via RPC pipes.
   */
  enum class Role
  {
    SOLO,
    COORDINATOR,
    WORKER,
  };

  /** RPC message types between workers and the coordinator. */
  enum class RpcMsg : uint8_t
  {
    ADD_ERROR = 1,
    LOG       = 2,
  };

  /** Reply payload from coordinator to worker for ADD_ERROR. */
  struct RpcErrorReply
  {
    uint8_t kind; /* ErrorKind cast to uint8_t */
    uint64_t error_id;
    uint64_t nduplicates;
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

  /**
   * Set the role and the RPC pipe file descriptors for this Murxla instance.
   *
   * For workers: `rpc_req_fd` is the worker→coordinator request pipe and
   * `rpc_resp_fd` is the coordinator→worker reply pipe (both write/read by
   * this process respectively).
   *
   * For coordinators: file descriptors are unused (-1); the coordinator
   * keeps its own bookkeeping in main.cpp.
   *
   * Also wires up the shared `Aggregate` struct used for cross-process
   * status counters.
   */
  void set_parallel_role(Role role,
                         int rpc_req_fd,
                         int rpc_resp_fd,
                         Aggregate* aggregate);

  /**
   * Coordinator-side handler for an ADD_ERROR request. Reads the request
   * payload from `req_fd`, runs the canonical dedup against `g_errors`, and
   * writes the reply to `resp_fd`. Returns true on success, false if the
   * worker closed its end of the pipe (EOF).
   */
  bool serve_rpc_add_error(int req_fd, int resp_fd);

  /**
   * Coordinator-side dedup tail used by the parallel-fuzzing coordinator.
   *
   * This is the same logic as the non-FILTER tail of `add_error()`: walks
   * `d_errors` for a fuzzy match and either appends the seed (DUPLICATE) or
   * inserts a new entry (ERROR). The error message must already have been
   * filtered/normalized via `prefilter_error()`.
   */
  std::tuple<Murxla::ErrorKind, uint64_t, uint64_t> insert_error(
      const std::string& filtered_err,
      const std::string& normalized_err,
      uint64_t seed);

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

  /**
   * Returns true if the given stderr line matches any of the regex patterns
   * configured via `errors::exclude-lines` in the solver profile.
   */
  bool is_excluded_error_line(const std::string& line) const;

  /** Register error to d_errors. */
  std::tuple<Murxla::ErrorKind, const std::string, uint64_t, uint64_t>
  add_error(const std::string& err, uint64_t seed);

  /**
   * Filter prologue extracted from `add_error()`. Runs `filter_error` plus
   * the immutable solver-profile exclude regexes / 5%-diff exclude check.
   *
   * Returns:
   *   - `(FILTER, filtered_err, "")` if the error should be dropped, OR
   *   - `(ERROR,  filtered_err, normalized_err)` otherwise (caller must
   *     proceed to the dedup step, either locally for SOLO/COORDINATOR or
   *     via RPC for WORKER).
   */
  std::tuple<Murxla::ErrorKind, std::string, std::string> prefilter_error(
      const std::string& err);

  /**
   * Worker-side: send an ADD_ERROR RPC request to the coordinator and
   * block on the reply. The coordinator runs the canonical dedup and
   * returns the assigned error id.
   */
  std::tuple<Murxla::ErrorKind, uint64_t, uint64_t> add_error_via_rpc(
      const std::string& filtered_err,
      const std::string& normalized_err,
      uint64_t seed);

  /**
   * Worker-side: send a LOG message to the coordinator. The coordinator
   * writes the bytes verbatim to stdout (interleaved with its aggregate
   * status line). Used so workers never write to stdout themselves.
   */
  void log_via_rpc(const std::string& s);

  /** Load solver profile of currently configured solver. */
  void load_solver_profile();

  std::string get_smt2_file_name(uint64_t seed,
                                 const std::string& untrace_file_name) const;

  std::string get_api_trace_file_name(uint64_t seed,
                                      uint64_t error_id = 0) const;

  /** Statistics of current test run(s). */
  statistics::Statistics* d_stats;
  /** Map normalized error message to pair (original error message, seeds). */
  ErrorMap* d_errors;

  std::unordered_set<std::string> d_exclude_errors;
  std::vector<std::string> d_error_filters;
  std::vector<std::regex> d_excluded_error_lines;

  std::unique_ptr<SolverProfile> d_solver_profile;

  /** Stores error messages to be exported when --export-errors is enabled. */
  std::vector<std::string> d_export_errors;

  /** Role of this instance (SOLO unless `-j>1` is in effect). */
  Role d_role = Role::SOLO;
  /** Worker-side: write end of the worker→coordinator pipe. */
  int d_rpc_req_fd = -1;
  /** Worker-side: read end of the coordinator→worker pipe. */
  int d_rpc_resp_fd = -1;
  /** Pointer to shared Aggregate counters; null in SOLO mode. */
  Aggregate* d_aggregate = nullptr;
};

/* -------------------------------------------------------------------------- */

}  // namespace murxla
#endif
