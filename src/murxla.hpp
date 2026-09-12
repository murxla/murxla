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
#include <csignal>
#include <cstdint>
#include <functional>
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

  /**
   * Stable, content-derived id of this error group, see
   * `Murxla::error_group_id()`. Doubles as the name of the directory the
   * group's traces are written to, see `Murxla::error_group_dir()`.
   */
  uint64_t id;
  /**
   * The representative error message of this group, i.e. the (filtered)
   * message of the first error that was assigned to it. All further errors
   * are matched against this message, and it alone determines `id`.
   */
  std::string errmsg;
  std::vector<uint64_t> seeds;
  /**
   * The output directories the group was restored from, see
   * `Murxla::load_state()`. Empty for a group that was discovered by the
   * current run. Usually a single directory (the one named after `id`), but
   * a group can be spread over several, e.g. when a directory from an older
   * version of Murxla holds the same error.
   *
   * Only used by `recheck_state()`, which needs to find the group's trace
   * files and the directories to move when the error is gone.
   */
  std::vector<std::string> dirs;
};

/** The verdict `Murxla::recheck_state()` arrived at for an error group. */
enum class RecheckStatus
{
  /** One of the group's traces still triggers an error of this group. */
  LIVE,
  /** All of the group's traces ran through without an error. */
  FIXED,
  /**
   * Neither: no trace triggered an error of this group, but at least one did
   * not run through cleanly either (it timed out, could not be replayed, now
   * triggers a different error, or was recorded with a configuration the
   * current run does not reproduce). The group is kept.
   */
  INCONCLUSIVE,
};

/** The outcome of rechecking a single error group. */
struct RecheckInfo
{
  /** The id of the rechecked group. */
  uint64_t id;
  /** The representative error message of the group. */
  std::string errmsg;
  /** The number of seeds recorded for the group. */
  size_t nseeds;
  /** The number of traces that were replayed. */
  size_t nreplayed;
  /** The verdict. */
  RecheckStatus status;
  /**
   * A short human-readable reason for the verdict, empty if there is nothing
   * to add to it. For FIXED groups this is where the traces were moved to,
   * for INCONCLUSIVE ones why the group is kept.
   */
  std::string detail;
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

  /**
   * Upper bound on the payload size of an RPC message, chosen to be far
   * beyond any real error message.
   *
   * The length is read from the message header, so a desynchronized pipe --
   * a worker killed in the middle of writing a message, say -- would
   * otherwise turn four arbitrary bytes into a multi-gigabyte allocation.
   * A length above this bound is treated as a protocol error, which the
   * readers report the same way as a closed pipe.
   */
  inline static constexpr uint32_t RPC_MAX_PAYLOAD = 16u * 1024 * 1024;

  /**
   * Worker-side: send a LOG message to the coordinator. The coordinator
   * writes the bytes verbatim to stdout (interleaved with its aggregate
   * status line). Used so workers never write to stdout themselves.
   */
  void log_via_rpc(const std::string& s);

  inline static const std::string API_TRACE = "tmp-api.trace";
  inline static const std::string SMT2_FILE = "tmp-smt2.smt2";

  /**
   * Name of the directory, relative to the output directory, that
   * `recheck_state()` moves the traces of fixed error groups to.
   */
  inline static const std::string FIXED_DIR = "fixed";

  /** Number of hex digits in an error group directory name. */
  inline static constexpr size_t ERROR_GROUP_ID_DIGITS = 12;

  /**
   * The signal number recorded by the SIGINT handler, or 0.
   *
   * The handler restricts itself to async-signal-safe work and sets this
   * instead of shutting down itself. The fuzzing loops poll it and return,
   * so that printing the error summary and removing the temporary directory
   * happen on the regular exit path, where allocating and doing I/O is
   * actually allowed.
   */
  static volatile sig_atomic_t s_caught_signal;

  /**
   * Compute the stable id of the error group represented by `normalized_err`.
   *
   * Error grouping is fuzzy (see `insert_error()`), so the hash of an
   * arbitrary group member is not a group identity. The id is therefore
   * always derived from the group's *representative* message, i.e. the first
   * message that was assigned to the group.
   *
   * The message is stripped of trailing whitespace before hashing. This is
   * required for the id to survive a round-trip through `error.txt`, which
   * stores the representative message stripped (see `test()`).
   */
  static uint64_t error_group_id(const std::string& normalized_err);

  /**
   * Name of the directory holding the traces of error group `id`, relative to
   * the output directory.
   */
  static std::string error_group_dir(uint64_t id);

  /**
   * Rehydrate the error map from the error groups already present in the
   * output directory, so that a new run continues where a previous one left
   * off instead of re-reporting known errors into colliding directories.
   *
   * A group directory serializes its own state: `<group>/error.txt` holds
   * the representative message (which yields both the map key and the group
   * id) and the seeds are recoverable from the `murxla-<seed>.trace` file
   * names. No separate state file is involved, which means deleting a group
   * directory reliably forgets that error and merging output directories
   * from several hosts is a plain copy of the group directories.
   *
   * Groups are keyed by content, not by directory name, so directories from
   * older versions of Murxla (which named them `1`, `2`, ...) are picked up
   * as well and their errors are recognized as known. Note that new traces
   * for such a group are written to the content-derived directory, which
   * never receives an `error.txt` of its own (that is only written for a
   * newly discovered error), so those traces are not restored again later.
   * Only the directory named after the group id is fully self-describing.
   */
  void load_state();

  /**
   * Replay the traces of the error groups `load_state()` restored and forget
   * the groups whose error is gone, e.g. because the solver has been fixed
   * since the group was recorded.
   *
   * A group's traces are replayed (minimized traces first) until one of them
   * triggers an error that belongs to this group again, which leaves the
   * group untouched. If none does, and all of them ran through without an
   * error, the group is dropped from the error map and its directories are
   * moved to `fixed/` below the output directory. `fixed/` is not itself an
   * error group directory, so later runs neither restore nor recheck what
   * ended up there, and if the error resurfaces it is recorded from scratch.
   *
   * Anything in between -- a trace that times out, one that can no longer be
   * replayed, one that now triggers a *different* error, one that was
   * recorded with solver options the current run does not use -- is not
   * enough to call the error fixed, so the group is kept (`INCONCLUSIVE`).
   *
   * Must be called after `load_state()` and before fuzzing starts: groups
   * discovered by the current run have no trace files on disk to replay yet.
   * `on_group`, if set, is invoked with the outcome of each group as soon as
   * it is available, so the caller can report progress; the outcomes are
   * also returned, in the order the groups were rechecked.
   */
  std::vector<RecheckInfo> recheck_state(
      const std::function<void(const RecheckInfo&)>& on_group = nullptr);

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
   * minimize           : True if the replayed trace should be delta debugged
   *                      (if delta debugging is enabled). This should only be
   *                      false for traces of errors we have already minimized
   *                      a trace for, i.e., duplicates of a known error.
   * min_trace_file_name: If non-null and the trace is delta debugged, stores
   *                      the name of the minimized trace file.
   *
   * Returns a result that indicates the status of the test run.
   */
  Result replay(uint64_t seed,
                const std::string& out_file_name,
                const std::string& err_file_name,
                const std::string& api_trace_file_name,
                const std::string& untrace_file_name,
                bool minimize                    = true,
                std::string* min_trace_file_name = nullptr);

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
   * Look up the error group `normalized_err` belongs to.
   *
   * Returns `d_errors->end()` if the message does not match any known group.
   */
  ErrorMap::iterator find_error(const std::string& normalized_err);

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

  /** Load solver profile of currently configured solver. */
  void load_solver_profile();

  /** Write the errors collected for --export-errors to their JSON file. */
  void export_errors() const;

  /**
   * Add the error group stored in directory `dir` to `d_errors`.
   *
   * Returns false if `dir` does not hold an error group, i.e. if it has no
   * readable, non-empty `error.txt`.
   */
  bool load_error_group(const std::string& dir);

  /**
   * Collect the trace files of the error group `e_info` as (seed, path)
   * pairs, in the order `recheck_state()` replays them: minimized traces
   * first (they are the cheapest to replay), then by seed, so that the
   * recheck of a group does not depend on directory iteration order.
   */
  std::vector<std::pair<uint64_t, std::string>> error_group_traces(
      const ErrorInfo& e_info) const;

  /** Recheck a single error group, see `recheck_state()`. */
  RecheckInfo recheck_error_group(const ErrorInfo& e_info,
                                  const std::string& err_file_name);

  /**
   * Move the directories of error group `e_info` to `fixed/` below the output
   * directory.
   *
   * Returns true if all of them were moved. `moved` is set to the paths the
   * traces ended up in and `err` to why the first directory that could not be
   * moved was left behind. A group can be spread over several directories, so
   * both can be non-empty at once.
   */
  bool move_error_group_to_fixed(const ErrorInfo& e_info,
                                 std::string& moved,
                                 std::string& err) const;

  /** Drop error group `e_norm` from the error map (and the exported errors). */
  void forget_error_group(const std::string& e_norm, const std::string& errmsg);

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
