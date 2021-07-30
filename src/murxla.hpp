#ifndef __MURXLA__MURXLA_H
#define __MURXLA__MURXLA_H

#include <cstdint>
#include <string>

#include "action.hpp"
#include "options.hpp"
#include "solver_option.hpp"
#include "theory.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

namespace statistics {
class Statistics;
};
class Solver;

/* -------------------------------------------------------------------------- */

class Murxla
{
 public:
  using ErrorMap =
      std::unordered_map<std::string,
                         std::pair<std::string, std::vector<uint32_t>>>;

  enum Result
  {
    RESULT_ERROR,
    RESULT_ERROR_CONFIG,
    RESULT_OK,
    RESULT_TIMEOUT,
    RESULT_UNKNOWN,
  };

  enum TraceMode
  {
    NONE,
    TO_STDOUT,
    TO_FILE,
  };

  inline static const std::string SOLVER_BTOR  = "btor";
  inline static const std::string SOLVER_BZLA  = "bzla";
  inline static const std::string SOLVER_CVC5  = "cvc5";
  inline static const std::string SOLVER_SMT2  = "smt2";
  inline static const std::string SOLVER_YICES = "yices";

  inline static const std::string API_TRACE = "tmp-api.trace";
  inline static const std::string SMT2_FILE = "tmp-smt2.smt2";

  Murxla(statistics::Statistics* stats,
         const Options& options,
         SolverOptions* solver_options,
         ErrorMap* error_map,
         const std::string& tmp_dir);

  Result run(uint32_t seed,
             double time,
             const std::string& file_out,
             const std::string& file_err,
             const std::string& api_trace_file_name,
             const std::string& untrace_file_name,
             bool run_forked,
             bool record_stats,
             TraceMode trace_mode);

  void test();

  Solver* create_solver(RNGenerator& rng, std::ostream& smt2_out = std::cout);

  const Options& d_options;
  SolverOptions* d_solver_options;
  /** The directory for temp files. */
  std::string d_tmp_dir;

 private:
  Solver* new_solver(RNGenerator& rng,
                     const std::string& solver_name,
                     std::ostream& smt2_out = std::cout);

  /**
   * api_trace_file_name: If given, trace is immediately written to file if
   *                      'run_forked' is false. Else, 'api_trace_file_name' is
   *                      set to the name of the temp trace file name and its
   *                      contents are copied to the final trace file in run(),
   *                      after run_aux() is finished.
   * run_forked         : True if test run is executed in a child process.
   */
  Result run_aux(uint32_t seed,
                 double time,
                 const std::string& file_out,
                 const std::string& file_err,
                 std::string& api_trace_file_name,
                 const std::string& untrace_file_name,
                 bool run_forked,
                 bool record_stats,
                 TraceMode trace_mode);

  Result replay(uint32_t seed,
                const std::string& out_file_name,
                const std::string& err_file_name,
                const std::string& api_trace_file_name,
                const std::string& untrace_file_name);

  bool add_error(const std::string& err, uint32_t seed);

  statistics::Statistics* d_stats;

  /** Map normalized error message to pair (original error message, seeds). */
  ErrorMap* d_errors;
};

std::ostream& operator<<(std::ostream& out, const Murxla::Result& res);

/* -------------------------------------------------------------------------- */

class MurxlaDD
{
 public:
  inline static const std::string TRACE_PREFIX = "murxla-dd-";
  inline static const std::string API_TRACE    = "tmp-dd-api.trace";

  MurxlaDD(Murxla* murxla, uint32_t seed, double time);

  void dd(const std::string& api_trace_file_name,
          const std::string& input_trace_file_name,
          std::string reduced_trace_file_name);

 private:
  bool minimize_lines(Murxla::Result golden_exit,
                      const std::vector<std::vector<std::string>>& lines,
                      std::vector<size_t>& included_lines,
                      const std::string& input_trace_file_name);

  bool minimize_line(Murxla::Result golden_exit,
                     std::vector<std::vector<std::string>>& lines,
                     const std::vector<size_t>& included_lines,
                     const std::string& input_trace_file_name);

  bool minimize_line_aux(
      Murxla::Result golden_exit,
      std::vector<std::vector<std::string>>& lines,
      const std::vector<size_t>& included_lines,
      const std::string& input_trace_file_name,
      size_t n_args,
      const std::vector<
          std::tuple<size_t, Action::Kind, std::vector<std::string>, size_t>>&
          to_minimize);

  bool substitute_terms(Murxla::Result golden_exit,
                        std::vector<std::vector<std::string>>& lines,
                        std::vector<size_t>& included_lines,
                        const std::string& input_trace_file_name);

  std::vector<size_t> test(Murxla::Result golden_exit,
                           const std::vector<std::vector<std::string>>& lines,
                           const std::vector<size_t>& superset,
                           const std::string& input_trace_file_name);

  /** The associated Murxla instance. */
  Murxla* d_murxla = nullptr;
  /** The directory for output files (default: current). */
  std::string d_out_dir = "";
  /** The directory for temp files. */
  std::string d_tmp_dir;
  /** The current seed for the RNG. */
  uint32_t d_seed;
  /** The time limit for one test run. */
  double d_time;

  /** Number of tests performed while delta debugging. */
  uint64_t d_ntests = 0;
  /** Number of successful tests performed while delta debugging. */
  uint64_t d_ntests_success = 0;
  /** The output file name for the initial dd test run. */
  std::string d_gold_out_file_name;
  /** The error output file name for the initial dd test run. */
  std::string d_gold_err_file_name;
  /** The temp trace file name for dd. */
  std::string d_tmp_trace_file_name;
};

/* -------------------------------------------------------------------------- */

}  // namespace murxla
#endif
