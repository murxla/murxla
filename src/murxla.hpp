#ifndef __MURXLA__MURXLA_H
#define __MURXLA__MURXLA_H

#include <cstdint>
#include <string>

#include "solver_option.hpp"
#include "theory.hpp"

namespace murxla {

namespace statistics {
class Statistics;
};

class Murxla
{
 public:
  using ErrorMap =
      std::unordered_map<std::string,
                         std::pair<std::string, std::vector<uint32_t>>>;
  struct Options
  {
    /** The current seed. */
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
    std::string dd_out_string;
    /**
     * Check for occurrence of this string in stderr output (rather than
     * matching against the whole stderr output) when delta debugging.
     */
    std::string dd_err_string;
    /** The file to write the reduced API trace to. */
    std::string dd_trace_file_name;

    /** The name of the solver to cross-check given solver with. */
    std::string cross_check;

    /** The name of the options file of the enabled solver. */
    std::string solver_options_file;

    /** The list of currently enabled theories. */
    TheoryIdVector enabled_theories;
  };

  enum Result
  {
    RESULT_ERROR,
    RESULT_ERROR_CONFIG,
    RESULT_OK,
    RESULT_TIMEOUT,
    RESULT_UNKNOWN,
  };

  static std::string get_info(Result res);
  static std::string DD_PREFIX;
  static std::string SOLVER_BTOR;
  static std::string SOLVER_BZLA;
  static std::string SOLVER_CVC5;
  static std::string SOLVER_SMT2;
  static std::string SOLVER_YICES;
  static constexpr int32_t SMT2_READ_END  = 0;
  static constexpr int32_t SMT2_WRITE_END = 1;

  Murxla(statistics::Statistics* stats,
         SolverOptions* solver_options,
         ErrorMap* error_map,
         const std::string& tmp_dir);
  Murxla(statistics::Statistics* stats,
         const Options& options,
         SolverOptions* solver_options,
         ErrorMap* error_map,
         const std::string& tmp_dir);

  Result run(bool run_forked, std::string file_out, std::string file_err);

  void test();

  void dd();

  Options d_options;
  SolverOptions* d_solver_options;
  std::string d_tmp_dir;

 private:
  // void init_statistics();

  Result run_aux(bool run_forked, std::string file_out, std::string file_err);

  Result replay(std::string& out_file_name, std::string& err_file_name);

  bool add_error(const std::string& err, uint32_t seed);

  statistics::Statistics* d_stats;

  /** Map normalized error message to pair (original error message, seeds). */
  ErrorMap* d_errors;
};

std::ostream& operator<<(std::ostream& out, const Murxla::Result& res);

}  // namespace murxla
#endif
