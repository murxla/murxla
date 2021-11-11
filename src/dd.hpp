#ifndef __MURXLA__DD_H
#define __MURXLA__DD_H

#include <cstdint>
#include <string>
#include <vector>

#include "action.hpp"
#include "result.hpp"

namespace murxla {

class Murxla;

class DD
{
 public:
  /** The default file name prefix used for reduced trace files. */
  inline static const std::string TRACE_PREFIX = "murxla-dd-";
  /** The default api trace file name for temporary trace files. */
  inline static const std::string API_TRACE    = "tmp-dd-api.trace";

  /**
   * Constructor.
   *
   * murxla: The associated Murxla instance.
   * seed  : The seed for the RNG.
   * time  : The time limit for one test run.
   */
  DD(Murxla* murxla, uint32_t seed, double time);

  /**
   * Delta debug a given api trace.
   *
   * input_trace_file_name  : The name of the api trace file to minimize.
   * reduced_trace_file_name: The name of the resulting reduced trace, may be
   *                          empty.
   */
  void run(const std::string& input_trace_file_name,
           std::string reduced_trace_file_name);

 private:
  bool minimize_lines(Result golden_exit,
                      const std::vector<std::vector<std::string>>& lines,
                      std::vector<size_t>& included_lines,
                      const std::string& input_trace_file_name);

  bool minimize_line(Result golden_exit,
                     std::vector<std::vector<std::string>>& lines,
                     const std::vector<size_t>& included_lines,
                     const std::string& input_trace_file_name);

  bool minimize_line_aux(Result golden_exit,
                         std::vector<std::vector<std::string>>& lines,
                         const std::vector<size_t>& included_lines,
                         const std::string& input_trace_file_name,
                         size_t n_args,
                         const std::vector<std::tuple<uint32_t,
                                                      size_t,
                                                      Action::Kind,
                                                      std::vector<std::string>,
                                                      size_t>>& to_minimize);

  bool substitute_terms(Result golden_exit,
                        std::vector<std::vector<std::string>>& lines,
                        std::vector<size_t>& included_lines,
                        const std::string& input_trace_file_name);

  std::vector<size_t> test(Result golden_exit,
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

}  // namespace murxla

#endif
