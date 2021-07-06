#ifndef __MURXLA__MURXLA_H
#define __MURXLA__MURXLA_H

#include <cstdint>
#include <string>

#include "options.hpp"
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
