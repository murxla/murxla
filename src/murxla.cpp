#include "murxla.hpp"

#include <fcntl.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include <filesystem>
#include <fstream>
#include <iomanip>
#include <regex>

#include "btor_solver.hpp"
#include "bzla_solver.hpp"
#include "cross_check_solver.hpp"
#include "cvc5_solver.hpp"
#include "except.hpp"
#include "fsm.hpp"
#include "smt2_solver.hpp"
#include "statistics.hpp"
#include "util.hpp"
#include "yices_solver.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

namespace {

std::string
get_api_trace_file_name(uint32_t seed,
                        bool is_dd,
                        std::string untrace_file_name = "")
{
  if (untrace_file_name.empty())
  {
    std::stringstream ss;
    ss << "murxla-" << seed << ".trace";
    return ss.str();
  }
  if (is_dd)
  {
    std::stringstream ss;
    ss << "murxla-dd-tmp-" << untrace_file_name;
    return ss.str();
  }
  return DEVNULL;
}

/**
 * Removes memory addresses and ==...== from ASAN messages.
 */
std::string
normalize_asan_error(const std::string& s)
{
  std::vector<std::string> regex = {"0x[0-9a-fA-F]+", "==[0-9]+=="};

  std::string res, cur_s(s);
  for (const auto& re : regex)
  {
    res.clear();
    std::regex_replace(std::back_inserter(res),
                       cur_s.begin(),
                       cur_s.end(),
                       std::regex(re),
                       "");
    cur_s = res;
  }

  return res;
}

/**
 * Split string into tokens.
 */
std::vector<std::string>
str_tokenize(const std::string& s)
{
  std::istringstream buf(s);
  std::vector<std::string> ret{std::istream_iterator<std::string>(buf),
                               std::istream_iterator<std::string>()};
  return ret;
}

/**
 * Count the number of non-digit characters two strings differ in.
 */
size_t
str_diff(const std::string& s1, const std::string& s2)
{
  size_t diff;
  auto t1 = str_tokenize(s1);
  auto t2 = str_tokenize(s2);

  if (t1.size() > t2.size())
  {
    std::swap(t1, t2);
  }

  diff = t2.size() - t1.size();
  for (size_t i = 0; i < t1.size(); ++i)
  {
    if (t1[i] != t2[i])
    {
      // Ignore numbers for diff.
      for (size_t j = 0; j < t1[i].size(); ++j)
      {
        if (std::isdigit(t1[i][j])) continue;
        ++diff;
      }
    }
  }
  return diff;
}

/**
 * Write trace lines to output file.
 *
 * A trace is represented as a vector of lines and a line is represented as a
 * vector of strings with at most 2 elements.
 *
 * Trace statements that do not expect a return statement are represented as a
 * line (vector) with one element. Trace statements that expect a return
 * statement are represented as a line (vector) with two elements: the action
 * and the return statement.
 *
 * This function writes only the lines at the indices given in 'indices'
 * to the output file.
 *
 * This is only used for delta debugging traces.
 */
void
write_lines_to_file(const std::vector<std::vector<std::string>>& lines,
                    const std::vector<size_t> indices,
                    const std::string& out_file_name)
{
  size_t size            = lines.size();
  std::ofstream out_file = open_output_file(out_file_name, false);
  for (size_t idx : indices)
  {
    assert(idx < size);
    assert(lines[idx].size() > 0);
    assert(lines[idx].size() <= 2);
    out_file << lines[idx][0];
    if (lines[idx].size() == 2)
    {
      out_file << std::endl << lines[idx][1];
    }
    out_file << std::endl;
  }
  out_file.close();
}

/**
 * Remove subsets listed in 'excluded_sets' from the list of 'subsets'.
 *
 * Excluded sets are given as indices of the list of subsets.
 * A subset is a set of indices (line, token) itself.
 *
 * This is only used for delta debugging traces.
 */
std::vector<size_t>
remove_subsets(std::vector<std::vector<size_t>>& subsets,
               std::unordered_set<size_t>& excluded_sets)
{
  std::vector<size_t> res;

  for (size_t i = 0, n = subsets.size(); i < n; ++i)
  {
    if (excluded_sets.find(i) != excluded_sets.end()) continue;
    res.insert(res.end(), subsets[i].begin(), subsets[i].end());
  }
  return res;
}

/**
 * Split set 'superset' into chunks of size 'subset_size'.
 *
 * Last subset will contain the remaining m > subset_size lines if subset_size
 * does not divide superset.size().
 */
std::vector<std::vector<size_t>>
split_superset(const std::vector<size_t> superset, uint32_t subset_size)
{
  std::vector<std::vector<size_t>> subsets;
  uint32_t superset_size = superset.size();
  auto begin             = superset.begin();
  auto end               = superset.begin();
  for (int64_t lo = 0; end != superset.end(); lo += subset_size)
  {
    int64_t hi = lo + subset_size;
    end        = hi > superset_size || (superset_size - hi) < subset_size
                     ? superset.end()
                     : begin + hi;
    std::vector<size_t> subset(begin + lo, end);
    subsets.push_back(subset);
  }
  assert(subsets.size() == (size_t) superset_size / subset_size);
  return subsets;
}
}  // namespace

/* -------------------------------------------------------------------------- */

Murxla::Murxla(statistics::Statistics* stats,
               const Options& options,
               SolverOptions* solver_options,
               ErrorMap* error_map,
               const std::string& tmp_dir)
    : d_options(options),
      d_solver_options(solver_options),
      d_tmp_dir(tmp_dir),
      d_stats(stats),
      d_errors(error_map)
{
  assert(stats);
  assert(solver_options);
}

Murxla::Result
Murxla::run(uint32_t seed,
            double time,
            const std::string& file_out,
            const std::string& file_err,
            const std::string& api_trace_file_name,
            const std::string& untrace_file_name,
            bool run_forked,
            bool record_stats,
            Murxla::TraceMode trace_mode)
{
  std::string tmp_file_out = get_tmp_file_path("run-tmp1.out", d_tmp_dir);
  std::string tmp_file_err = get_tmp_file_path("run-tmp1.err", d_tmp_dir);

  std::string tmp_api_trace_file_name;
  Result res = run_aux(seed,
                       time,
                       tmp_file_out,
                       tmp_file_err,
                       tmp_api_trace_file_name,
                       untrace_file_name,
                       run_forked,
                       record_stats,
                       trace_mode);

  if (trace_mode == TO_FILE)
  {
    /* For the SMT2 solver, we only write the SMT2 file (not the trace). */
    if (d_options.solver == Murxla::SOLVER_SMT2)
    {
      std::string smt2_file_name = d_options.smt2_file_name;
      if (smt2_file_name.empty())
      {
        smt2_file_name = get_smt2_file_name(seed, untrace_file_name);
        if (!d_options.out_dir.empty())
        {
          smt2_file_name = prepend_path(d_options.out_dir, smt2_file_name);
        }
      }
      std::string tmp_smt2_file_name = get_tmp_file_path(SMT2_FILE, d_tmp_dir);
      assert(std::filesystem::exists(tmp_smt2_file_name));
      std::filesystem::copy(tmp_smt2_file_name,
                            smt2_file_name,
                            std::filesystem::copy_options::overwrite_existing);
      if (!d_options.dd)
      {
        if (res != RESULT_OK && res != RESULT_TIMEOUT)
        {
          std::cout << smt2_file_name << std::endl;
        }
      }
    }
    /* For all other solvers, we write the trace file. */
    else
    {
      assert(api_trace_file_name != DEVNULL);
      assert(std::filesystem::exists(tmp_api_trace_file_name));
      if (tmp_api_trace_file_name != api_trace_file_name)
      {
        std::filesystem::copy(
            tmp_api_trace_file_name,
            api_trace_file_name,
            std::filesystem::copy_options::overwrite_existing);
      }
      if (!d_options.dd)
      {
        std::cout << (run_forked ? "" : "api trace file: ")
                  << api_trace_file_name << std::endl;
      }
    }
  }

  if (run_forked)
  {
    std::ofstream err = open_output_file(file_err, true);
    std::ofstream out = open_output_file(file_out, true);

    std::ifstream tmp_out = open_input_file(tmp_file_out, true);
    out << tmp_out.rdbuf();
    tmp_out.close();

    std::ifstream tmp_err = open_input_file(tmp_file_err, true);
    err << tmp_err.rdbuf();
    tmp_err.close();

    out.close();
    err.close();
  }
  return res;
}

void
Murxla::test()
{
  uint32_t num_runs         = 0;
  double start_time         = get_cur_wall_time();
  std::string out_file_name = DEVNULL;
  SeedGenerator sg(d_options.seed);

  std::string err_file_name = get_tmp_file_path("tmp.err", d_tmp_dir);

  do
  {
    double cur_time = get_cur_wall_time();

    uint32_t seed = sg.next();

    std::cout << std::setw(10) << seed;
    std::cout << " " << std::setw(5) << num_runs++ << " runs";
    std::cout << " " << std::setw(8);
    std::cout << std::setprecision(2) << std::fixed;
    std::cout << num_runs / (cur_time - start_time) << " r/s";
    std::cout << " " << std::setw(4);
    std::cout << d_stats->d_results[Solver::Result::SAT] << " sat";
    std::cout << " " << std::setw(4);
    std::cout << d_stats->d_results[Solver::Result::UNSAT] << " unsat";
    std::cout << " " << std::setw(4);
    std::cout << d_errors->size() << " errors";
    std::cout << std::flush;

    /* Note: If the selected solver is SOLVER_SMT2 and no online solver is
     *       configured, we'll never run into the error case below and replay
     *       (the Smt2Solver only answers 'unknown' and dumps SMT2 -> should
     *       never terminate with an error).  We therefore dump every generated
     *       sequence to smt2 continuously. */

    /* Run and test for error without tracing to trace file (we by default still
     * trace to stdout here, which is redirected to /dev/null).
     * If error encountered, replay and trace below. */

    std::string api_trace_file_name = d_options.api_trace_file_name;
    if (api_trace_file_name.empty())
    {
      api_trace_file_name = get_api_trace_file_name(
          seed, d_options.dd, d_options.untrace_file_name);
      if (!d_options.out_dir.empty())
      {
        api_trace_file_name =
            prepend_path(d_options.out_dir, api_trace_file_name);
      }
    }
    bool smt2_offline =
        (d_options.solver == SOLVER_SMT2 && d_options.solver_binary.empty());
    Result res =
        run(seed,
            d_options.time,
            out_file_name,
            err_file_name,
            api_trace_file_name,
            d_options.untrace_file_name,
            true,
            true,
            // for the SMT2 offline mode we want to store all SMT2 files
            smt2_offline ? TO_FILE : NONE);

    /* report status */
    if (res == RESULT_OK)
    {
      std::cout << "\33[2K\r" << std::flush;
    }
    else
    {
      /* Read error file and check if we already encounterd the same error. */
      bool duplicate = false;
      if (res == RESULT_ERROR || res == RESULT_ERROR_CONFIG)
      {
        std::ifstream errs = open_input_file(err_file_name, false);
        std::string errmsg, line;
        while (std::getline(errs, line))
        {
          errmsg += line + "\n";
        }
        if (res == RESULT_ERROR)
        {
          duplicate = add_error(errmsg, seed);
        }
        else
        {
          std::cout << "\33[2K\r" << std::flush;
          MURXLA_CHECK_CONFIG(false) << errmsg;
        }
      }

      std::stringstream info;
      info << " [";
      switch (res)
      {
        case RESULT_ERROR:
          if (duplicate)
          {
            info << COLOR_GREEN << "duplicate";
          }
          else
          {
            info << COLOR_RED << "error";
          }
          break;
        case RESULT_ERROR_CONFIG: info << COLOR_RED << "config error"; break;
        case RESULT_TIMEOUT: info << COLOR_BLUE << "timeout"; break;
        default: assert(res == RESULT_UNKNOWN); info << "unknown";
      }
      info << COLOR_DEFAULT << "]";

      std::cout << info.str() << std::flush;
      if (res == RESULT_ERROR)
        std::cout << " ";
      else
        std::cout << std::endl;
    }

    /* Replay and trace on error.
     *
     * If SMT2 solver with online solver configured, dump smt2 on replay.
     * If SMT2 solver configured without an online solver, we'll never enter
     * here (the SMT2 solver should never return an error result). */
    if (res != RESULT_OK && res != RESULT_TIMEOUT && !smt2_offline)
    {
      Result res_replay = replay(seed,
                                 out_file_name,
                                 err_file_name,
                                 api_trace_file_name,
                                 d_options.untrace_file_name);
      assert(res == res_replay);
    }
    std::cout << "\r" << std::flush;
  } while (d_options.max_runs == 0 || num_runs < d_options.max_runs);
}

Murxla::Result
Murxla::replay(uint32_t seed,
               const std::string& out_file_name,
               const std::string& err_file_name,
               const std::string& api_trace_file_name,
               const std::string& untrace_file_name)
{
  Result res = run(seed,
                   0,
                   out_file_name,
                   err_file_name,
                   api_trace_file_name,
                   untrace_file_name,
                   true,
                   false,
                   TO_FILE);

  if (d_options.dd)
  {
    MurxlaDD(this, seed, 0)
        .dd(d_options.api_trace_file_name,
            api_trace_file_name,
            d_options.dd_trace_file_name);
  }
  return res;
}

Solver*
Murxla::new_solver(RNGenerator& rng,
                   const std::string& solver_name,
                   std::ostream& smt2_out)
{
  if (solver_name == SOLVER_BTOR)
  {
#if MURXLA_USE_BOOLECTOR
    return new btor::BtorSolver(rng);
#endif
  }
  else if (solver_name == SOLVER_BZLA)
  {
#if MURXLA_USE_BITWUZLA
    return new bzla::BzlaSolver(rng);
#endif
  }
  else if (solver_name == SOLVER_CVC5)
  {
#if MURXLA_USE_CVC5
    return new cvc5::Cvc5Solver(rng);
#endif
  }
  else if (solver_name == SOLVER_YICES)
  {
#if MURXLA_USE_YICES
    return new yices::YicesSolver(rng);
#endif
  }
  else if (solver_name == SOLVER_SMT2)
  {
    return new smt2::Smt2Solver(rng, smt2_out, d_options.solver_binary);
  }
  MURXLA_CHECK(true) << "no solver created";
  return nullptr;
}

Solver*
Murxla::create_solver(RNGenerator& rng, std::ostream& smt2_out)
{
  Solver* solver = new_solver(rng, d_options.solver, smt2_out);

  if (!d_options.cross_check.empty())
  {
    Solver* reference_solver = new_solver(rng, d_options.cross_check);
    solver = new cross_check::CrossCheckSolver(rng, solver, reference_solver);
  }

  return solver;
}

Murxla::Result
Murxla::run_aux(uint32_t seed,
                double time,
                const std::string& file_out,
                const std::string& file_err,
                std::string& api_trace_file_name,
                const std::string& untrace_file_name,
                bool run_forked,
                bool record_stats,
                Murxla::TraceMode trace_mode)
{
  int32_t status, fd;
  Result result;
  pid_t pid_solver = 0, pid_timeout = 0;
  std::ofstream file_trace, file_smt2;
  std::ostream smt2_out(std::cout.rdbuf());
  std::ostream trace(std::cout.rdbuf());

  if (trace_mode == NONE)
  {
    file_trace = open_output_file(DEVNULL, false);
    trace.rdbuf(file_trace.rdbuf());
    if (d_options.solver == SOLVER_SMT2)
    {
      smt2_out.rdbuf(file_trace.rdbuf());
    }
  }
  else if (trace_mode == TO_FILE)
  {
    /* If we don't run forked and an explicit api trace file name is given,
     * we have to immediately trace into file. Else, we don't get a chance to
     * write the contents from the temp file back to the given file when the
     * process aborts (if the trace triggers an issue). */
    if (run_forked || api_trace_file_name.empty())
    {
      api_trace_file_name = get_tmp_file_path(API_TRACE, d_tmp_dir);
    }
    file_trace = open_output_file(api_trace_file_name, false);
    trace.rdbuf(file_trace.rdbuf());
    if (d_options.solver == SOLVER_SMT2)
    {
      std::string smt2_file_name = get_tmp_file_path(SMT2_FILE, d_tmp_dir);
      file_smt2                  = open_output_file(smt2_file_name, false);
      smt2_out.rdbuf(file_smt2.rdbuf());
    }
  }
  else
  {
    assert(trace_mode == TO_STDOUT);
    /* Disable trace output since we only want SMT2 output on stdout. */
    if (d_options.solver == SOLVER_SMT2)
    {
      file_trace = open_output_file(DEVNULL, false);
      trace.rdbuf(file_trace.rdbuf());
    }
  }

  RNGenerator rng(seed);

  result = RESULT_UNKNOWN;

  /* If seeded, run in main process. */
  if (run_forked)
  {
    pid_solver = fork();

    MURXLA_CHECK(pid_solver >= 0) << "forking solver process failed.";
  }

  /* parent */
  if (pid_solver)
  {
    /* If a time limit is given, fork another process that kills the pid_solver
     * after time seconds. (https://stackoverflow.com/a/8020324) */
    if (time)
    {
      pid_timeout = fork();

      MURXLA_CHECK(pid_timeout >= 0) << "forking timeout process failed";

      if (pid_timeout == 0)
      {
        signal(SIGINT, SIG_DFL);  // reset stats signal handler
        usleep(time * 1000000);
        exit(EXIT_OK);
      }
    }

    /* Wait for the first process to finish (pid_solver or pid_timeout). */
    pid_t exited_pid = wait(&status);

    if (exited_pid == pid_solver)
    {
      /* Kill and collect timeout process if solver process terminated first. */
      if (pid_timeout)
      {
        kill(pid_timeout, SIGKILL);
        waitpid(pid_timeout, nullptr, 0);
      }
      if (WIFEXITED(status))
      {
        switch (WEXITSTATUS(status))
        {
          case EXIT_OK: result = RESULT_OK; break;
          case EXIT_ERROR_CONFIG: result = RESULT_ERROR_CONFIG; break;
          default:
            assert(WEXITSTATUS(status) == EXIT_ERROR);
            result = RESULT_ERROR;
        }
      }
      else if (WIFSIGNALED(status))
      {
        result = RESULT_ERROR;
      }
    }
    else
    {
      /* Kill and collect solver process if time limit is exceeded. */
      assert(pid_timeout);
      kill(pid_solver, SIGKILL);
      waitpid(pid_solver, nullptr, 0);
      result = RESULT_TIMEOUT;
    }
  }
  /* child */
  else
  {
    signal(SIGINT, SIG_DFL);  // reset stats signal handler

    if (run_forked)
    {
      /* Redirect stdout and stderr of child process into given files. */
      fd = open(
          file_out.c_str(), O_CREAT | O_WRONLY | O_TRUNC, S_IRUSR | S_IWUSR);

      MURXLA_EXIT_ERROR_FORK(fd < 0, true)
          << "unable to open file " << file_out;
      dup2(fd, STDOUT_FILENO);
      close(fd);
      fd = open(
          file_err.c_str(), O_CREAT | O_WRONLY | O_TRUNC, S_IRUSR | S_IWUSR);
      if (fd < 0)
      {
        perror(0);
        MURXLA_EXIT_ERROR_FORK(true, true)
            << "unable to open file " << file_err;
      }
      dup2(fd, STDERR_FILENO);
      close(fd);
    }

    try
    {
      /* Dummy statistics object for the cases were we don't want to record
       * statistics (replay, dd). */
      statistics::Statistics dummy_stats;

      bool arith_subtyping = false;
      /* Check if Int is treated as subtype of Real (if supported). */
      {
        /* We need a solver instance for the check (will not be passed to FSM
         * in order to have a fresh instance for the actual run). */
        Solver* solver = create_solver(rng, smt2_out);
        if (solver->supports_theory(THEORY_INT))
        {
          solver->new_solver();
          Sort sort       = solver->mk_sort(SORT_INT);
          arith_subtyping = sort->is_real();
        }
        delete solver;
      }

      FSM fsm(rng,
              create_solver(rng, smt2_out),
              trace,
              *d_solver_options,
              arith_subtyping,
              d_options.arith_linear,
              d_options.trace_seeds,
              d_options.simple_symbols,
              d_options.smt,
              record_stats ? d_stats : &dummy_stats,
              d_options.enabled_theories);
      fsm.configure();

      /* replay/untrace given API trace */
      if (!untrace_file_name.empty())
      {
        fsm.untrace(untrace_file_name);
      }
      /* regular MBT run */
      else
      {
        fsm.run();
      }
    }
    catch (MurxlaConfigException& e)
    {
      MURXLA_EXIT_ERROR_CONFIG_FORK(true, run_forked) << e.get_msg();
    }
    catch (MurxlaException& e)
    {
      MURXLA_EXIT_ERROR_FORK(true, run_forked) << e.get_msg();
    }

    if (file_trace.is_open()) file_trace.close();

    if (run_forked)
    {
      exit(EXIT_OK);
    }
    else
    {
      result = RESULT_OK;
    }
  }

  return result;
}

bool
Murxla::add_error(const std::string& err, uint32_t seed)
{
  bool duplicate       = false;
  std::string err_norm = normalize_asan_error(err);

  for (auto& p : *d_errors)
  {
    const auto& e_norm = p.first;
    auto& seeds        = p.second.second;

    size_t len   = std::max(err_norm.size(), e_norm.size());
    size_t diff  = str_diff(err_norm, e_norm);
    double pdiff = diff / static_cast<double>(len);

    /* Errors are classified as the same error if they differ in at most 5% of
     * characters. */
    if (pdiff <= 0.05)
    {
      seeds.push_back(seed);
      duplicate = true;
      break;
    }
  }

  if (!duplicate)
  {
    std::vector<uint32_t> seeds = {seed};
    d_errors->emplace(err_norm, std::make_pair(err, seeds));
  }

  return duplicate;
}

std::ostream&
operator<<(std::ostream& out, const Murxla::Result& res)
{
  switch (res)
  {
    case Murxla::Result::RESULT_OK: out << "ok"; break;
    case Murxla::Result::RESULT_ERROR: out << "error"; break;
    case Murxla::Result::RESULT_ERROR_CONFIG: out << "config error"; break;
    case Murxla::Result::RESULT_TIMEOUT: out << "timeout"; break;
    default: assert(res == Murxla::Result::RESULT_UNKNOWN); out << "unknown";
  }
  return out;
}

/* -------------------------------------------------------------------------- */

MurxlaDD::MurxlaDD(Murxla* murxla, uint32_t seed, double time)
    : d_murxla(murxla), d_seed(seed), d_time(time)
{
  assert(d_murxla);
  d_gold_out_file_name =
      get_tmp_file_path("tmp-dd-gold.out", d_murxla->d_tmp_dir);
  d_gold_err_file_name =
      get_tmp_file_path("tmp-dd-gold.err", d_murxla->d_tmp_dir);
  d_tmp_trace_file_name =
      get_tmp_file_path("tmp-api-dd.trace", d_murxla->d_tmp_dir);
}

void
MurxlaDD::dd(const std::string& api_trace_file_name,
             const std::string& input_trace_file_name,
             std::string reduced_trace_file_name)
{
  assert(!input_trace_file_name.empty());

  Murxla::Result gold_exit;

  std::string tmp_api_trace_file_name =
      get_tmp_file_path(API_TRACE, d_murxla->d_tmp_dir);
  std::string tmp_input_trace_file_name =
      get_tmp_file_path("tmp-dd.trace", d_murxla->d_tmp_dir);

  MURXLA_MESSAGE_DD << "start minimizing file '"
                    << input_trace_file_name.c_str() << "'";

  /* golden run */
  gold_exit = d_murxla->run(d_seed,
                            d_time,
                            d_gold_out_file_name,
                            d_gold_err_file_name,
                            tmp_input_trace_file_name,
                            input_trace_file_name,
                            true,
                            false,
                            Murxla::TraceMode::TO_FILE);

  MURXLA_MESSAGE_DD << "golden exit: " << gold_exit;
  {
    std::ifstream gold_out_file = open_input_file(d_gold_out_file_name, false);
    std::stringstream ss;
    ss << gold_out_file.rdbuf();
    MURXLA_MESSAGE_DD << "golden stdout output: " << ss.str();
    gold_out_file.close();
  }
  {
    std::ifstream gold_err_file = open_input_file(d_gold_err_file_name, false);
    MURXLA_MESSAGE_DD << "golden stderr output: " << gold_err_file.rdbuf();
    gold_err_file.close();
  }
  if (d_murxla->d_options.dd_ignore_out)
  {
    MURXLA_MESSAGE_DD << "ignoring stdout output";
  }
  if (d_murxla->d_options.dd_ignore_err)
  {
    MURXLA_MESSAGE_DD << "ignoring stderr output";
  }
  if (!d_murxla->d_options.dd_ignore_out
      && !d_murxla->d_options.dd_match_out.empty())
  {
    MURXLA_MESSAGE_DD << "checking for occurrence of '"
                      << d_murxla->d_options.dd_match_out.c_str()
                      << "' in stdout output";
  }
  if (!d_murxla->d_options.dd_ignore_err
      && !d_murxla->d_options.dd_match_err.empty())
  {
    MURXLA_MESSAGE_DD << "checking for occurrence of '"
                      << d_murxla->d_options.dd_match_err.c_str()
                      << "' in stderr output";
  }

  /* Start delta debugging */

  /* Represent input trace as vector of lines.
   *
   * A line is a vector of strings with at most two elements.
   * Trace statements that do not expect a return statement are represented
   * as a line (vector) with one element.  Trace statements that expect a
   * return statement are represented as one line, that is, a vector with two
   * elements: the statement and the return statement.
   */

  std::string line;
  std::vector<std::vector<std::string>> lines;
  std::ifstream trace_file = open_input_file(tmp_input_trace_file_name, false);
  while (std::getline(trace_file, line))
  {
    std::string token;
    if (line[0] == '#') continue;
    if (std::getline(std::stringstream(line), token, ' ') && token == "return")
    {
      std::stringstream ss;
      assert(lines.size() > 0);
      std::vector<std::string>& prev = lines.back();
      prev.push_back(line);
    }
    else
    {
      lines.push_back(std::vector{line});
    }
  }
  trace_file.close();

  uint64_t iterations = 0;
  bool success        = false;
  std::uintmax_t size = std::filesystem::file_size(tmp_input_trace_file_name);
  std::vector<size_t> included_lines(lines.size());
  std::iota(included_lines.begin(), included_lines.end(), 0);

  do
  {
    success = minimize_lines(gold_exit,
                             lines,
                             included_lines,
                             tmp_input_trace_file_name);

    if (iterations > 0 && !success) break;

    success = minimize_line(gold_exit,
                            lines,
                            included_lines,
                            tmp_input_trace_file_name);
    iterations += 1;
  } while (success);

  /* Write minimized trace file to path if given. */
  if (reduced_trace_file_name.empty())
  {
    if (tmp_input_trace_file_name.empty())
    {
      reduced_trace_file_name =
          prepend_prefix_to_file_name(TRACE_PREFIX, api_trace_file_name);
    }
    else
    {
      reduced_trace_file_name =
          prepend_prefix_to_file_name(TRACE_PREFIX, input_trace_file_name);
    }
  }
  if (!d_murxla->d_options.out_dir.empty())
  {
    reduced_trace_file_name =
        prepend_path(d_murxla->d_options.out_dir, reduced_trace_file_name);
  }

  MURXLA_MESSAGE_DD;
  MURXLA_MESSAGE_DD << d_ntests_success << " (of " << d_ntests
                    << ") tests reduced successfully";

  if (std::filesystem::exists(d_tmp_trace_file_name))
  {
    std::filesystem::copy(d_tmp_trace_file_name,
                          reduced_trace_file_name,
                          std::filesystem::copy_options::overwrite_existing);
    MURXLA_MESSAGE_DD << "written to: " << reduced_trace_file_name.c_str();
    MURXLA_MESSAGE_DD << "file reduced to "
                      << ((double) std::filesystem::file_size(
                              reduced_trace_file_name)
                          / size * 100)
                      << "% of original size";
  }
  else
  {
    MURXLA_MESSAGE_DD << "unable to reduce api trace";
  }
}

bool
MurxlaDD::minimize_lines(Murxla::Result golden_exit,
                         const std::vector<std::vector<std::string>>& lines,
                         std::vector<size_t>& included_lines,
                         const std::string& untrace_file_name)
{
  MURXLA_MESSAGE_DD << "Start trying to minimize number of trace lines ...";
  size_t n_lines     = included_lines.size();
  size_t n_lines_cur = n_lines;
  size_t subset_size = n_lines_cur / 2;

  while (subset_size > 0)
  {
    std::vector<std::vector<size_t>> subsets =
        split_superset(included_lines, subset_size);

    std::vector<size_t> superset_cur;
    std::unordered_set<size_t> excluded_sets;
    /* we skip the first subset (will always fail since it contains 'new') */
    for (size_t i = 0, n = subsets.size() - 1; i < n; ++i)
    {
      /* remove subsets from last to first */
      size_t idx = n - i - 1;

      std::unordered_set<size_t> ex(excluded_sets);
      ex.insert(idx);

      std::vector<size_t> tmp_superset = test(golden_exit,
                                              lines,
                                              remove_subsets(subsets, ex),
                                              untrace_file_name);
      if (!tmp_superset.empty())
      {
        superset_cur = tmp_superset;
        excluded_sets.insert(idx);
      }
    }
    if (superset_cur.empty())
    {
      subset_size = subset_size / 2;
    }
    else
    {
      /* write found subset immediately to file and continue */
      write_lines_to_file(lines, superset_cur, d_tmp_trace_file_name);
      included_lines = superset_cur;
      n_lines_cur    = included_lines.size();
      subset_size = n_lines_cur / 2;
      MURXLA_MESSAGE_DD << "number of lines reduced to " << std::fixed
                        << std::setprecision(2)
                        << (((double) included_lines.size()) / lines.size()
                            * 100)
                        << "% of original number";
    }
  }
  return included_lines.size() < n_lines;
}

namespace {

/**
 * Generate a minimized action trace line from the given original tokens and
 * the terms to include.
 *
 * action_kind  : The kind of the action.
 * tokens       : The tokens of the original action line (does not include the
 *                action kind).
 * included_args: The indices of the sorts/terms to include, starting from
 *                index 'idx'.  The indices start from 0 and occur in 'tokens'
 *                at 'idx' + included_terms[i].
 * idx          : The starting index (in 'tokens') of the (term or sort)
 *                argument set to minimize.
 * pre          : The updated set of trace line arguments to print right before
 *                the set of minimized arguments. This contains, for example,
 *                the number of term arguments to 'mk-term'. All trace
 *                arguments before these updated arguments remain unchanged.
 * post         : The updated set of trace line arguments to print right after
 *                the set of minimized arguments. This contains, for example,
 *                the domain sort for an action that creates a function sort.
 */
std::string
generate_minimized_line(Action::Kind action_kind,
                        const std::vector<std::string>& tokens,
                        const std::vector<size_t>& included_args,
                        size_t idx,
                        const std::vector<std::string>& pre,
                        const std::vector<std::string>& post)
{
  std::stringstream ss;
  ss << action_kind;
  for (size_t i = 0, n = idx - pre.size(); i < n; ++i)
  {
    ss << " " << tokens[i];
  }
  for (const std::string& p : pre)
  {
    ss << " " << p;
  }
  for (size_t i : included_args)
  {
    ss << " " << tokens[idx + i];
  }
  for (const std::string& p : post)
  {
    ss << " " << p;
  }

  return ss.str();
}

/**
 * Update lines with their minimized correspondence.
 *
 * lines    : The set of trace lines.  A line is represented as a vector of
 *            strings with at most 2 elements.
 * to_update: Map line number of the line to update to
 *            - its action kind
 *            - its original tokens
 *            - the arguments to include
 *            - the start index of the arguments to minimize
 *
 * return: The previous state of the updated lines as a map from line index to
 *         action line string.
 */
std::unordered_map<size_t, std::string>
update_lines(
    std::vector<std::vector<std::string>>& lines,
    const std::vector<size_t>& included_args,
    const std::vector<
        std::tuple<size_t, Action::Kind, std::vector<std::string>, size_t>>&
        to_update)
{
  std::unordered_map<size_t, std::string> updated_lines_prev;

  for (const auto& t : to_update)
  {
    size_t line_idx    = std::get<0>(t);
    Action::Kind kind  = std::get<1>(t);
    const auto& tokens = std::get<2>(t);
    size_t idx         = std::get<3>(t);

    /* save current state of line in case we need to revert */
    updated_lines_prev[line_idx] = lines[line_idx][0];

    /* determine pre and post terms for generate_minimized_line */
    std::vector<std::string> pre;
    std::vector<std::string> post;

    if (kind == Action::MK_SORT)
    {
      post.push_back(tokens[tokens.size() - 1]);
    }
    else if (kind == Action::MK_TERM && tokens[0] == Op::UF_APPLY)
    {
      pre.push_back(std::to_string((included_args.size() + 1)));
      pre.push_back(tokens[idx - 1]);
    }
    /* update line */
    lines[line_idx][0] =
        generate_minimized_line(kind, tokens, included_args, idx, pre, post);
  }
  return updated_lines_prev;
}
}  // namespace

bool
MurxlaDD::minimize_line_aux(
    Murxla::Result golden_exit,
    std::vector<std::vector<std::string>>& lines,
    const std::vector<size_t>& included_lines,
    const std::string& input_trace_file_name,
    size_t n_args,
    std::vector<
        std::tuple<size_t, Action::Kind, std::vector<std::string>, size_t>>
        to_update)
{
  assert(to_update.size() >= 1);

  bool res = false;

  /* We minimize based on the first line of the lines to update. For example,
   * when minimizing function sorts, that would be the line to create the sort
   * with MK_SORT. */
  size_t line_idx_first   = std::get<0>(to_update[0]);
  Action::Kind kind_first = std::get<1>(to_update[0]);
  auto tokens_first       = std::get<2>(to_update[0]);
  assert(tokens_first.size() >= n_args + 1);

  size_t line_size = lines[line_idx_first][0].size();
  std::vector<size_t> line_superset(n_args);
  std::iota(line_superset.begin(), line_superset.end(), 0);
  uint32_t subset_size = n_args / 2;

  while (subset_size > 0)
  {
    std::vector<std::vector<size_t>> subsets =
        split_superset(line_superset, subset_size);

    std::vector<size_t> cur_line_superset;
    std::unordered_set<size_t> excluded_sets;
    for (size_t i = 0, n = subsets.size(); i < n; ++i)
    {
      std::unordered_set<size_t> ex(excluded_sets);
      ex.insert(i);
      std::vector<size_t> included_args = remove_subsets(subsets, ex);
      if (included_args.size() == 0) continue;

      /* Cache previous state of lines to update and update lines. */
      auto lines_cur = update_lines(lines, included_args, to_update);

      /* test if minimization was successful */
      std::vector<size_t> tmp_superset =
          test(golden_exit, lines, included_lines, input_trace_file_name);

      if (!tmp_superset.empty())
      {
        /* success */
        cur_line_superset = included_args;
        excluded_sets.insert(i);
      }
      else
      {
        /* failure */
        for (auto l : lines_cur)
        {
          lines[l.first][0] = l.second;
        }
      }
    }
    if (cur_line_superset.empty())
    {
      subset_size = subset_size / 2;
    }
    else
    {
      /* write to file and continue */
      write_lines_to_file(lines, included_lines, d_tmp_trace_file_name);
      line_superset = cur_line_superset;
      subset_size   = line_superset.size() / 2;
      res           = true;
      MURXLA_MESSAGE_DD << "line " << line_idx_first << " reduced to "
                        << std::fixed << std::setprecision(2)
                        << (((double) lines[line_idx_first][0].size())
                            / line_size * 100)
                        << "% of original size";
    }
  }
  return res;
}

bool
MurxlaDD::minimize_line_sort_fun(Murxla::Result golden_exit,
                                 std::vector<std::vector<std::string>>& lines,
                                 const std::vector<size_t>& included_lines,
                                 const std::string& input_trace_file_name,
                                 size_t line_idx,
                                 const std::vector<std::string>& tokens)
{
  MURXLA_MESSAGE_DD << "Start trying to minimize function sort on line "
                    << line_idx << " ...";

  bool res        = false;
  size_t n_tokens = tokens.size();
  /* The index of the first domain sort. */
  size_t idx = 1;
  /* The number of domain sorts. */
  size_t n_args = n_tokens - 2;

  /* Retrieve sort id. */
  std::string sort_id;
  {
    assert(lines[line_idx].size() == 2);
    std::vector<std::string> tokens_return;
    std::string _action_id;
    tokenize(lines[line_idx][1], _action_id, tokens_return);
    assert(_action_id == "return");
    assert(tokens_return.size() == 1);
    sort_id = tokens_return[0];
  }

  /* Collect all function terms that can occur as an argument to apply
   * (MK_CONST of the function sort 'sort_id' and ITE over function constants
   * of that sort). Further, collect all applies that need to be updated
   * simultaneously, together with the update of the function sort. */

  /* The function terms. */
  std::unordered_set<std::string> funs;

  /* Collect the data for the lines to update.
   * We have to record the original tokens here -- we can't retokenize these
   * lines on the fly while delta debugging, the set of tokens has to match the
   * indices of the included_args set. */
  std::vector<
      std::tuple<size_t, Action::Kind, std::vector<std::string>, size_t>>
      to_update{std::make_tuple(line_idx, Action::MK_SORT, tokens, idx)};

  for (size_t _line_idx : included_lines)
  {
    std::vector<std::string> _tokens;
    std::string _action_id;
    tokenize(lines[_line_idx][0], _action_id, _tokens);
    size_t _n_tokens = _tokens.size();
    if (_n_tokens > 0)
    {
      if (_action_id == Action::MK_CONST && _tokens[0] == sort_id)
      {
        assert(lines[_line_idx].size() == 2);
        std::vector<std::string> _tokens_return;
        std::string _action_id_return;
        tokenize(lines[_line_idx][1], _action_id_return, _tokens_return);
        assert(_action_id_return == "return");
        assert(_tokens_return.size() == 1);
        funs.insert(_tokens_return[0]);
      }
      else if (_action_id == Action::MK_TERM && _tokens[0] == Op::ITE)
      {
        assert(str_to_uint32(_tokens[2]) == 3);
        for (size_t j = 4; j < 6; ++j)
        {
          if (funs.find(_tokens[j]) != funs.end())
          {
            assert(lines[_line_idx].size() == 2);
            std::string _action_id_return;
            std::vector<std::string> _tokens_return;
            tokenize(lines[_line_idx][1], _action_id_return, _tokens_return);
            assert(_action_id_return == "return");
            assert(_tokens_return.size() == 1);
            funs.insert(_tokens_return[0]);
          }
        }
      }
      else if (_action_id == Action::MK_TERM && _tokens[0] == Op::UF_APPLY)
      {
        to_update.emplace_back(_line_idx, _action_id, _tokens, 4);
      }
    }
  }

  res = minimize_line_aux(golden_exit,
                          lines,
                          included_lines,
                          input_trace_file_name,
                          n_args,
                          to_update);
  return res;
}

bool
MurxlaDD::minimize_line(Murxla::Result golden_exit,
                        std::vector<std::vector<std::string>>& lines,
                        const std::vector<size_t>& included_lines,
                        const std::string& untrace_file_name)
{
  MURXLA_MESSAGE_DD << "Start trying to minimize trace lines ...";

  bool res = false;

  /* Create OpKindManager to query Op configuration. */
  statistics::Statistics opmgr_stats;
  TheoryIdSet opmgr_enabled_theories;
  for (int32_t t = 0; t < THEORY_ALL; ++t)
  {
    /* we enable all theories for delta debugging */
    opmgr_enabled_theories.insert(static_cast<TheoryId>(t));
  }
  OpKindManager opmgr(opmgr_enabled_theories, {}, false, &opmgr_stats);
  {
    RNGenerator opmgr_rng;
    std::unique_ptr<Solver> opmgr_solver(d_murxla->create_solver(opmgr_rng));
    opmgr_solver->configure_opmgr(&opmgr);
  }

  /* The set of actions that we consider for this minimization strategy. */
  std::unordered_set<Action::Kind> actions = {
      Action::GET_VALUE, Action::MK_SORT, Action::MK_TERM};

  /* Minimize. */
  for (size_t line_idx : included_lines)
  {
    std::string action_id;
    std::vector<std::string> tokens;

    /* first item is the action, second (if present) the return statement */
    tokenize(lines[line_idx][0], action_id, tokens);

    auto it = actions.find(action_id);
    if (it == actions.end()) continue;
    const Action::Kind& action = *it;
    uint32_t idx = 0, n_terms = 0, n_tokens = tokens.size();

    if (action == Action::MK_SORT)
    {
      if (Action::get_sort_kind_from_str(tokens[0]) != SORT_FUN) continue;
      res = minimize_line_sort_fun(golden_exit,
                                   lines,
                                   included_lines,
                                   untrace_file_name,
                                   line_idx,
                                   tokens);
    }
    else
    {
      MURXLA_MESSAGE_DD << "Start trying to minimize line " << line_idx
                        << " ...";

      if (action == Action::MK_TERM)
      {
        Op::Kind op_kind = tokens[0];
        Op& op           = opmgr.get_op(op_kind);
        if (op.d_arity != MURXLA_MK_TERM_N_ARGS_BIN) continue;
        idx     = 3;
        n_terms = str_to_uint32(tokens[2]);
      }
      else
      {
        for (idx = 0; idx < n_tokens; ++idx)
        {
          assert(!tokens[idx].empty());
          if (tokens[idx].find_first_not_of("0123456789") == std::string::npos)
          {
            n_terms = str_to_uint32(tokens[idx]);
            idx += 1;
            assert(n_tokens > n_terms);
            break;
          }
        }
      }

      if (n_terms > 0)
      {
        assert(n_tokens >= n_terms + 1);
        size_t line_size = lines[line_idx][0].size();
        std::vector<size_t> line_superset(n_terms);
        std::iota(line_superset.begin(), line_superset.end(), 0);
        uint32_t subset_size = n_terms / 2;

        while (subset_size > 0)
        {
          std::vector<std::vector<size_t>> subsets =
              split_superset(line_superset, subset_size);

          std::vector<size_t> cur_line_superset;
          std::unordered_set<size_t> excluded_sets;
          for (size_t i = 0, n = subsets.size(); i < n; ++i)
          {
            std::unordered_set<size_t> ex(excluded_sets);
            ex.insert(i);
            std::vector<size_t> included_terms = remove_subsets(subsets, ex);
            if (action == Action::MK_TERM && included_terms.size() < 2)
              continue;
            if (included_terms.size() == 0) continue;

            std::string line_cur = lines[line_idx][0];
            lines[line_idx][0]   = generate_minimized_line(
                action_id,
                tokens,
                included_terms,
                idx,
                {std::to_string((included_terms.size()))},
                {});

            std::vector<size_t> tmp_superset = test(golden_exit,
                                                    lines,
                                                    included_lines,
                                                    untrace_file_name);
            if (!tmp_superset.empty())
            {
              cur_line_superset = included_terms;
              excluded_sets.insert(i);
            }
            else
            {
              lines[line_idx][0] = line_cur;
            }
          }
          if (cur_line_superset.empty())
          {
            subset_size = subset_size / 2;
          }
          else
          {
            /* write to file and continue */
            write_lines_to_file(lines, included_lines, d_tmp_trace_file_name);
            line_superset = cur_line_superset;
            subset_size   = line_superset.size() / 2;
            res           = true;
            MURXLA_MESSAGE_DD
                << "line " << line_idx << " reduced to " << std::fixed
                << std::setprecision(2)
                << (((double) lines[line_idx][0].size()) / line_size * 100)
                << "% of original size";
          }
        }
      }
    }
  }
  return res;
}

std::vector<size_t>
MurxlaDD::test(Murxla::Result golden_exit,
               const std::vector<std::vector<std::string>>& lines,
               const std::vector<size_t>& superset,
               const std::string& untrace_file_name)
{
  std::vector<size_t> res_superset;
  std::string tmp_out_file_name =
      get_tmp_file_path("tmp-dd.out", d_murxla->d_tmp_dir);
  std::string tmp_err_file_name =
      get_tmp_file_path("tmp-dd.err", d_murxla->d_tmp_dir);

  write_lines_to_file(lines, superset, untrace_file_name);
  /* while delta debugging, do not trace to file or stdout */
  Murxla::Result exit = d_murxla->run(d_seed,
                                      d_time,
                                      tmp_out_file_name,
                                      tmp_err_file_name,
                                      "",
                                      untrace_file_name,
                                      true,
                                      false,
                                      Murxla::TraceMode::NONE);
  d_ntests += 1;
  if (exit == golden_exit
      && (d_murxla->d_options.dd_ignore_out
          || (!d_murxla->d_options.dd_match_out.empty()
              && find_in_file(
                  tmp_err_file_name, d_murxla->d_options.dd_match_out, false))
          || compare_files(tmp_out_file_name, d_gold_out_file_name))
      && (d_murxla->d_options.dd_ignore_err
          || (!d_murxla->d_options.dd_match_err.empty()
              && find_in_file(
                  tmp_err_file_name, d_murxla->d_options.dd_match_err, false))
          || compare_files(tmp_err_file_name, d_gold_err_file_name)))
  {
    res_superset = superset;
    d_ntests_success += 1;
  }
  return res_superset;
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla
