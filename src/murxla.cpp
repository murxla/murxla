#include "murxla.hpp"

#include <fcntl.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include <fstream>
#include <iomanip>
#include <regex>

#include "btor_solver.hpp"
#include "bzla_solver.hpp"
#include "cvc5_solver.hpp"
#include "except.hpp"
#include "fsm.hpp"
#include "smt2_solver.hpp"
#include "statistics.hpp"
#include "util.hpp"
#include "yices_solver.hpp"

namespace murxla {

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

/** Removes memory addresses and ==...== from ASAN messages. */
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

std::vector<std::string>
str_tokenize(const std::string& s)
{
  std::istringstream buf(s);
  std::vector<std::string> ret{std::istream_iterator<std::string>(buf),
                               std::istream_iterator<std::string>()};
  return ret;
}

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
void
write_idxs_to_file(const std::vector<std::string>& lines,
                   const std::vector<size_t> indices,
                   std::string& out_file_name)
{
  size_t size            = lines.size();
  std::ofstream out_file = open_output_file(out_file_name);
  for (size_t idx : indices)
  {
    assert(idx < size);
    out_file << lines[idx] << std::endl;
  }
  out_file.close();
}

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

}  // namespace

std::string
Murxla::get_info(Murxla::Result res)
{
  std::stringstream info;
  switch (res)
  {
    case RESULT_OK: info << "ok"; break;
    case RESULT_ERROR: info << "error"; break;
    case RESULT_ERROR_CONFIG: info << "config error"; break;
    case RESULT_TIMEOUT: info << "timeout"; break;
    default: assert(res == RESULT_UNKNOWN); info << "unknown";
  }
  return info.str();
}

std::string Murxla::DD_PREFIX    = "murxla-dd-";
std::string Murxla::SOLVER_BTOR  = "btor";
std::string Murxla::SOLVER_BZLA  = "czla";
std::string Murxla::SOLVER_CVC5  = "cvc5";
std::string Murxla::SOLVER_SMT2  = "smt2";
std::string Murxla::SOLVER_YICES = "yices";

Murxla::Murxla(statistics::Statistics* stats,
               SolverOptions* solver_options,
               ErrorMap* error_map,
               const std::string& tmp_dir)
    : d_solver_options(solver_options),
      d_tmp_dir(tmp_dir),
      d_stats(stats),
      d_errors(error_map)
{
  assert(stats);
  assert(solver_options);
  //  init_statistics();
}

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
Murxla::run(bool run_forked, std::string file_out, std::string file_err)
{
  bool cross  = !d_options.cross_check.empty();
  bool forked = run_forked || cross;

  std::string tmp_file_out = get_tmp_file_path("run-tmp1.out", d_tmp_dir);
  std::string tmp_file_err = get_tmp_file_path("run-tmp1.err", d_tmp_dir);

  Result res = run_aux(forked, tmp_file_out, tmp_file_err);

  if (cross)
  {
    std::streambuf *obuf, *ebuf;
    std::ofstream fout, ferr;

    if (d_options.dd)
    {
      fout.open(file_out);
      ferr.open(file_err);
      obuf = fout.rdbuf();
      ebuf = ferr.rdbuf();
    }
    else
    {
      obuf = std::cout.rdbuf();
      ebuf = std::cout.rdbuf();
    }
    std::ostream out(obuf), err(ebuf);

    SolverOptions solver_options_cross;  // not used for now
    std::string tmp_file_cross_out =
        get_tmp_file_path("run-tmp2.out", d_tmp_dir);
    std::string tmp_file_cross_err =
        get_tmp_file_path("run-tmp2.err", d_tmp_dir);

    statistics::Statistics stats_cross;
    Options options_cross(d_options);
    options_cross.solver = d_options.cross_check;

    Murxla murxla_cross(
        &stats_cross, options_cross, &solver_options_cross, nullptr, d_tmp_dir);
    Result cres =
        murxla_cross.run_aux(forked, tmp_file_cross_out, tmp_file_cross_err);

    /* write result / error output to .err */
    if (res != cres)
    {
      err << d_options.solver << ": " << get_info(res) << std::endl;
      if (res == RESULT_ERROR)
      {
        std::ifstream tmp_err = open_input_file(tmp_file_err);
        err << tmp_err.rdbuf();
        tmp_err.close();
        err << std::endl;
      }
      err << d_options.cross_check << ": " << get_info(cres) << std::endl;

      if (cres == RESULT_ERROR)
      {
        std::ifstream tmp_err = open_input_file(tmp_file_cross_err);
        err << tmp_err.rdbuf();
        tmp_err.close();
      }
      res = RESULT_ERROR;
    }

    /* write output diff to .out */
    if (!compare_files(tmp_file_out, tmp_file_cross_out))
    {
      out << "output differs";
      if (d_options.dd)
      {
        out << std::endl;
      }
      else
      {
        out << ":" << std::endl;
        diff_files(out, tmp_file_out, tmp_file_cross_out);
      }
      res = RESULT_ERROR;
    }
  }
  else if (forked)
  {
    std::ofstream err = open_output_file(file_err);
    std::ofstream out = open_output_file(file_out);

    std::ifstream tmp_out = open_input_file(tmp_file_out);
    out << tmp_out.rdbuf();
    tmp_out.close();

    std::ifstream tmp_err = open_input_file(tmp_file_err);
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
  bool is_cross             = !d_options.cross_check.empty();
  std::string out_file_name = DEVNULL;
  SeedGenerator sg(d_options.seed);
  Options options_test(d_options);

  std::string err_file_name = get_tmp_file_path("tmp.err", d_tmp_dir);

  if (is_cross)
  {
    options_test.api_trace_file_name = DEVNULL;
    out_file_name                    = get_tmp_file_path("tmp.out", d_tmp_dir);
  }

  do
  {
    double cur_time            = get_cur_wall_time();
    std::string smt2_file_name = options_test.smt2_file_name;

    options_test.seed = sg.next();

    std::cout << std::setw(10) << options_test.seed;
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

    if (!is_cross && options_test.solver == Murxla::SOLVER_SMT2)
    {
      if (!options_test.solver_binary.empty())
      {
        options_test.smt2_file_name = "";
      }
      else if (options_test.smt2_file_name.empty())
      {
        /* If no online solver is configured, we'll never run into the error
         * case below and replay (the Smt2Solver only answers 'unknown' and
         * dumps SMT2 -> should never terminate with an error).
         * We therefore dump every generated sequence to smt2 continuously. */
        options_test.smt2_file_name = get_smt2_file_name(
            options_test.seed, options_test.untrace_file_name);
        if (!options_test.out_dir.empty())
        {
          options_test.smt2_file_name =
              prepend_path(options_test.out_dir, options_test.smt2_file_name);
        }
      }
    }

    /* Run and test for error without tracing to trace file (we by default still
     * trace to stdout here, which is redirected to /dev/null).
     * If error encountered, replay and trace below. */
    statistics::Statistics stats_test;
    Murxla murxla_test(
        &stats_test, options_test, d_solver_options, nullptr, d_tmp_dir);
    Result res = murxla_test.run(true, out_file_name, err_file_name);

    /* report status */
    if (res == RESULT_OK)
    {
      std::cout << "\33[2K\r" << std::flush;
    }
    else
    {
      /* Read error file and check if we already encounterd the same error. */
      bool duplicate = false;
      if (res == RESULT_ERROR)
      {
        std::ifstream errs = open_input_file(err_file_name);
        std::string errmsg, line;
        while (std::getline(errs, line))
        {
          errmsg += line + "\n";
        }
        duplicate = add_error(errmsg, options_test.seed);
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
    if (res != RESULT_OK && res != RESULT_TIMEOUT)
    {
      options_test.api_trace_file_name = d_options.api_trace_file_name;
      Result res_replay = murxla_test.replay(out_file_name, err_file_name);
      assert(res == res_replay);
    }
    std::cout << "\r" << std::flush;
    options_test.smt2_file_name = smt2_file_name;
  } while (options_test.max_runs == 0 || num_runs < options_test.max_runs);
}

Murxla::Result
Murxla::replay(std::string& out_file_name, std::string& err_file_name)
{
  statistics::Statistics stats_replay;
  Options options_replay(d_options);

  options_replay.time = 0;  // reset time limit

  if (options_replay.api_trace_file_name.empty())
  {
    options_replay.api_trace_file_name =
        get_api_trace_file_name(options_replay.seed,
                                options_replay.dd,
                                options_replay.untrace_file_name);
    if (!options_replay.out_dir.empty())
    {
      options_replay.api_trace_file_name = prepend_path(
          options_replay.out_dir, options_replay.api_trace_file_name);
    }
  }
  if (options_replay.smt2_file_name.empty()
      && options_replay.solver == Murxla::SOLVER_SMT2)
  {
    options_replay.smt2_file_name = get_smt2_file_name(
        options_replay.seed, options_replay.untrace_file_name);
    if (!options_replay.out_dir.empty())
    {
      options_replay.smt2_file_name =
          prepend_path(options_replay.out_dir, options_replay.smt2_file_name);
    }
  }

  Murxla murxla_replay(
      &stats_replay, options_replay, d_solver_options, nullptr, d_tmp_dir);
  Result res = murxla_replay.run(true, out_file_name, err_file_name);

  if (options_replay.dd)
  {
    murxla_replay.dd();
  }
  else
  {
    std::cout << options_replay.api_trace_file_name << std::endl;
  }
  return res;
}

void
Murxla::dd()
{
  assert(!d_options.api_trace_file_name.empty());

  std::vector<std::string> lines;
  std::string line, token;
  Murxla::Result gold_exit, exit;

  std::string gold_out_file_name =
      get_tmp_file_path("dd-gold-tmp.out", d_tmp_dir);
  std::string gold_err_file_name =
      get_tmp_file_path("dd-gold-tmp.err", d_tmp_dir);
  std::string tmp_trace_file_name =
      get_tmp_file_path("dd-tmp.trace", d_tmp_dir);
  std::string tmp_out_file_name = get_tmp_file_path("dd-tmp.out", d_tmp_dir);
  std::string tmp_err_file_name = get_tmp_file_path("dd-tmp.err", d_tmp_dir);

  /* init options object for golden (replay of original) run */
  Murxla::Options options_dd(d_options);
  options_dd.verbosity           = 0;
  options_dd.api_trace_file_name = tmp_trace_file_name;
  options_dd.untrace_file_name   = d_options.api_trace_file_name;

  /* init trace file name for minimized trace */
  if (options_dd.dd_trace_file_name.empty())
  {
    if (d_options.untrace_file_name.empty())
    {
      options_dd.dd_trace_file_name = prepend_prefix_to_file_name(
          Murxla::DD_PREFIX, d_options.api_trace_file_name);
    }
    else
    {
      options_dd.dd_trace_file_name = prepend_prefix_to_file_name(
          Murxla::DD_PREFIX, d_options.untrace_file_name);
    }
  }
  if (!d_options.out_dir.empty())
  {
    options_dd.dd_trace_file_name =
        prepend_path(d_options.out_dir, options_dd.dd_trace_file_name);
  }
  MURXLA_MESSAGE_DD << "start minimizing file '"
                    << options_dd.untrace_file_name.c_str() << "'";

  /* golden run */
  statistics::Statistics stats_golden;
  Murxla murxla_golden(
      &stats_golden, options_dd, d_solver_options, nullptr, d_tmp_dir);
  gold_exit = murxla_golden.run(true, gold_out_file_name, gold_err_file_name);

  MURXLA_MESSAGE_DD << "golden exit: " << Murxla::get_info(gold_exit).c_str();
  {
    std::ifstream gold_out_file = open_input_file(gold_out_file_name);
    std::stringstream ss;
    ss << gold_out_file.rdbuf();
    MURXLA_MESSAGE_DD << "golden stdout output: " << ss.str();
    gold_out_file.close();
  }
  {
    std::ifstream gold_err_file = open_input_file(gold_err_file_name);
    MURXLA_MESSAGE_DD << "golden stderr output: " << gold_err_file.rdbuf();
    gold_err_file.close();
  }
  if (!options_dd.dd_out_string.empty())
  {
    MURXLA_MESSAGE_DD << "checking for occurrence of '"
                      << options_dd.dd_out_string.c_str()
                      << "' in stdout output";
  }
  if (!options_dd.dd_err_string.empty())
  {
    MURXLA_MESSAGE_DD << "checking for occurrence of '"
                      << options_dd.dd_err_string.c_str()
                      << "' in stderr output";
  }

  /* start delta debugging */

  /* represent input trace as vector of lines, trace statements that expect and
   * are accompanied by a return statement are represented as one element of
   * the vector */

  std::ifstream trace_file = open_input_file(tmp_trace_file_name);
  while (std::getline(trace_file, line))
  {
    if (line[0] == '#') continue;
    if (std::getline(std::stringstream(line), token, ' ') && token == "return")
    {
      std::stringstream ss;
      assert(lines.size() > 0);
      std::string prev = lines.back();
      ss << prev << std::endl << line;
      lines.pop_back();
      lines.push_back(ss.str());
    }
    else
    {
      lines.push_back(line);
    }
  }
  trace_file.close();

  /* while delta debugging, do not trace to file */
  options_dd.api_trace_file_name = DEVNULL;
  options_dd.untrace_file_name   = tmp_trace_file_name;

  statistics::Statistics stats_dd;
  Murxla murxla_dd(&stats_dd, options_dd, d_solver_options, nullptr, d_tmp_dir);

  int64_t orig_size = lines.size();
  int64_t size      = orig_size;
  std::vector<size_t> superset(size);
  std::iota(superset.begin(), superset.end(), 0);
  int64_t subset_size = size / 2;
  uint32_t n_tests = 0, n_failed = 0;
  while (subset_size > 0)
  {
    std::vector<std::vector<size_t>> subsets;
    auto begin = superset.begin();
    auto end   = superset.begin();
    for (int64_t lo = 0; end != superset.end(); lo += subset_size)
    {
      /* split original set into chunks of size 'subset_size' (last subset will
       * contain the remaining m > subset_size lines if 'subset_size' does not
       * divide 'size') */
      int64_t hi = lo + subset_size;
      end =
          hi > size || (size - hi) < subset_size ? superset.end() : begin + hi;
      std::vector<size_t> subset(begin + lo, end);
      subsets.push_back(subset);
    }
    assert(subsets.size() == (size_t) size / subset_size);

    std::vector<size_t> cur_superset;
    std::unordered_set<size_t> excluded_sets;
    for (size_t i = 0, n = subsets.size(); i < n; ++i)
    {
      std::unordered_set<size_t> ex(excluded_sets);
      ex.insert(i);
      std::vector<size_t> tmp = remove_subsets(subsets, ex);

      write_idxs_to_file(lines, tmp, tmp_trace_file_name);
      exit = murxla_dd.run(true, tmp_out_file_name, tmp_err_file_name);
      n_tests += 1;
      if (exit == gold_exit
          && ((!options_dd.dd_out_string.empty()
               && find_in_file(tmp_err_file_name, options_dd.dd_out_string))
              || compare_files(tmp_out_file_name, gold_out_file_name))
          && ((!options_dd.dd_err_string.empty()
               && find_in_file(tmp_err_file_name, options_dd.dd_err_string))
              || compare_files(tmp_err_file_name, gold_err_file_name)))
      {
        cur_superset = tmp;
        excluded_sets.insert(i);
        n_failed += 1;
        MURXLA_MESSAGE_DD << "reduced to " << std::fixed << std::setprecision(2)
                          << (((double) cur_superset.size()) / orig_size * 100)
                          << "% of original size";
      }
    }
    if (cur_superset.empty())
    {
      subset_size = subset_size / 2;
    }
    else
    {
      /* write found subset immediately to file and continue */
      write_idxs_to_file(lines, cur_superset, options_dd.dd_trace_file_name);
      superset    = cur_superset;
      size        = superset.size();
      subset_size = size / 2;
    }
  }
  MURXLA_MESSAGE_DD << std::endl;
  MURXLA_MESSAGE_DD << n_failed << " of " << n_tests
                    << " successful (reduced) tests";
  MURXLA_MESSAGE_DD << "written to: " << options_dd.dd_trace_file_name.c_str();
}

// void
// Murxla::init_statistics()
//{
//  int fd;
//  std::stringstream ss;
//  std::string shmfilename;
//
//  ss << "/tmp/murxla-shm-" << getpid();
//  shmfilename = ss.str();
//
//  MURXLA_EXIT_ERROR((fd = open(shmfilename.c_str(), O_RDWR | O_CREAT,
//  S_IRWXU))
//                    < 0)
//      << "failed to create shared memory file for statistics";
//
//  d_stats = static_cast<Statistics*>(mmap(0,
//                                        sizeof(Statistics),
//                                        PROT_READ | PROT_WRITE,
//                                        MAP_ANONYMOUS | MAP_SHARED,
//                                        fd,
//                                        0));
//  memset(d_stats, 0, sizeof(Statistics));
//
//  MURXLA_EXIT_ERROR(close(fd))
//      << "failed to close shared memory file for statistics";
//  (void) unlink(shmfilename.c_str());
//}

Murxla::Result
Murxla::run_aux(bool run_forked, std::string file_out, std::string file_err)
{
  bool untrace     = !d_options.untrace_file_name.empty();
  bool smt2_online = !d_options.solver_binary.empty();
  int32_t status, fd;
  Result result;
  pid_t solver_pid = 0, timeout_pid = 0;
  std::streambuf *trace_buf, *smt2_buf;
  std::ofstream trace_file;
  std::ofstream smt2_file;

  if (smt2_online) run_forked = true;

  if (!d_options.api_trace_file_name.empty())
  {
    trace_file = open_output_file(d_options.api_trace_file_name);
    trace_buf  = trace_file.rdbuf();
  }
  else
  {
    trace_buf = std::cout.rdbuf();
  }
  std::ostream trace(trace_buf);

  if (!d_options.smt2_file_name.empty())
  {
    smt2_file = open_output_file(d_options.smt2_file_name);
    smt2_buf  = smt2_file.rdbuf();
  }
  else
  {
    smt2_buf = std::cout.rdbuf();
  }
  std::ostream smt2(smt2_buf);

  RNGenerator rng(d_options.seed);

  result = RESULT_UNKNOWN;

  /* If seeded run in main process. */
  if (run_forked)
  {
    solver_pid = fork();
    MURXLA_EXIT_ERROR(solver_pid == -1) << "forking solver process failed.";
  }

  /* parent */
  if (solver_pid)
  {
    /* If a time limit is given, fork another process that kills the solver_pid
     * after g_option.time seconds. (https://stackoverflow.com/a/8020324) */
    if (d_options.time)
    {
      timeout_pid = fork();
      MURXLA_EXIT_ERROR(timeout_pid == -1) << "forking timeout process failed";
      if (timeout_pid == 0)
      {
        signal(SIGINT, SIG_DFL);  // reset stats signal handler
        usleep(d_options.time * 1000000);
        exit(EXIT_OK);
      }
    }

    /* Wait for the first process to finish (solver_pid or timeout_pid). */
    pid_t exited_pid = wait(&status);

    if (exited_pid == solver_pid)
    {
      /* Kill and collect timeout process if solver process terminated first. */
      if (timeout_pid)
      {
        kill(timeout_pid, SIGKILL);
        waitpid(timeout_pid, nullptr, 0);
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
      assert(timeout_pid);
      kill(solver_pid, SIGKILL);
      waitpid(solver_pid, nullptr, 0);
      result = RESULT_TIMEOUT;
    }
  }
  /* child */
  else
  {
    signal(SIGINT, SIG_DFL);  // reset stats signal handler

    int32_t fd_to[2], fd_from[2];
    FILE *to_external = nullptr, *from_external = nullptr;
    pid_t smt2_pid = 0;

    if (run_forked)
    {
      /* Redirect stdout and stderr of child process into given files. */
      fd = open(
          file_out.c_str(), O_CREAT | O_WRONLY | O_TRUNC, S_IRUSR | S_IWUSR);
      MURXLA_EXIT_ERROR(fd < 0) << "unable to open file " << file_out;
      dup2(fd, STDOUT_FILENO);
      close(fd);
      fd = open(
          file_err.c_str(), O_CREAT | O_WRONLY | O_TRUNC, S_IRUSR | S_IWUSR);
      if (fd < 0)
      {
        perror(0);
        MURXLA_EXIT_ERROR(true) << "unable to open file " << file_err;
      }
      dup2(fd, STDERR_FILENO);
      close(fd);
    }

    Solver* solver = nullptr;

    if (d_options.solver == SOLVER_BTOR)
    {
#if MURXLA_USE_BOOLECTOR
      solver = new btor::BtorSolver(rng);
#else
      MURXLA_EXIT_ERROR(true) << "Boolector not configured";
#endif
    }
    else if (d_options.solver == SOLVER_BZLA)
    {
#if MURXLA_USE_BITWUZLA
      solver = new bzla::BzlaSolver(rng);
#else
      MURXLA_EXIT_ERROR(true) << "Bitwuzla not configured";
#endif
    }
    else if (d_options.solver == SOLVER_CVC5)
    {
#if MURXLA_USE_CVC5
      solver = new cvc5::Cvc5Solver(rng);
#else
      MURXLA_EXIT_ERROR(true) << "cvc5 not configured";
#endif
    }
    else if (d_options.solver == SOLVER_YICES)
    {
#if MURXLA_USE_YICES
      solver = new yices::YicesSolver(rng);
#else
      MURXLA_EXIT_ERROR << "Yices not configured";
#endif
    }
    else if (d_options.solver == SOLVER_SMT2)
    {
      if (smt2_online)
      {
        /* Open input/output pipes from and to the external online solver. */
        MURXLA_EXIT_ERROR(pipe(fd_to) != 0 || pipe(fd_from) != 0)
            << "creating input and/or output pipes failed";

        smt2_pid = fork();

        MURXLA_EXIT_ERROR(smt2_pid == -1) << "forking solver process failed.";

        if (smt2_pid == 0)  // child
        {
          close(fd_to[SMT2_WRITE_END]);
          dup2(fd_to[SMT2_READ_END], STDIN_FILENO);

          close(fd_from[SMT2_READ_END]);
          /* Redirect stdout of external solver to write end. */
          dup2(fd_from[SMT2_WRITE_END], STDOUT_FILENO);
          /* Redirect stderr of external solver to write end. */
          dup2(fd_from[SMT2_WRITE_END], STDERR_FILENO);

          std::vector<std::string> args;
          std::string arg;
          std::stringstream ss(d_options.solver_binary);
          while (std::getline(ss, arg, ' '))
          {
            args.push_back(arg);
          }
          size_t n        = args.size();
          char** execargs = new char*[n + 1];
          for (size_t i = 0; i < n; ++i)
          {
            size_t m    = args[i].size() + 1;
            execargs[i] = new char[m];
            std::strncpy(execargs[i], args[i].c_str(), m);
          }
          execargs[n] = nullptr;

          execv(execargs[0], execargs);
          for (size_t i = 0; i < n; ++i)
          {
            delete[] execargs[i];
          }
          delete[] execargs;

          MURXLA_EXIT_ERROR(true)
              << "'" << d_options.solver_binary << "' is not executable";
        }

        close(fd_to[SMT2_READ_END]);
        to_external = fdopen(fd_to[SMT2_WRITE_END], "w");
        close(fd_from[SMT2_WRITE_END]);
        from_external = fdopen(fd_from[SMT2_READ_END], "r");

        MURXLA_EXIT_ERROR(to_external == nullptr || from_external == nullptr)
            << "opening read/write channels to external solver failed";
      }
      solver = new smt2::Smt2Solver(
          rng, smt2, smt2_online, to_external, from_external);
    }

    try
    {
      FSM fsm(rng,
              solver,
              trace,
              *d_solver_options,
              d_options.arith_linear,
              d_options.trace_seeds,
              !d_options.cross_check.empty(),
              d_options.simple_symbols,
              d_options.smt,
              d_stats,
              d_options.enabled_theories);
      fsm.configure();

      /* replay/untrace given API trace */
      if (untrace)
      {
        fsm.untrace(d_options.untrace_file_name);
      }
      /* regular MBT run */
      else
      {
        fsm.run();
      }
    }
    catch (MurxlaConfigException& e)
    {
      MURXLA_EXIT_ERROR_CONFIG(true) << e.get_msg();
    }
    catch (MurxlaException& e)
    {
      MURXLA_EXIT_ERROR(true) << e.get_msg();
    }

    if (smt2_online) waitpid(smt2_pid, nullptr, 0);

    if (trace_file.is_open()) trace_file.close();
    if (smt2_file.is_open()) smt2_file.close();

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
}  // namespace murxla
