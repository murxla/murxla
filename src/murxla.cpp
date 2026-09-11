/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include "murxla.hpp"

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <nlohmann/json.hpp>
#include <regex>
#include <set>

#include "dd.hpp"
#include "except.hpp"
#include "fsm.hpp"
#include "solver/bitwuzla/bitwuzla_solver.hpp"
#include "solver/btor/btor_solver.hpp"
#include "solver/cvc5/cvc5_solver.hpp"
#include "solver/meta/check_solver.hpp"
#include "solver/meta/shadow_solver.hpp"
#include "solver/smt2/smt2_solver.hpp"
#include "solver/solver_profile.hpp"
#include "solver/yices/yices_solver.hpp"
#include "statistics.hpp"
#include "util.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

#ifdef MURXLA_COVERAGE
extern "C" void __gcov_dump();

volatile sig_atomic_t handled_abort = 0;

/* This handler makes sure that coverage data is dumped even when the process
 * aborts since we also want the coverage information for these runs. */
extern "C" void
handle_abort(int sig)
{
  if (!handled_abort)
  {
    handled_abort = 1;
    __gcov_dump();
  }
  signal(sig, SIG_DFL);
  raise(sig);
}
#endif

/* -------------------------------------------------------------------------- */

namespace {

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
      /* Ignore numbers for diff. */
      for (size_t j = 0; j < t1[i].size(); ++j)
      {
        if (std::isdigit(t1[i][j])) continue;
        ++diff;
      }
    }
  }
  return diff;
}

double
error_diff(const std::string& e1, const std::string& e2)
{
  size_t len = std::max(e1.size(), e2.size());
  /* Two empty messages are the same message. Without this the division
   * below is 0/0, and the resulting NaN compares false against any
   * threshold, so an empty error message would not even match itself. */
  if (len == 0)
  {
    return 0;
  }
  size_t diff = str_diff(e1, e2);
  return static_cast<double>(diff) / static_cast<double>(len);
}

/* -------------------------------------------------------------------------- */
/* RPC pipe I/O helpers.                                                      */
/*                                                                            */
/* Used for `-j/--jobs` parallel fuzzing: workers communicate with the        */
/* coordinator over pipe pairs. Messages are length-prefixed (4-byte little-  */
/* endian) and writes/reads loop on EINTR (workers' solver/timeout children   */
/* deliver SIGCHLD which interrupts pipe I/O).                                */
/* -------------------------------------------------------------------------- */

bool
write_all(int fd, const void* buf, size_t n)
{
  const char* p = static_cast<const char*>(buf);
  while (n > 0)
  {
    ssize_t w = ::write(fd, p, n);
    if (w < 0)
    {
      if (errno == EINTR) continue;
      return false;
    }
    if (w == 0) return false;
    p += w;
    n -= static_cast<size_t>(w);
  }
  return true;
}

bool
read_all(int fd, void* buf, size_t n)
{
  char* p = static_cast<char*>(buf);
  while (n > 0)
  {
    ssize_t r = ::read(fd, p, n);
    if (r < 0)
    {
      if (errno == EINTR) continue;
      return false;
    }
    if (r == 0) return false; /* EOF */
    p += r;
    n -= static_cast<size_t>(r);
  }
  return true;
}

bool
write_msg(int fd, uint8_t type, const std::string& payload)
{
  if (payload.size() > 0xFFFFFFFFULL) return false;
  uint32_t len = static_cast<uint32_t>(payload.size());
  uint8_t hdr[5];
  hdr[0] = type;
  hdr[1] = (uint8_t) (len & 0xFF);
  hdr[2] = (uint8_t) ((len >> 8) & 0xFF);
  hdr[3] = (uint8_t) ((len >> 16) & 0xFF);
  hdr[4] = (uint8_t) ((len >> 24) & 0xFF);
  if (!write_all(fd, hdr, sizeof(hdr))) return false;
  if (len == 0) return true;
  return write_all(fd, payload.data(), payload.size());
}

bool
read_msg(int fd, uint8_t& type, std::string& payload)
{
  uint8_t hdr[5];
  if (!read_all(fd, hdr, sizeof(hdr))) return false;
  type         = hdr[0];
  uint32_t len = (uint32_t) hdr[1] | ((uint32_t) hdr[2] << 8)
                 | ((uint32_t) hdr[3] << 16) | ((uint32_t) hdr[4] << 24);
  payload.assign(len, '\0');
  if (len == 0) return true;
  return read_all(fd, payload.data(), len);
}

}  // namespace

/* -------------------------------------------------------------------------- */

volatile sig_atomic_t Murxla::s_caught_signal = 0;

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
  load_solver_profile();

  if (!d_options.export_errors_filename.empty())
  {
    d_export_errors.insert(d_export_errors.end(),
                           d_exclude_errors.begin(),
                           d_exclude_errors.end());
  }
}

Result
Murxla::run(uint64_t seed,
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

  /* If we don't run forked, and an explicit api trace file name is given, the
   * trace is immediately written to the given file (rather than writing it
   * first to a temp file).  This is because else, we don't get a chance to
   * write the contents from the temp file back to the given file when the
   * process aborts (if the trace triggers an issue).
   *
   * When forking, run_aux stores the name of the temp file in
   * 'tmp_api_trace_file_name', and its contents are then copied into the
   * given file 'api_trace_file_name'. */
  std::string tmp_api_trace_file_name;
  if (!run_forked)
  {
    tmp_api_trace_file_name = api_trace_file_name;
  }

  Result res = run_aux(seed,
                       time,
                       tmp_file_out,
                       tmp_file_err,
                       tmp_api_trace_file_name,
                       untrace_file_name,
                       run_forked,
                       record_stats,
                       trace_mode,
                       d_error_msg);

  if (trace_mode == TO_FILE)
  {
    std::string copy_from, copy_to;

    /* For the SMT2 solver, we only write the SMT2 file (not the trace). */
    if (!d_options.dd && d_options.solver == SOLVER_SMT2)
    {
      copy_from = get_tmp_file_path(SMT2_FILE, d_tmp_dir);
      copy_to   = get_smt2_file_name(seed, untrace_file_name);
    }
    /* For all other solvers, we write the trace file. */
    else if (api_trace_file_name != DEVNULL)
    {
      copy_from = tmp_api_trace_file_name;
      copy_to   = api_trace_file_name;
    }

    if (copy_from != copy_to)
    {
      assert(std::filesystem::exists(copy_from));

      // Create parent directories if they do not exist yet.
      std::filesystem::path fp(copy_to);
      if (fp.has_parent_path() && !std::filesystem::exists(fp.parent_path()))
      {
        std::filesystem::create_directories(fp.parent_path());
      }
      std::filesystem::copy(copy_from,
                            copy_to,
                            std::filesystem::copy_options::overwrite_existing);
    }
  }
  // Print terminating "}" for main() function of native API traces.
  else if (trace_mode == TO_STDOUT && d_options.solver_trace)
  {
    std::cout << "}" << std::endl;
  }

  if (run_forked)
  {
    std::ofstream err = open_output_file(file_err, true);
    std::ofstream out = open_output_file(file_out, true);

    std::ifstream tmp_out = open_input_file(tmp_file_out, true);
    out << tmp_out.rdbuf();
    tmp_out.close();

    std::ifstream tmp_err = open_input_file(tmp_file_err, true);
    if (d_excluded_error_lines.empty())
    {
      err << tmp_err.rdbuf();
    }
    else
    {
      std::string line;
      while (std::getline(tmp_err, line))
      {
        if (is_excluded_error_line(line)) continue;
        err << line << "\n";
      }
    }
    tmp_err.close();

    out.close();
    err.close();
  }
  return res;
}

void
Murxla::test()
{
  uint64_t num_timeouts = 0, num_printed_lines = 0;
  uint64_t error_id = 0, error_nduplicates = 0;
  uint32_t num_runs         = 0;
  double start_time         = get_cur_wall_time();
  std::string out_file_name = DEVNULL;
  SeedGenerator sg;
  if (d_options.is_seeded)
  {
    sg.set_seed(d_options.seed);
  }

  std::string err_file_name = get_tmp_file_path("tmp.err", d_tmp_dir);
  Terminal term;
  bool is_worker = (d_role == Role::WORKER);

  /* Workers funnel all stdout-bound output through `log_via_rpc` so the
   * coordinator can interleave it with its own status line. We accumulate
   * per-iteration output into `worker_out` and flush once per iteration. */
  std::ostringstream worker_out;
  auto put = [&](const std::string& s) {
    if (is_worker)
      worker_out << s;
    else
      std::cout << s;
  };

  do
  {
    double cur_time = get_cur_wall_time();

    uint64_t seed = sg.next();

    /* Per-iteration status line. The coordinator prints its own aggregate
     * status line, so workers skip this entirely. */
    if (!is_worker)
    {
      if (num_printed_lines % 100 == 0)
      {
        std::cout << std::setw(16) << "seed";
        std::cout << " " << std::setw(5) << "runs";
        std::cout << " " << std::setw(8) << "r/s";
        std::cout << " " << std::setw(5) << "sat";
        std::cout << " " << std::setw(5) << "unsat";
        std::cout << " " << std::setw(5) << "unknw";
        std::cout << " " << std::setw(5) << "to";
        std::cout << " " << std::setw(5) << "err";

        std::cout << std::endl;
        ++num_printed_lines;
      }

      std::cout << std::setw(16) << std::hex << seed << std::dec;
      std::cout << " " << std::setw(5) << num_runs;
      std::cout << " " << std::setw(8) << std::setprecision(2) << std::fixed;
      std::cout << num_runs / (cur_time - start_time);
      std::cout << " " << std::setw(5)
                << d_stats->d_results[Solver::Result::SAT];
      std::cout << " " << std::setw(5)
                << d_stats->d_results[Solver::Result::UNSAT];
      std::cout << " " << std::setw(5)
                << d_stats->d_results[Solver::Result::UNKNOWN];
      std::cout << " " << std::setw(5) << num_timeouts;
      std::cout << " " << std::setw(5) << d_errors->size();
      std::cout << std::flush;
    }
    num_runs++;

    /* Note: If the selected solver is SOLVER_SMT2 and no online solver is
     *       configured, we'll never run into the error case below and replay
     *       (the Smt2Solver only answers 'unknown' and dumps SMT2 -> should
     *       never terminate with an error).  We therefore dump every generated
     *       sequence to smt2 continuously. */

    /* Run and test for error without tracing to trace file (we by default still
     * trace to stdout here, which is redirected to /dev/null).
     * If error encountered, replay and trace below. */

    std::string api_trace_file_name = get_api_trace_file_name(seed);
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

    std::string errmsg, errmsg_filtered;
    ErrorKind errkind = ErrorKind::ERROR;
    /* report status */
    if (res == RESULT_OK)
    {
      if (!is_worker)
      {
        if (term.is_term())
        {
          term.erase(std::cout);
        }
        else
        {
          std::cout << std::endl;
          ++num_printed_lines;
        }
      }
    }
    else
    {
      /* Read error file and check if we already encounterd the same error. */
      if (res == RESULT_ERROR || res == RESULT_ERROR_CONFIG
          || res == RESULT_ERROR_UNTRACE)
      {
        std::ifstream errs = open_input_file(err_file_name, false);
        std::string line;
        while (std::getline(errs, line))
        {
          errmsg += line + "\n";
        }
        if (res == RESULT_ERROR)
        {
          /* Run the local filter prologue (cheap, immutable solver-profile
           * data is already in this process). For workers, send the dedup
           * RPC to the coordinator so error_id assignment stays globally
           * consistent. SOLO callers go straight through insert_error. */
          auto [pre_kind, pre_filtered, pre_norm] = prefilter_error(errmsg);
          errmsg_filtered                         = pre_filtered;
          if (pre_kind == ErrorKind::FILTER)
          {
            errkind           = ErrorKind::FILTER;
            error_id          = 0;
            error_nduplicates = 0;
          }
          else if (is_worker)
          {
            std::tie(errkind, error_id, error_nduplicates) =
                add_error_via_rpc(pre_filtered, pre_norm, seed);
          }
          else
          {
            std::tie(errkind, error_id, error_nduplicates) =
                insert_error(pre_filtered, pre_norm, seed);
          }
        }
        else if (res == RESULT_ERROR_CONFIG)
        {
          if (!is_worker) term.erase(std::cout);
          MURXLA_CHECK_CONFIG(false) << errmsg_filtered << " " << d_error_msg;
        }
        else
        {
          assert(res == RESULT_ERROR_UNTRACE);
          MURXLA_CHECK_TRACE(false) << errmsg_filtered << " " << d_error_msg;
        }
      }

      std::stringstream info;
      info << " [";
      switch (res)
      {
        case RESULT_ERROR:
          if (errkind == ErrorKind::DUPLICATE)
          {
            info << term.green() << "duplicate:" << error_group_dir(error_id);
          }
          else if (errkind == ErrorKind::ERROR)
          {
            info << term.red() << "error:" << error_group_dir(error_id);
          }
          else if (errkind == ErrorKind::FILTER)
          {
            info << term.gray() << "filtered";
          }
          break;
        case RESULT_ERROR_CONFIG: info << term.red() << "config error"; break;
        case RESULT_ERROR_UNTRACE: info << term.red() << "untrace error"; break;
        case RESULT_TIMEOUT:
          info << term.blue() << "timeout";
          ++num_timeouts;
          break;
        default: assert(res == RESULT_UNKNOWN); info << "unknown";
      }
      info << term.defaultcolor() << "]";

      put(info.str());
      if (!is_worker) std::cout << std::flush;
      if (res == RESULT_ERROR && errkind != ErrorKind::FILTER)
      {
        put(" ");
      }
      else
      {
        if (d_options.verbosity > 0)
        {
          put("\n");
          ++num_printed_lines;
        }
      }

      /* Replay and trace on error.
       *
       * If SMT2 solver with online solver configured, dump smt2 on replay.
       * If SMT2 solver configured without an online solver, we'll never enter
       * here (the SMT2 solver should never return an error result). */
      if (res != RESULT_TIMEOUT && errkind != ErrorKind::FILTER)
      {
        // No need to replay SMT2 since we already have the SMT2 problem.
        if (smt2_offline)
        {
          put(get_smt2_file_name(seed, api_trace_file_name) + "\n");
        }
        else
        {
          assert(error_id > 0);
          api_trace_file_name = get_api_trace_file_name(seed, error_id);

          /* Only minimize the first trace of an error group, minimizing
           * duplicates of an already known error does not add any new
           * information. */
          bool minimize = d_options.dd && errkind != ErrorKind::DUPLICATE;

          /* At default verbosity the output of the delta debugger is
           * suppressed. Instead, we mark the line as being delta debugged
           * while minimization is in progress and replace the marker with the
           * name of the minimized trace when done. */
          const std::string marker = "[dd]";
          bool quiet_dd            = minimize && d_options.verbosity == 0;
          bool print_marker        = quiet_dd && !is_worker && term.is_term();
          if (print_marker)
          {
            std::cout << term.gray() << marker << term.defaultcolor()
                      << std::flush;
          }

          std::string min_trace_file_name;
          Result res_replay = replay(seed,
                                     out_file_name,
                                     err_file_name,
                                     api_trace_file_name,
                                     d_options.untrace_file_name,
                                     minimize,
                                     &min_trace_file_name);

          if (print_marker)
          {
            std::cout << term.erase_chars(static_cast<uint32_t>(marker.size()));
          }
          if (quiet_dd && !min_trace_file_name.empty())
          {
            put(min_trace_file_name + "\n");
          }
          else
          {
            put(api_trace_file_name + "\n");
          }

          // Note: This may happen in few cases where the replay runs into a
          // timeout, but the original run does not.
          MURXLA_WARN(res != res_replay)
              << "Replay did not return the same result as original run. "
              << "Original run returned " << res << ", but replay returned "
              << res_replay << ".";
        }
      }
      /* Print new error message after it was found. */
      if (res == RESULT_ERROR && errkind == ErrorKind::ERROR)
      {
        put("\n");
        put(rstrip(errmsg_filtered) + "\n\n");
        num_printed_lines = 0;  // print header again after error

        // If it is the first error, we also store the error message in a text
        // file. This is the representative message of the error group: it
        // determines the group's id, and load_state() reads it back to
        // recognize the error in later runs. Never clobber an existing one.
        assert(error_nduplicates == 1);
        std::filesystem::path fp(api_trace_file_name);
        std::string text_file = prepend_path(fp.parent_path(), "error.txt");
        if (!std::filesystem::exists(text_file))
        {
          std::ofstream os(text_file);
          os << errmsg_filtered << "\n";
        }
      }
    }

    /* Worker: flush per-iteration output and update shared counters. */
    if (is_worker)
    {
      const std::string s = worker_out.str();
      if (!s.empty())
      {
        log_via_rpc(s);
      }
      worker_out.str("");
      worker_out.clear();

      if (d_aggregate)
      {
        d_aggregate->num_runs.fetch_add(1, std::memory_order_relaxed);
        if (res == RESULT_TIMEOUT)
        {
          d_aggregate->num_timeouts.fetch_add(1, std::memory_order_relaxed);
        }
        d_aggregate->last_seed.store(seed, std::memory_order_relaxed);
      }
    }
  } while (!s_caught_signal
           && (d_options.max_runs == 0 || num_runs < d_options.max_runs));
}

Result
Murxla::replay(uint64_t seed,
               const std::string& out_file_name,
               const std::string& err_file_name,
               const std::string& api_trace_file_name,
               const std::string& untrace_file_name,
               bool minimize,
               std::string* min_trace_file_name)
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

  if (d_options.dd && minimize)
  {
    std::string dd_trace_file_name = d_options.dd_trace_file_name;
    if (dd_trace_file_name.empty())
    {
      /* Write the minimized trace next to the trace we are minimizing. The
       * api trace file name already includes the output directory, which
       * DD::run() prepends again, hence strip it here. */
      std::string name = api_trace_file_name;
      if (!d_options.out_dir.empty())
      {
        std::filesystem::path rel =
            std::filesystem::path(name).lexically_relative(d_options.out_dir);
        if (!rel.empty() && *rel.begin() != "..")
        {
          name = rel.string();
        }
      }
      dd_trace_file_name = replace_suffix_file_name(name, ".min.trace");
    }
    /* Only print the progress of the delta debugger if verbose output is
     * enabled, the caller reports the result of the minimization instead. */
    std::string minimized = DD(this, seed, d_options.verbosity > 0)
                                .run(api_trace_file_name, dd_trace_file_name);
    if (min_trace_file_name)
    {
      *min_trace_file_name = minimized;
    }
  }
  return res;
}

Solver*
Murxla::new_solver(SolverSeedGenerator& sng,
                   const SolverKind& solver_kind,
                   std::ostream& smt2_out) const
{
  if (solver_kind == SOLVER_BTOR)
  {
#if MURXLA_USE_BOOLECTOR
    return new btor::BtorSolver(sng);
#endif
  }
  else if (solver_kind == SOLVER_BITWUZLA)
  {
#if MURXLA_USE_BITWUZLA
    return new bitwuzla::BitwuzlaSolver(sng);
#endif
  }
  else if (solver_kind == SOLVER_CVC5)
  {
#if MURXLA_USE_CVC5
    return new cvc5::Cvc5Solver(sng, d_options.solver_trace);
#endif
  }
  else if (solver_kind == SOLVER_YICES)
  {
#if MURXLA_USE_YICES
    return new yices::YicesSolver(sng);
#endif
  }
  else if (solver_kind == SOLVER_SMT2)
  {
    return new smt2::Smt2Solver(sng, smt2_out, d_options.solver_binary);
  }
  MURXLA_CHECK(true) << "no solver created";
  return nullptr;
}

Solver*
Murxla::create_solver(SolverSeedGenerator& sng, std::ostream& smt2_out) const
{
  Solver* solver = new_solver(sng, d_options.solver, smt2_out);

  /* If unsat core checking is enabled wrap solver with a CheckSolver. */
  if (d_options.check_solver)
  {
    Solver* reference_solver = new_solver(sng, d_options.check_solver_name);
    solver                   = new CheckSolver(sng, solver, reference_solver);
  }

  if (!d_options.cross_check.empty())
  {
    Solver* reference_solver = new_solver(sng, d_options.cross_check);
    solver = new shadow::ShadowSolver(sng, solver, reference_solver);
  }

  return solver;
}

FSM
Murxla::create_fsm(RNGenerator& rng,
                   SolverSeedGenerator& sng,
                   std::ostream& trace,
                   std::ostream& smt2_out,
                   bool record_stats,
                   bool in_untrace_replay_mode) const
{
  /* Dummy statistics object for the cases were we don't want to record
   * statistics (replay, dd). */
  statistics::Statistics dummy_stats;

  if (!d_options.cmd_line_trace.empty())
  {
    trace << d_options.cmd_line_trace << std::endl;
  }

  return FSM(rng,
             sng,
             create_solver(sng, smt2_out),
             *d_solver_profile,
             trace,
             *d_solver_options,
             d_options.arith_linear,
             d_options.simple_symbols,
             d_options.smtlib_compliant,
             d_options.fuzz_options,
             d_options.fuzz_options_filter,
             record_stats ? d_stats : &dummy_stats,
             d_options.enabled_theories,
             d_options.disabled_theories,
             d_options.solver_options,
             in_untrace_replay_mode);
}

void
Murxla::print_fsm() const
{
  RNGenerator rng(0);
  SolverSeedGenerator sng(0);
  std::ofstream file_smt2_out = open_output_file(DEVNULL, false);
  std::ostream smt2_out(std::cout.rdbuf());
  smt2_out.rdbuf(file_smt2_out.rdbuf());
  FSM fsm = create_fsm(rng, sng, std::cout, smt2_out, false, false);
  fsm.configure();
  fsm.print();
}

Result
Murxla::run_aux(uint64_t seed,
                double time,
                const std::string& file_out,
                const std::string& file_err,
                std::string& api_trace_file_name,
                const std::string& untrace_file_name,
                bool run_forked,
                bool record_stats,
                Murxla::TraceMode trace_mode,
                std::string& error_msg)
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
    /* Disable API trace output if we only want SMT2 or native API calls to
     * stdout. */
    if (d_options.solver == SOLVER_SMT2 || d_options.solver_trace)
    {
      file_trace = open_output_file(DEVNULL, false);
      trace.rdbuf(file_trace.rdbuf());
    }
  }

  /* The global random number generator. Used everywhere, except for in the
   * solvers, which maintain their own RNG, seed with seeds from the solver
   * seed generator. This guarantees that runs can be reproduced even when
   * solvers use the RNG in their API wrapper functions. */
  RNGenerator rng(seed);
  /* The solver seed generator.  Responsible for generating seeds to be used to
   * seed the random generator of the solver. */
  SolverSeedGenerator sng(seed);

  result = RESULT_UNKNOWN;

  /* If seeded, run in main process. */
  if (run_forked)
  {
    /* Flush stdout to make sure that pending output of the parent process is
     * not duplicated by the forked processes. */
    std::cout << std::flush;
    pid_solver = fork();

    MURXLA_CHECK(pid_solver >= 0) << "forking solver process failed.";
  }

  /* parent */
  if (pid_solver)
  {
    /* If a time limit is given, fork another process that kills the pid_solver
     * after time seconds. (https://stackoverflow.com/a/8020324) */
    if (time != 0)
    {
      pid_timeout = fork();

      MURXLA_CHECK(pid_timeout >= 0) << "forking timeout process failed";

      if (pid_timeout == 0)
      {
        signal(SIGINT, SIG_DFL);  // reset stats signal handler
        usleep(static_cast<useconds_t>(time * 1000000));
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
          case EXIT_ERROR_UNTRACE: result = RESULT_ERROR_UNTRACE; break;
          default:
            assert(WEXITSTATUS(status) == EXIT_ERROR);
            result = RESULT_ERROR;
        }
      }
      else if (WIFSIGNALED(status))
      {
        result = RESULT_ERROR;
      }
      if (result == RESULT_ERROR_CONFIG || result == RESULT_ERROR_UNTRACE)
      {
        std::ifstream ferr(file_err);
        std::stringstream ss;
        ss << ferr.rdbuf();
        error_msg = ss.str();
      }
    }
    else
    {
      /* Kill and collect solver process if time limit is exceeded. */
      assert(pid_timeout);
#ifdef MURXLA_COVERAGE
      /* Try to trigger the abort handler to dump coverage information. */
      kill(pid_solver, SIGABRT);
      usleep(100);
#endif
      /* Signal the SMT2 solver to kill the online solver process. */
      if (d_options.solver == SOLVER_SMT2 && !d_options.solver_binary.empty())
      {
        kill(pid_solver, SIGINT);
        usleep(100);
      }
      kill(pid_solver, SIGKILL);
      waitpid(pid_solver, nullptr, 0);
      result = RESULT_TIMEOUT;
    }
  }
  /* child */
  else
  {
    signal(SIGINT, SIG_DFL);  // reset stats signal handler
#ifdef MURXLA_COVERAGE
    signal(SIGABRT, handle_abort);
#endif

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
      FSM fsm = create_fsm(
          rng, sng, trace, smt2_out, record_stats, !untrace_file_name.empty());

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
    catch (MurxlaUntraceException& e)
    {
      MURXLA_EXIT_ERROR_UNTRACE_FORK(true, run_forked) << e.get_msg();
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

std::string
Murxla::filter_error(const std::string& err)
{
  std::string res;
  for (const auto& re : d_error_filters)
  {
    std::smatch sm;
    std::regex_search(err, sm, std::regex(re));
    if (sm.size() == 1)
    {
      res = sm[0];
      break;
    }
  }
  return res.empty() ? err : res;
}

std::tuple<Murxla::ErrorKind, std::string, std::string>
Murxla::prefilter_error(const std::string& err)
{
  std::string filtered_err = filter_error(err);
  /* Strip trailing whitespace up front so that the message stored as a
   * group's representative is byte-identical to what `error.txt` holds and
   * what `load_error_group()` reads back. */
  rstrip(filtered_err);
  std::string err_norm = normalize_asan_error(filtered_err);

  /* Filter errors if specified in the solver profile. */
  for (const auto& e : d_exclude_errors)
  {
    std::smatch sm;
    std::regex_search(filtered_err, sm, std::regex(e));
    if (!sm.empty())
    {
      return std::make_tuple(ErrorKind::FILTER, filtered_err, std::string());
    }

    /* Errors are classified as the same error if they differ in at most 5% of
     * characters. */
    if (error_diff(err_norm, e) <= 0.05)
    {
      return std::make_tuple(ErrorKind::FILTER, filtered_err, std::string());
    }
  }

  return std::make_tuple(ErrorKind::ERROR, filtered_err, err_norm);
}

uint64_t
Murxla::error_group_id(const std::string& normalized_err)
{
  std::string s(normalized_err);
  rstrip(s);
  /* Mask down to what the directory name can represent so that id and
   * directory name are in one-to-one correspondence. Shifting by the full
   * width of the type is undefined, so the case of the name covering the
   * whole hash needs to be spelled out. */
  constexpr size_t bits = 4 * ERROR_GROUP_ID_DIGITS;
  static_assert(bits <= 64, "error group id does not fit into uint64_t");
  constexpr uint64_t mask = bits >= 64 ? UINT64_MAX : (1ULL << bits) - 1;
  uint64_t id             = fnv1a64(s) & mask;
  /* Id 0 is reserved to mean 'not part of an error group'. */
  return id == 0 ? 1 : id;
}

std::string
Murxla::error_group_dir(uint64_t id)
{
  std::stringstream ss;
  ss << std::hex << std::setw(ERROR_GROUP_ID_DIGITS) << std::setfill('0') << id;
  return ss.str();
}

Murxla::ErrorMap::iterator
Murxla::find_error(const std::string& normalized_err)
{
  for (auto it = d_errors->begin(); it != d_errors->end(); ++it)
  {
    /* Errors are classified as the same error if they differ in at most 5% of
     * characters. */
    if (error_diff(normalized_err, it->first) <= 0.05)
    {
      return it;
    }
  }
  return d_errors->end();
}

std::tuple<Murxla::ErrorKind, uint64_t, uint64_t>
Murxla::insert_error(const std::string& filtered_err,
                     const std::string& normalized_err,
                     uint64_t seed)
{
  auto it = find_error(normalized_err);
  if (it != d_errors->end())
  {
    auto& e_info = it->second;
    e_info.seeds.push_back(seed);
    return std::make_tuple(
        ErrorKind::DUPLICATE, e_info.id, e_info.seeds.size());
  }

  /* The new error becomes the representative of its group, hence it is the
   * message the group's id is derived from. */
  const uint64_t id = error_group_id(normalized_err);
  d_errors->emplace(normalized_err, ErrorInfo(id, filtered_err, {seed}));

  if (!d_options.export_errors_filename.empty())
  {
    d_export_errors.push_back(filtered_err);
    export_errors();
  }

  return std::make_tuple(ErrorKind::ERROR, id, 1);
}

void
Murxla::export_errors() const
{
  if (d_options.export_errors_filename.empty())
  {
    return;
  }
  nlohmann::json j;
  j["errors"]["exclude"] = d_export_errors;
  std::ofstream o(d_options.export_errors_filename);
  o << std::setw(2) << j << std::endl;
}

std::tuple<Murxla::ErrorKind, const std::string, uint64_t, uint64_t>
Murxla::add_error(const std::string& err, uint64_t seed)
{
  auto [kind, filtered_err, err_norm] = prefilter_error(err);
  if (kind == ErrorKind::FILTER)
  {
    return std::make_tuple(ErrorKind::FILTER, filtered_err, 0, 0);
  }
  auto [k, error_id, ndup] = insert_error(filtered_err, err_norm, seed);
  return std::make_tuple(k, filtered_err, error_id, ndup);
}

bool
Murxla::load_error_group(const std::string& dir)
{
  std::error_code ec;
  std::filesystem::path errfile = std::filesystem::path(dir) / "error.txt";
  if (!std::filesystem::is_regular_file(errfile, ec))
  {
    return false;
  }

  /* Read error.txt verbatim. test() writes the representative message
   * stripped of trailing whitespace, followed by a single newline, so
   * stripping here recovers it byte for byte. */
  std::ifstream is(errfile, std::ios::binary);
  if (!is.is_open())
  {
    return false;
  }
  std::string errmsg((std::istreambuf_iterator<char>(is)),
                     std::istreambuf_iterator<char>());
  /* A completely empty file means nothing was ever written, so there is no
   * group here. An empty message on the other hand is a group like any
   * other -- a solver that dies without writing to stderr is a failure mode
   * worth keeping track of across runs -- and test() records it as the
   * single newline it appends to the message. */
  if (errmsg.empty())
  {
    return false;
  }
  rstrip(errmsg);

  /* Skip groups that the solver profile excludes by now: the profile may
   * have been extended since the group was recorded, and restoring an error
   * that every new occurrence of is filtered would make the reported error
   * count disagree with what the run actually does.
   *
   * Only the exclusion verdict is taken from prefilter_error(). The message
   * in error.txt has already been through filter_error(), so deriving the
   * map key or the group id from the filtered message it returns here would
   * risk moving the group to a different directory. */
  if (std::get<0>(prefilter_error(errmsg)) == ErrorKind::FILTER)
  {
    return false;
  }

  /* Recover the seeds of all runs recorded for this group from the trace
   * file names. A seed with both a trace and a minimized trace is counted
   * once, and the seeds are sorted so that the error summary of a resumed
   * run does not depend on directory iteration order. */
  std::set<uint64_t> seeds;
  const std::regex re("murxla-([0-9a-fA-F]+)\\.(min\\.)?trace");
  for (const auto& e : std::filesystem::directory_iterator(dir, ec))
  {
    std::smatch sm;
    std::string name = e.path().filename().string();
    if (!std::regex_match(name, sm, re))
    {
      continue;
    }
    try
    {
      seeds.insert(std::stoull(sm[1].str(), nullptr, 16));
    }
    catch (const std::exception&)
    {
      /* Seed does not fit into a uint64_t, so it is not a trace we wrote. */
    }
  }

  std::string norm = normalize_asan_error(errmsg);

  auto it = find_error(norm);
  if (it != d_errors->end())
  {
    /* Some other directory already provided a group this message belongs to,
     * e.g. a directory from an older version of Murxla sitting next to the
     * content-derived directory the same error is written to now. Keep the
     * representative we already have (it owns the group id) and only take
     * over the seeds. */
    auto& e_info = it->second;
    e_info.seeds.insert(e_info.seeds.end(), seeds.begin(), seeds.end());
    return true;
  }

  d_errors->emplace(
      norm,
      ErrorInfo(error_group_id(norm),
                errmsg,
                std::vector<uint64_t>(seeds.begin(), seeds.end())));
  if (!d_options.export_errors_filename.empty())
  {
    d_export_errors.push_back(errmsg);
  }
  return true;
}

void
Murxla::load_state()
{
  /* With no output directory configured, error groups are written to
   * directories below the current working directory. */
  std::string dir = d_options.out_dir.empty() ? "." : d_options.out_dir;

  std::error_code ec;
  if (!std::filesystem::is_directory(dir, ec))
  {
    return;
  }

  /* Sort the candidates so that which message ends up as a group's
   * representative -- and hence which id the group gets -- does not depend on
   * the order the file system happens to report the directories in. */
  std::vector<std::string> dirs;
  for (const auto& e : std::filesystem::directory_iterator(dir, ec))
  {
    if (e.is_directory(ec))
    {
      dirs.push_back(e.path().string());
    }
  }
  std::sort(dirs.begin(), dirs.end());

  size_t nrestored = 0;
  for (const auto& d : dirs)
  {
    nrestored += load_error_group(d) ? 1 : 0;
  }

  /* Errors are exported as they are found, so a resumed run has to export
   * what it restored -- otherwise the exported set would shrink to the
   * errors of the most recent run. */
  if (nrestored > 0)
  {
    export_errors();
  }
}

/* -------------------------------------------------------------------------- */
/* RPC: worker side (-j>1 parallel fuzzing).                                  */
/* -------------------------------------------------------------------------- */

void
Murxla::set_parallel_role(Role role,
                          int rpc_req_fd,
                          int rpc_resp_fd,
                          Aggregate* aggregate)
{
  d_role        = role;
  d_rpc_req_fd  = rpc_req_fd;
  d_rpc_resp_fd = rpc_resp_fd;
  d_aggregate   = aggregate;
}

std::tuple<Murxla::ErrorKind, uint64_t, uint64_t>
Murxla::add_error_via_rpc(const std::string& filtered_err,
                          const std::string& normalized_err,
                          uint64_t seed)
{
  /* Payload layout:
   *   uint64_t seed
   *   uint32_t filtered_err.size()
   *   bytes    filtered_err
   *   uint32_t normalized_err.size()
   *   bytes    normalized_err
   */
  std::string payload;
  payload.resize(sizeof(uint64_t) + sizeof(uint32_t) + filtered_err.size()
                 + sizeof(uint32_t) + normalized_err.size());
  size_t off = 0;
  std::memcpy(&payload[off], &seed, sizeof(seed));
  off += sizeof(seed);
  uint32_t flen = static_cast<uint32_t>(filtered_err.size());
  std::memcpy(&payload[off], &flen, sizeof(flen));
  off += sizeof(flen);
  std::memcpy(&payload[off], filtered_err.data(), flen);
  off += flen;
  uint32_t nlen = static_cast<uint32_t>(normalized_err.size());
  std::memcpy(&payload[off], &nlen, sizeof(nlen));
  off += sizeof(nlen);
  std::memcpy(&payload[off], normalized_err.data(), nlen);

  if (!write_msg(d_rpc_req_fd, (uint8_t) RpcMsg::ADD_ERROR, payload))
  {
    /* Coordinator died; nothing useful we can do. Treat as ERROR with id 0
     * so the worker can still print and exit. */
    return std::make_tuple(ErrorKind::ERROR, 0, 1);
  }

  RpcErrorReply reply{};
  if (!read_all(d_rpc_resp_fd, &reply, sizeof(reply)))
  {
    return std::make_tuple(ErrorKind::ERROR, 0, 1);
  }
  return std::make_tuple(
      static_cast<ErrorKind>(reply.kind), reply.error_id, reply.nduplicates);
}

void
Murxla::log_via_rpc(const std::string& s)
{
  (void) write_msg(d_rpc_req_fd, (uint8_t) RpcMsg::LOG, s);
}

bool
Murxla::serve_rpc_add_error(int req_fd, int resp_fd)
{
  /* Caller has already consumed the message header and verified the type
   * is ADD_ERROR; this method reads the rest. (We don't take that path:
   * the coordinator's main loop reads the header AND the payload via
   * read_msg, then calls into a helper. So serve_rpc_add_error itself is
   * driven by the coordinator's main loop in main.cpp - see below.)
   *
   * For symmetry with the API, we implement the version that reads the
   * full message.
   */
  uint8_t type;
  std::string payload;
  if (!read_msg(req_fd, type, payload)) return false;
  if (type != (uint8_t) RpcMsg::ADD_ERROR) return false;

  if (payload.size() < sizeof(uint64_t) + sizeof(uint32_t)) return false;
  size_t off = 0;
  uint64_t seed;
  std::memcpy(&seed, &payload[off], sizeof(seed));
  off += sizeof(seed);
  uint32_t flen;
  std::memcpy(&flen, &payload[off], sizeof(flen));
  off += sizeof(flen);
  if (off + flen + sizeof(uint32_t) > payload.size()) return false;
  std::string filtered_err(&payload[off], flen);
  off += flen;
  uint32_t nlen;
  std::memcpy(&nlen, &payload[off], sizeof(nlen));
  off += sizeof(nlen);
  if (off + nlen > payload.size()) return false;
  std::string normalized_err(&payload[off], nlen);

  auto [kind, error_id, ndup] =
      insert_error(filtered_err, normalized_err, seed);
  RpcErrorReply reply;
  reply.kind        = static_cast<uint8_t>(kind);
  reply.error_id    = error_id;
  reply.nduplicates = ndup;
  return write_all(resp_fd, &reply, sizeof(reply));
}

void
Murxla::load_solver_profile()
{
  // Create solver instance to query solver profile.
  SolverSeedGenerator sng(0);
  Solver* solver      = create_solver(sng);
  std::string profile = solver->get_profile();
  delete solver;

  // Merge solver profiles if user specified one.
  if (!d_options.solver_profile_filename.empty())
  {
    std::ifstream ifs(d_options.solver_profile_filename);
    std::stringstream buf;
    buf << ifs.rdbuf();
    profile = SolverProfile::merge(profile, buf.str());
  }

  d_solver_profile.reset(new SolverProfile(profile));
  auto errors = d_solver_profile->get_excluded_errors();
  d_exclude_errors.insert(errors.begin(), errors.end());
  auto error_filters = d_solver_profile->get_error_filters();
  d_error_filters.insert(
      d_error_filters.end(), error_filters.begin(), error_filters.end());
  for (const auto& re : d_solver_profile->get_excluded_error_lines())
  {
    d_excluded_error_lines.emplace_back(re);
  }
}

bool
Murxla::is_excluded_error_line(const std::string& line) const
{
  for (const auto& re : d_excluded_error_lines)
  {
    if (std::regex_search(line, re))
    {
      return true;
    }
  }
  return false;
}

std::string
Murxla::get_smt2_file_name(uint64_t seed,
                           const std::string& untrace_file_name) const
{
  std::string smt2_file_name = d_options.smt2_file_name;
  if (smt2_file_name.empty())
  {
    std::stringstream ss;
    if (untrace_file_name.empty())
    {
      ss << "murxla-" << std::hex << seed << ".smt2";
    }
    else
    {
      auto path = std::filesystem::path(untrace_file_name);
      ss << path.replace_extension(".smt2").c_str();
    }
    smt2_file_name = ss.str();
    if (!d_options.out_dir.empty())
    {
      smt2_file_name = prepend_path(d_options.out_dir, smt2_file_name);
    }
  }
  return smt2_file_name;
}

std::string
Murxla::get_api_trace_file_name(uint64_t seed, uint64_t error_id) const
{
  std::string api_trace_file_name = d_options.api_trace_file_name;
  if (api_trace_file_name.empty())
  {
    if (d_options.untrace_file_name.empty())
    {
      std::stringstream ss;
      ss << "murxla-" << std::hex << seed << ".trace";
      api_trace_file_name = ss.str();
    }
    else if (d_options.dd)
    {
      std::stringstream ss;
      ss << "murxla-dd-tmp-" << d_options.untrace_file_name;
      api_trace_file_name = ss.str();
    }
    else
    {
      api_trace_file_name = DEVNULL;
    }
    if (error_id > 0)
    {
      api_trace_file_name =
          prepend_path(error_group_dir(error_id), api_trace_file_name);
    }
    if (!d_options.out_dir.empty())
    {
      api_trace_file_name =
          prepend_path(d_options.out_dir, api_trace_file_name);
    }
  }
  return api_trace_file_name;
}

/* -------------------------------------------------------------------------- */

}  // namespace murxla
