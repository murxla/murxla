/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include "dd.hpp"

#include <chrono>
#include <filesystem>
#include <fstream>

#include "except.hpp"
#include "murxla.hpp"
#include "solver_manager.hpp"
#include "statistics.hpp"
#include "util.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

namespace {
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
split_superset(const std::vector<size_t> superset, size_t subset_size)
{
  std::vector<std::vector<size_t>> subsets;
  size_t superset_size   = superset.size();
  auto begin             = superset.begin();
  auto end               = superset.begin();
  for (size_t lo = 0; end != superset.end(); lo += subset_size)
  {
    size_t hi  = lo + subset_size;
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

DD::DD(Murxla* murxla, uint64_t seed)
    : d_murxla(murxla), d_seed(seed), d_time(0)
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
DD::run(const std::string& input_trace_file_name,
        std::string reduced_trace_file_name)
{
  assert(!input_trace_file_name.empty());

  Result gold_exit;

  std::string tmp_api_trace_file_name =
      get_tmp_file_path(API_TRACE, d_murxla->d_tmp_dir);
  std::string tmp_input_trace_file_name =
      get_tmp_file_path("tmp-dd.trace", d_murxla->d_tmp_dir);

  MURXLA_MESSAGE_DD << "start minimizing file '"
                    << input_trace_file_name.c_str() << "'";

  /* golden run */
  auto start = std::chrono::system_clock::now();
  gold_exit  = d_murxla->run(d_seed,
                            0,
                            d_gold_out_file_name,
                            d_gold_err_file_name,
                            tmp_input_trace_file_name,
                            input_trace_file_name,
                            true,
                            false,
                            Murxla::TraceMode::TO_FILE);
  auto end   = std::chrono::system_clock::now();
  // Compute time limit for delta-debugging tests (3 * golden runtime).
  auto gold_time = std::chrono::duration<double>(end - start).count();
  d_time         = gold_time * 3;

  MURXLA_EXIT_ERROR(gold_exit == RESULT_ERROR_UNTRACE) << d_murxla->d_error_msg;

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
    if (line.rfind("set-murxla-options", 0) == 0)
    {
      d_options_line = line;
      continue;
    }
    if (std::getline(
            std::stringstream(line.erase(0, line.find_first_not_of(' '))),
            token,
            ' ')
        && token == "return")
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
  std::uintmax_t size = std::filesystem::file_size(tmp_input_trace_file_name);
  std::vector<size_t> included_lines(lines.size());
  std::iota(included_lines.begin(), included_lines.end(), 0);
  bool success, fixed_point;

  do
  {
    fixed_point = true;

    success = minimize_lines(
        gold_exit, lines, included_lines, tmp_input_trace_file_name);

    if (!success && iterations > 0) break;

    if (minimize_line(
            gold_exit, lines, included_lines, tmp_input_trace_file_name))
    {
      fixed_point = false;
    }

    if (substitute_terms(
            gold_exit, lines, included_lines, tmp_input_trace_file_name))
    {
      fixed_point = false;
    }

    iterations += 1;
  } while (!fixed_point);

  /* Write minimized trace file to path if given. */
  assert(!reduced_trace_file_name.empty());
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
                      << (static_cast<double>(std::filesystem::file_size(
                              reduced_trace_file_name))
                          / static_cast<double>(size) * 100)
                      << "\% of original size";
  }
  else
  {
    MURXLA_MESSAGE_DD << "unable to reduce api trace";
  }
}

bool
DD::minimize_lines(Result golden_exit,
                   const std::vector<std::vector<std::string>>& lines,
                   std::vector<size_t>& included_lines,
                   const std::string& input_trace_file_name)
{
  MURXLA_MESSAGE_DD << "trying to minimize number of trace lines ...";
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
                                              input_trace_file_name);
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
      subset_size    = n_lines_cur / 2;
      MURXLA_MESSAGE_DD << ">> number of lines reduced to " << std::fixed
                        << std::setprecision(2)
                        << (static_cast<double>(included_lines.size())
                            / static_cast<double>(n_lines) * 100)
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
 * seed         : The line seed.
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
generate_minimized_line(uint64_t seed,
                        Action::Kind action_kind,
                        const std::vector<std::string>& tokens,
                        const std::vector<size_t>& included_args,
                        size_t idx,
                        const std::vector<std::string>& pre,
                        const std::vector<std::string>& post)
{
  std::stringstream ss;
  ss << seed << " " << action_kind;
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
    assert(idx + i < tokens.size());
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
 * lines         : The set of trace lines representing the full (unminimized)
 *                 trace.  A line is represented as a vector of strings with at
 *                 most 2 elements.
 * included_args: The indices of the arguments to minimize that are considered.
 * to_update    : A vector of tuples that represent a line to update and
 *                contain its
 *                - seed
 *                - line index
 *                - action kind
 *                - original tokens
 *                - the start index (in the tokens) of the arguments to minimize
 *
 * return: The previous state of the updated lines as a map from line index to
 *         action line string.
 */
std::unordered_map<size_t, std::string>
update_lines(std::vector<std::vector<std::string>>& lines,
             const std::vector<size_t>& included_args,
             const std::vector<std::tuple<uint64_t,
                                          size_t,
                                          Action::Kind,
                                          std::vector<std::string>,
                                          size_t>>& to_update)
{
  std::unordered_map<size_t, std::string> updated_lines_prev;

  for (const auto& t : to_update)
  {
    uint64_t seed      = std::get<0>(t);
    size_t line_idx    = std::get<1>(t);
    Action::Kind kind  = std::get<2>(t);
    const auto& tokens = std::get<3>(t);
    size_t idx         = std::get<4>(t);

    /* save current state of line in case we need to revert */
    updated_lines_prev[line_idx] = lines[line_idx][0];

    /* determine pre and post terms for generate_minimized_line */
    std::vector<std::string> pre;
    std::vector<std::string> post;

    if (kind == ActionMkSort::s_name)
    {
      post.push_back(tokens[tokens.size() - 1]);
    }
    else if (kind == ActionMkTerm::s_name && tokens[0] == Op::UF_APPLY)
    {
      pre.push_back(std::to_string((included_args.size() + 1)));
      pre.push_back(tokens[idx - 1]);
    }
    else
    {
      pre = {std::to_string((included_args.size()))};
    }
    /* update line */
    lines[line_idx][0] = generate_minimized_line(
        seed, kind, tokens, included_args, idx, pre, post);
  }
  return updated_lines_prev;
}

/**
 * Collect all lines that have to be minimized simultaneously when minimizing a
 * ActionMkSort trace line.
 *
 * lines         : The set of trace lines representing the full (unminimized)
 *                 trace.  A line is represented as a vector of strings with at
 *                 most 2 elements.
 * included_lines: The current set of considered lines.
 * seed          : The line seed.
 * line_idx      : The line index (in 'lines') of the line creating the sort.
 * line_tokens   : The tokenized line at 'line_idx'.
 * term_id       : The id of the term.
 * to_minimize   : The resulting collected lines, given as a vector of tuples
 *                 of seed, line id, action kind, line tokens and the index of
 *                 the first argument of the set of to minimize arguments.
 */
void
collect_to_minimize_lines_sort_fun(
    const std::vector<std::vector<std::string>>& lines,
    const std::vector<size_t>& included_lines,
    uint64_t seed,
    size_t line_idx,
    const std::vector<std::string>& line_tokens,
    std::vector<std::tuple<uint64_t,
                           size_t,
                           Action::Kind,
                           std::vector<std::string>,
                           size_t>>& to_minimize)
{
  /* Add function sort trace line. */
  to_minimize.emplace_back(
      std::make_tuple(seed, line_idx, ActionMkSort::s_name, line_tokens, 1));

  /* Collect all function terms that can occur as an argument to apply
   * (mk_const of the function sort 'sort_id' and ITE over function
   * constants of that sort). Further, collect all applies that need to be
   * updated simultaneously, together with the update of the function sort. */

  /* Retrieve sort id. */
  std::string sort_id;
  {
    assert(lines[line_idx].size() == 2);
    const auto& [seed, action_kind_return, tokens_return] =
        tokenize(lines[line_idx][1]);
    assert(action_kind_return == "return");
    assert(tokens_return.size() == 1);
    sort_id = tokens_return[0];
  }

  /* The function terms. */
  std::unordered_set<std::string> funs;

  for (size_t _line_idx : included_lines)
  {
    if (_line_idx <= line_idx) continue;
    const auto& [seed, action_kind, tokens] = tokenize(lines[_line_idx][0]);
    size_t _n_tokens = tokens.size();
    if (_n_tokens > 0)
    {
      if (action_kind == ActionMkConst::s_name && tokens[0] == sort_id)
      {
        assert(lines[_line_idx].size() == 2);
        const auto& [seed_return, action_kind_return, tokens_return] =
            tokenize(lines[_line_idx][1]);
        assert(action_kind_return == "return");
        assert(tokens_return.size() == 1);
        funs.insert(tokens_return[0]);
      }
      else if (action_kind == ActionMkTerm::s_name && tokens[0] == Op::ITE)
      {
        assert(str_to_uint32(tokens[2]) == 3);
        for (size_t j = 4; j < 6; ++j)
        {
          if (funs.find(tokens[j]) != funs.end())
          {
            assert(lines[_line_idx].size() == 2);
            const auto& [seed_return, action_kind_return, tokens_return] =
                tokenize(lines[_line_idx][1]);
            assert(action_kind_return == "return");
            assert(tokens_return.size() == 2);
            funs.insert(tokens_return[0]);
          }
        }
      }
      else if (action_kind == ActionMkTerm::s_name && tokens[0] == Op::UF_APPLY
               && funs.find(tokens[3]) != funs.end())
      {
        assert(tokens.size() == line_tokens.size() + 2);
        to_minimize.emplace_back(seed, _line_idx, action_kind, tokens, 4);
      }
    }
  }
}

/**
 * Replace all occurrence of string 'from' with string 'to' in string 'str'.
 * Replacement is in place.
 *
 * str : The string in which all occurrences of a given string are to be
 *       replaced.
 * from: The string that is to be replaced in all occurrences.
 * to  : The string that replaces all occurrences of 'from'.
 */
void
str_replace_all(std::string& str,
                const std::string& from,
                const std::string& to)
{
  if (from.empty()) return;
  size_t start_pos = 0;
  while ((start_pos = str.find(from, start_pos)) != std::string::npos)
  {
    str.replace(start_pos, from.length(), to);
    start_pos += to.length();  // In case 'to' contains 'from', like replacing
                               // 'x' with 'yx'
  }
}

/**
 * Collect all lines with ocurrences of 'term_id'.
 *
 * lines            : The set of trace lines representing the full (unminimized)
 *                    trace.  A line is represented as a vector of strings with
 *                    at most 2 elements.
 * included_lines   : The current set of considered lines.
 * line_idx         : The line index (in 'lines') of the line creating const
 *                    'term_id'.
 * term_id          : The id of the term.
 * to_substitute_map: The resulting map of lines to substitute. Maps line index
 *                    to the indices at which 'term_id' occurs in the tokens
 *                    list.
 * to_substitute_idx: A vector of indices of the lines to substitute.
 */
std::vector<size_t>
collect_to_update_lines_mk_const(
    const std::vector<std::vector<std::string>>& lines,
    const std::vector<size_t>& included_lines,
    const std::string& term_id)

{
  std::vector<size_t> res;
  for (size_t line_idx : included_lines)
  {
    const auto& [seed, action_kind, tokens] = tokenize(lines[line_idx][0]);
    if (action_kind == ActionMkConst::s_name) continue;
    for (size_t i = 0, n = tokens.size(); i < n; ++i)
    {
      if (tokens[i] == term_id)
      {
        res.push_back(line_idx);
        break;
      }
    }
  }
  return res;
}

/**
 * Group all term strings occurring in an api trace by sort. Additionally,
 * collect a set of declared (first-order) constants.
 *
 * lines         : The set of trace lines representing the full (unminimized)
 *                 trace.  A line is represented as a vector of strings with at
 *                 most 2 elements.
 * included_lines: The current set of considered lines.
 * consts        : The resulting set of constants.
 * terms         : The resulting set of terms (including constants), grouped
 *                 by sort (given as a map from sort id string to a vector of
 *                 term id strings).
 */
void
collect_terms_by_sort(
    const std::vector<std::vector<std::string>>& lines,
    const std::vector<size_t>& included_lines,
    std::unordered_set<std::string>& consts,
    std::unordered_map<std::string, std::vector<std::string>>& terms)
{
  for (size_t line_idx : included_lines)
  {
    const auto& [seed, action_kind, tokens] = tokenize(lines[line_idx][0]);

    if (action_kind != ActionMkConst::s_name
        && action_kind != ActionMkTerm::s_name)
      continue;

    std::string sort_id, term_id;

    /* It can happen, that the last line triggers an issue in the solver,
     * and no return statement is recorded. */
    assert(line_idx == lines.size() - 1 || lines[line_idx].size() == 2);
    if (lines[line_idx].size() != 2) continue;

    const auto& [seed_return, action_kind_return, tokens_return] =
        tokenize(lines[line_idx][1]);
    assert(action_kind_return == "return");

    if (action_kind == ActionMkConst::s_name)
    {
      sort_id = tokens[0];
      assert(tokens_return.size() == 1);
      term_id = tokens_return[0];
      consts.insert(term_id);
    }
    else
    {
      assert(tokens_return.size() == 2);
      term_id = tokens_return[0];
      sort_id = tokens_return[1];
    }
    terms[sort_id].push_back(term_id);
  }
}
}  // namespace

bool
DD::substitute_terms(Result golden_exit,
                     std::vector<std::vector<std::string>>& lines,
                     std::vector<size_t>& included_lines,
                     const std::string& input_trace_file_name)
{
  MURXLA_MESSAGE_DD << "trying to minimize trace by substituting terms ...";

  bool res = false;

  std::unordered_set<std::string> consts;
  std::unordered_map<std::string, std::vector<std::string>> terms;
  collect_terms_by_sort(lines, included_lines, consts, terms);

  for (const auto& t : terms)
  {
    if (t.second.size() < 2) continue; /* only one term with this sort */

    size_t n_terms = t.second.size();
    bool is_const  = consts.find(t.first) != consts.end();
    bool success   = false;

    for (size_t i = 0; i < n_terms && (is_const || !success); ++i)
    {
      const std::string& term_id = t.second[i];
      for (size_t j = 0, n = t.second.size(); j < n; ++j)
      {
        if (i == j) continue;

        const std::string& term_id_to_substitute = t.second[j];

        /* The line indices of the lines with occurrences. */
        std::vector<size_t> superset = collect_to_update_lines_mk_const(
            lines, included_lines, term_id_to_substitute);

        size_t n_lines     = superset.size();
        size_t n_lines_cur = n_lines;
        size_t subset_size = n_lines;

        while (subset_size > 0)
        {
          std::vector<std::vector<size_t>> subsets =
              split_superset(superset, subset_size);

          std::vector<size_t> superset_cur;
          std::unordered_set<size_t> successful_sets;

          /* We try for each subset if we can replace the term in all of
           * its lines. */
          for (size_t i = 0, n = subsets.size(); i < n; ++i)
          {
            /* Cache previous state of lines to update and update lines. */
            std::unordered_map<size_t, std::string> lines_cur;

            for (size_t line_idx : subsets[i])
            {
              lines_cur[line_idx] = lines[line_idx][0];
              str_replace_all(
                  lines[line_idx][0], term_id_to_substitute, term_id);
            }

            std::vector<size_t> tmp_superset =
                test(golden_exit, lines, included_lines, input_trace_file_name);

            if (!tmp_superset.empty())
            {
              /* success */
              successful_sets.insert(i);
            }
            else
            {
              /* failure */
              superset_cur.insert(
                  superset_cur.end(), subsets[i].begin(), subsets[i].end());
              for (auto l : lines_cur)
              {
                lines[l.first][0] = l.second;
              }
            }
          }
          if (successful_sets.empty())
          {
            subset_size = subset_size / 2;
          }
          else
          {
            /* write found subset immediately to file and continue */
            write_lines_to_file(lines, included_lines, d_tmp_trace_file_name);
            superset    = superset_cur;
            n_lines_cur = superset.size();
            subset_size = n_lines_cur / 2;
            MURXLA_MESSAGE_DD << ">> replaced term '" << term_id_to_substitute
                              << "' with '" << term_id << "' in "
                              << (n_lines - superset.size()) << " lines";
          }
        }
        if (superset.size() < n_lines)
        {
          res     = true;
          success = true;
        }
      }
    }
  }
  return res;
}

bool
DD::minimize_line_aux(Result golden_exit,
                      std::vector<std::vector<std::string>>& lines,
                      const std::vector<size_t>& included_lines,
                      const std::string& input_trace_file_name,
                      size_t n_args,
                      const std::vector<std::tuple<uint64_t,
                                                   size_t,
                                                   Action::Kind,
                                                   std::vector<std::string>,
                                                   size_t>>& to_minimize)
{
  assert(to_minimize.size() >= 1);

  bool res = false;

  /* We minimize based on the first line of the lines to update. For example,
   * when minimizing function sorts, that would be the line to create the sort
   * with ActionMkSort::s_name. */
  size_t line_idx_first   = std::get<1>(to_minimize[0]);
  Action::Kind kind_first = std::get<2>(to_minimize[0]);
  auto tokens_first       = std::get<3>(to_minimize[0]);
  assert(tokens_first.size() >= n_args + 1);

  size_t line_size = lines[line_idx_first][0].size();
  std::vector<size_t> line_superset(n_args);
  std::iota(line_superset.begin(), line_superset.end(), 0);
  size_t subset_size = n_args / 2;

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
      size_t n_included_args            = included_args.size();
      if (n_included_args == 0) continue;
      if (kind_first == ActionMkTerm::s_name && n_included_args < 2)
      {
        continue;
      }

      /* Cache previous state of lines to update and update lines. */
      auto lines_cur = update_lines(lines, included_args, to_minimize);

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
      MURXLA_MESSAGE_DD << ">> line " << line_idx_first << " reduced to "
                        << std::fixed << std::setprecision(2)
                        << (static_cast<double>(lines[line_idx_first][0].size())
                            / static_cast<double>(line_size) * 100)
                        << "% of original size";
    }
  }
  return res;
}

bool
DD::minimize_line(Result golden_exit,
                  std::vector<std::vector<std::string>>& lines,
                  const std::vector<size_t>& included_lines,
                  const std::string& input_trace_file_name)
{
  MURXLA_MESSAGE_DD << "trying to minimize trace lines ...";

  bool res = false;

  /* Create OpKindManager to query Op configuration. */
  statistics::Statistics opmgr_stats;
  TheorySet opmgr_enabled_theories;
  for (int32_t t = 0; t < THEORY_ALL; ++t)
  {
    /* we enable all theories for delta debugging */
    opmgr_enabled_theories.insert(static_cast<Theory>(t));
  }
  OpKindManager opmgr(opmgr_enabled_theories,
                      SolverManager::get_sort_kind_data(opmgr_enabled_theories),
                      {},
                      {},
                      false,
                      &opmgr_stats);
  {
    SolverSeedGenerator opmgr_sng(0);
    std::unique_ptr<Solver> opmgr_solver(d_murxla->create_solver(opmgr_sng));
    opmgr_solver->configure_opmgr(&opmgr);
  }

  /* The set of actions that we consider for this minimization strategy. */
  std::unordered_set<Action::Kind> actions = {
      ActionGetValue::s_name, ActionMkSort::s_name, ActionMkTerm::s_name};

  /* Minimize. */
  size_t line_number = 0;
  for (size_t line_idx : included_lines)
  {
    line_number += lines[line_idx].size();

    /* first item is the action, second (if present) the return statement */
    const auto& [seed, action_kind, tokens] = tokenize(lines[line_idx][0]);

    auto it = actions.find(action_kind);
    if (it == actions.end()) continue;
    const Action::Kind& action = *it;
    size_t idx = 0, n_args = 0, n_tokens = tokens.size();

    /* Collect the data for the lines to update.
     * We have to record the original tokens here -- we can't retokenize these
     * lines on the fly while delta debugging, the set of tokens has to match
     * the indices of the included_args set. */
    std::vector<std::tuple<uint64_t,
                           size_t,
                           Action::Kind,
                           std::vector<std::string>,
                           size_t>>
        to_minimize;

    if (action == ActionMkSort::s_name)
    {
      if (Action::get_sort_kind_from_str(tokens[0]) != SORT_FUN) continue;

      MURXLA_MESSAGE_DD << "trying to minimize function sort on line "
                        << (line_number - lines[line_idx].size() + 1) << " ...";
      n_args = n_tokens - 2;
      collect_to_minimize_lines_sort_fun(
          lines, included_lines, seed, line_idx, tokens, to_minimize);
    }
    else
    {
      MURXLA_MESSAGE_DD << "trying to minimize line "
                        << (line_number - lines[line_idx].size() + 1) << " ...";
      if (action == ActionMkTerm::s_name)
      {
        Op::Kind op_kind = tokens[0];
        Op& op           = opmgr.get_op(op_kind);
        /* op kind not in op datatbase, skip */
        if (op.d_kind == Op::UNDEFINED) continue;
        /* we don't minimize these kinds, skip */
        if (op.d_kind == Op::DT_APPLY_CONS || op.d_kind == Op::DT_MATCH)
        {
          continue;
        }
        /* we only minimize n-ary op kinds */
        if (op.d_arity != MURXLA_MK_TERM_N_ARGS_BIN) continue;
        idx    = 3;
        n_args = str_to_uint32(tokens[2]);
      }
      else
      {
        for (idx = 0; idx < n_tokens; ++idx)
        {
          assert(!tokens[idx].empty());
          if (tokens[idx].find_first_not_of("0123456789") == std::string::npos)
          {
            n_args = str_to_uint32(tokens[idx]);
            idx += 1;
            assert(n_tokens > n_args);
            break;
          }
        }
      }
      to_minimize.emplace_back(
          std::make_tuple(seed, line_idx, action_kind, tokens, idx));
    }

    if (n_args > 0)
    {
      if (minimize_line_aux(golden_exit,
                            lines,
                            included_lines,
                            input_trace_file_name,
                            n_args,
                            to_minimize))
      {
        res = true;
      }
    }
  }
  return res;
}

std::vector<size_t>
DD::test(Result golden_exit,
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
  Result exit = d_murxla->run(d_seed,
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

void
DD::write_lines_to_file(const std::vector<std::vector<std::string>>& lines,
                        const std::vector<size_t> indices,
                        const std::string& out_file_name)
{
  size_t size            = lines.size();
  std::ofstream out_file = open_output_file(out_file_name, false);
  if (!d_options_line.empty())
  {
    out_file << d_options_line << std::endl;
  }
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

/* -------------------------------------------------------------------------- */

}  // namespace murxla
