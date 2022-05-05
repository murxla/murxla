/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__EXCEPT_HPP_INCLUDED
#define __MURXLA__EXCEPT_HPP_INCLUDED

#include <sstream>

#include "exit.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

/** Base class for exceptions thrown by Murxla. */
class MurxlaException : public std::exception
{
 public:
  /**
   * Constructor.
   * @param msg The exception message.
   */
  MurxlaException(const std::string& msg) : d_msg(msg) {}
  /**
   * Constructor.
   * @param stream The exception message given as a std::stringstream.
   */
  MurxlaException(const std::stringstream& stream) : d_msg(stream.str()) {}
  /**
   * Get the exception message.
   * @return The exception message.
   */
  std::string get_msg() const { return d_msg; }

  const char* what() const noexcept override { return d_msg.c_str(); }

 protected:
  /** The exception message. */
  std::string d_msg;
};

/**
 * The exception used for configuration errors.
 *
 * For example, when passing the wrong arguments to a solver wrapper API
 * function, or when adding an action to a state of the FSM that is a decision
 * state but the actions' next state is neither the same state nor a choice
 * state.
 */
class MurxlaConfigException : public MurxlaException
{
 public:

  /**
   * Constructor.
   * @param msg The exception message.
   */
  MurxlaConfigException(const std::string& msg) : MurxlaException(msg) {}
  /**
   * Constructor.
   * @param stream The exception message given as a std::stringstream.
   */
  MurxlaConfigException(const std::stringstream& stream)
      : MurxlaException(stream)
  {
  }
};

/**
 * The exception used for any issues during untracing.
 *
 * @note Invalid trace tokens encountered in Action::untrace() trigger a
 *       MurxlaActionUntraceException or MurxlaUntraceIdException, which is
 *       then caught and rethrown as MurxlaUntraceException in FSM::untrace().
 */
class MurxlaUntraceException : public MurxlaException
{
 public:
  /**
   * Constructor.
   * @param trace_file_name The name of the trace file.
   * @param nline The line number of the invalid trace line.
   * @param msg The exception message.
   */
  MurxlaUntraceException(const std::string& trace_file_name,
                         uint32_t nline,
                         const std::string& msg)
      : MurxlaException("untrace: " + trace_file_name + ":"
                        + std::to_string(nline) + ": " + msg)
  {
  }
  /**
   * Constructor.
   * @param trace_file_name The name of the trace file.
   * @param nline The line number of the invalid trace line.
   * @param msg The exception message given as a std::stringstream.
   */
  MurxlaUntraceException(const std::string& trace_file_name,
                         uint32_t nline,
                         const std::stringstream& msg_stream)
      : MurxlaException("untrace: " + trace_file_name + ":"
                        + std::to_string(nline) + ": " + msg_stream.str())
  {
  }
};

/**
 * The exception used for trace lines that are invalid due to unknown sort or
 * term ids.
 *
 * This exception is only used in Action::untrace_str_to_id() and caught in
 * rethrown as MurxlaUntraceException in FSM::untrace().
 */
class MurxlaUntraceIdException : public MurxlaException
{
 public:
  /**
   * Constructor.
   * @param msg The exception message.
   */
  MurxlaUntraceIdException(const std::string& msg) : MurxlaException(msg) {}
  /**
   * Constructor.
   * @param msg The exception message given as a std::stringstream.
   */
  MurxlaUntraceIdException(const std::stringstream& stream)
      : MurxlaException(stream)
  {
  }
};

/**
 * The exception used for invalid trace lines encountered during
 * Action::untrace().
 *
 * This exception is thrown in all the MURXLA_CHECK_TRACE_* macros. For
 * trace lines with unknown sort or term ids, we use MurxlaUntraceIdException.
 *
 * This exception is only used in Action::untrace(), and caught and rethrown
 * as MurxlaUntraceException in FSM::untrace().
 */
class MurxlaActionUntraceException : public MurxlaException
{
 public:
  /**
   * Constructor.
   * @param msg The exception message.
   */
  MurxlaActionUntraceException(const std::string& msg) : MurxlaException(msg) {}
  /**
   * Constructor.
   * @param msg The exception message given as a std::stringstream.
   */
  MurxlaActionUntraceException(const std::stringstream& stream)
      : MurxlaException(stream)
  {
  }
};

/**
 * The exception used for invalid solver option configurations in
 * Solver::set_opt().
 */
class MurxlaSolverOptionException : public MurxlaException
{
 public:
  /**
   * Constructor.
   * @param msg The exception message.
   */
  MurxlaSolverOptionException(const std::string& msg) : MurxlaException(msg) {}
  /**
   * Constructor.
   * @param msg The exception message given as a std::stringstream.
   */
  MurxlaSolverOptionException(const std::stringstream& stream)
      : MurxlaException(stream)
  {
  }
};

/* -------------------------------------------------------------------------- */

class MessageStream
{
 public:
  MessageStream();
  MessageStream(const std::string& prefix);
  ~MessageStream();
  MessageStream(const MessageStream& astream) = default;

  std::ostream& stream();

 private:
  void flush();
};

class WarnStream
{
 public:
  WarnStream();
  ~WarnStream();
  WarnStream(const WarnStream& astream) = default;

  std::ostream& stream();

 private:
  void flush();
};

class AbortStream
{
 public:
  AbortStream(const std::string& msg_prefix);
  [[noreturn]] ~AbortStream();
  AbortStream(const AbortStream& astream) = default;

  std::ostream& stream();

 private:
  void flush();
};

class ExitStream
{
 public:
  ExitStream(bool is_forked = false, ExitCode exit_code = EXIT_ERROR);
  [[noreturn]] ~ExitStream();
  ExitStream(const ExitStream& astream) = default;

  std::ostream& stream();

 private:
  void flush();
  bool d_is_forked;
  ExitCode d_exit;
};

class ExceptionStream
{
 public:
  ExceptionStream() {}
  ~ExceptionStream() noexcept(false);
  ExceptionStream(const ExceptionStream& cstream);

  std::ostream& stream();

 private:
  void flush();
  std::stringstream d_ss;
};

class ConfigExceptionStream
{
 public:
  ConfigExceptionStream() {}
  ~ConfigExceptionStream() noexcept(false);
  ConfigExceptionStream(const ConfigExceptionStream& cstream);

  std::ostream& stream();

 private:
  void flush();
  std::stringstream d_ss;
};

class UntraceExceptionStream
{
 public:
  UntraceExceptionStream() {}
  ~UntraceExceptionStream() noexcept(false);
  UntraceExceptionStream(const UntraceExceptionStream& cstream);

  std::ostream& stream();

 private:
  void flush();
  std::stringstream d_ss;
};

class OstreamVoider
{
 public:
  OstreamVoider() = default;
  void operator&(std::ostream& ostream) {}
};

/** Create a message stream. */
#define MURXLA_MESSAGE MessageStream().stream()

/** Create a message stream for the delta debugger. */
#define MURXLA_MESSAGE_DD MessageStream("dd:").stream()

/**
 * Create a warning stream if given condition is not true.
 * @param cond The condition to check.
 */
#define MURXLA_WARN(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & WarnStream().stream()

/**
 * Create an abort stream if given condition is not true.
 * @param cond The condition to check.
 */
#define MURXLA_ABORT(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & AbortStream("murxla: ERROR:").stream()

/**
 * Create an exit stream for general errors in the main process which exits
 * with exit code EXIT_ERROR if given condition is not true.
 * @param cond The condition to check.
 */
#define MURXLA_EXIT_ERROR(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & ExitStream(false).stream()

/**
 * Create an exit stream for configuration errors in the main process which
 * exits with error code EXIT_ERROR_CONFIG if given condition is not true.
 * @param cond The condition to check.
 */
#define MURXLA_EXIT_ERROR_CONFIG(cond) \
  !(cond) ? (void) 0                   \
          : OstreamVoider() & ExitStream(false, EXIT_ERROR_CONFIG).stream()

/**
 * Create an exit stream for general errors in the fork which exits with exit
 * code EXIT_ERROR if given condition is not true. Flag `is_forked` inidcates
 * if process is indeed forked.
 * @param cond The condition to check.
 * @param is_forked True if the process is forked.
 */
#define MURXLA_EXIT_ERROR_FORK(cond, is_forked) \
  !(cond) ? (void) 0 : OstreamVoider() & ExitStream(is_forked).stream()

/**
 * Create an exit stream for configuration errors in the fork which exits with
 * error code EXIT_ERROR_CONFIG if given condition is not true. Flag
 * `is_forked` indicates if process is indeed forked.
 * @param cond The condition to check.
 * @param is_forked True if the process is forked.
 */
#define MURXLA_EXIT_ERROR_CONFIG_FORK(cond, is_forked) \
  !(cond)                                              \
      ? (void) 0                                       \
      : OstreamVoider() & ExitStream(is_forked, EXIT_ERROR_CONFIG).stream()

/**
 * Create an exit stream for untrace errors in the fork which exits with
 * error code EXIT_ERROR_UNTRACE if given condition is not true. Flag
 * `is_forked` indicates if process is indeed forked.
 * @param cond The condition to check.
 * @param is_forked True if the process is forked.
 */
#define MURXLA_EXIT_ERROR_UNTRACE_FORK(cond, is_forked) \
  !(cond)                                               \
      ? (void) 0                                        \
      : OstreamVoider() & ExitStream(is_forked, EXIT_ERROR_UNTRACE).stream()

/**
 * Create an exception stream which throws a MurxlaException if given condition
 * is not true.
 * @param cond The condition to check.
 */
#define MURXLA_CHECK(cond) \
  (cond) ? (void) 0 : OstreamVoider() & ExceptionStream().stream()

/**
 * Create an exception stream which throws a MurxlaConfigException if given
 * condition is not true.
 * @param cond The condition to check.
 */
#define MURXLA_CHECK_CONFIG(cond) \
  (cond) ? (void) 0 : OstreamVoider() & ConfigExceptionStream().stream()

/**
 * \addtogroup macros-check-trace
 * @{
 */

/**
 * Check if condition ``cond`` is true. If it is false, create a
 * murxla::UntraceExceptionStream, which throws a
 * murxla::MurxlaActionUntraceException.
 * @param cond The condition to check.
 */
#define MURXLA_CHECK_TRACE(cond) \
  (cond) ? (void) 0 : OstreamVoider() & UntraceExceptionStream().stream()

/**
 * Check if list of tokens ``tokens`` is empty. If it is not, create a
 * murxla::UntraceExceptionStream, which throws a
 * murxla::MurxlaActionUntraceException.
 * @param tokens The tokenized trace line, a vector strings.
 */
#define MURXLA_CHECK_TRACE_EMPTY(tokens) \
  MURXLA_CHECK_TRACE((tokens).empty())   \
      << "unexpected argument(s) to '" << get_kind() << "'";

/**
 * Check if list of tokens ``tokens`` is not empty. If it is not, create a
 * murxla::UntraceExceptionStream, which throws a
 * murxla::MurxlaActionUntraceException.
 * @param tokens The tokenized trace line, a vector strings.
 */
#define MURXLA_CHECK_TRACE_NOT_EMPTY(tokens) \
  MURXLA_CHECK_TRACE(!(tokens).empty())      \
      << "expected at least 1 argument to '" << get_kind() << "'";

/**
 * Check if given number of trace tokens ``ntokens`` matches the expected
 * number ``expected``. If not, create a murxla::UntraceExceptionStream, which
 * throws a murxla::MurxlaActionUntraceException.
 * @param expected The expected number of tokens.
 * @param ntokens The actual number of tokens.
 */
#define MURXLA_CHECK_TRACE_NTOKENS(expected, ntokens)                   \
  MURXLA_CHECK_TRACE((ntokens) == (expected))                           \
      << "expected " << (expected) << " argument(s) to '" << get_kind() \
      << "', got " << (ntokens);

/**
 * Check if at least as many number of trace tokens are given (``ntokens``) as
 * the number of (min) expected trace tokens (``expected``) and create a
 * murxla::UntraceExceptionStream, which throws a
 * murxla::MurxlaActionUntraceException, if this is not the case. String `what`
 * specifies what kind of trace tokens were expected.
 * @param expected The minimum number of expected trace tokens.
 * @param what A string specifying what kind of trace tokens were expected.
 * @param ntokens The actual number of trace tokens.
 */
#define MURXLA_CHECK_TRACE_NTOKENS_MIN(expected, what, ntokens)              \
  MURXLA_CHECK_TRACE((ntokens) >= (expected))                                \
      << "expected at least " << (expected) << " argument(s)" << what "to '" \
      << get_kind() << "', got " << (ntokens);

/**
 * Check if the given number of trace tokens ``ntokens`` matches the expected
 * number ``expected`` and create a murxla::UntraceExceptionStream, which
 * throws a murxla::MurxlaActionUntraceException, if this is not the case.
 * String `sort` specifies the expected sort of the given tokens.
 * @param expected The number of expected trace tokens.
 * @param sort The expected sort of the given tokens.
 * @param ntokens The actual number of trace tokens.
 */
#define MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(expected, ntokens, sort)          \
  MURXLA_CHECK_TRACE((ntokens) == (expected))                                \
      << "expected " << ((expected) -1) << " argument(s) to '" << get_kind() \
      << "' of sort '" << (sort) << "', got " << ((ntokens) -1);

/**
 * Check if given untraced sort (matched to ``id``) is not null. If it is,
 * create a murxla::UntraceExceptionStream, which throws a
 * murxla::MurxlaActionUntraceException.
 * @param sort The sort to check.
 * @param id The id of the sort.
 */
#define MURXLA_CHECK_TRACE_SORT(sort, id) \
  MURXLA_CHECK_TRACE((sort) != nullptr) << "unknown sort id '" << (id) << "'";

/**
 * Check if given untraced term (matched to ``id``) is not null. If it is,
 * create a murxla::UntraceExceptionStream, which throws a
 * murxla::MurxlaActionUntraceException.
 * @param sort The term to check.
 * @param id The id of the sort.
 */
#define MURXLA_CHECK_TRACE_TERM(term, id) \
  MURXLA_CHECK_TRACE((term) != nullptr) << "unknown term id '" << (id) << "'";

/** @} */

/**
 * Test assertion about a solver's behavior.
 * @param cond The asserted condition.
 */
#define MURXLA_TEST(cond)                                                     \
  (cond) ? (void) 0                                                           \
         : OstreamVoider()                                                    \
               & AbortStream(std::string(__FILE__) + ":"                      \
                             + std::to_string(__LINE__) + ": Check `" + #cond \
                             + "' failed.")                                   \
                     .stream()

/* -------------------------------------------------------------------------- */
}  // namespace murxla

#endif
