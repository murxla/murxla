#ifndef __MURXLA__EXCEPT_HPP_INCLUDED
#define __MURXLA__EXCEPT_HPP_INCLUDED

#include <sstream>

#include "exit.hpp"

namespace murxla {

/* -------------------------------------------------------------------------- */

class MurxlaException : public std::exception
{
 public:
  MurxlaException(const std::string& msg) : d_msg(msg) {}
  MurxlaException(const std::stringstream& stream) : d_msg(stream.str()) {}
  std::string get_msg() const { return d_msg; }
  const char* what() const noexcept override { return d_msg.c_str(); }

 protected:
  std::string d_msg;
};

class MurxlaConfigException : public MurxlaException
{
 public:
  MurxlaConfigException(const std::string& msg) : MurxlaException(msg) {}
  MurxlaConfigException(const std::stringstream& stream)
      : MurxlaException(stream)
  {
  }
};

class MurxlaUntraceException : public MurxlaException
{
 public:
  MurxlaUntraceException(const std::string& trace_file_name,
                         uint32_t nline,
                         const std::string& msg)
      : MurxlaException("")
  {
    std::stringstream ss;
    ss << "untrace: " << trace_file_name << ":" << nline << ": " << msg;
    d_msg = ss.str();
  }

  MurxlaUntraceException(const std::string& trace_file_name,
                         uint32_t nline,
                         const std::stringstream& msg_stream)
      : MurxlaException("")
  {
    std::stringstream ss;
    ss << "untrace: " << trace_file_name << ":" << nline << ": "
       << msg_stream.str();
    d_msg = ss.str();
  }
  std::string get_msg() const { return d_msg; }
  const char* what() const noexcept override { return d_msg.c_str(); }
};

class MurxlaUntraceIdException : public MurxlaException
{
 public:
  MurxlaUntraceIdException(const std::string& msg) : MurxlaException(msg) {}
  MurxlaUntraceIdException(const std::stringstream& stream)
      : MurxlaException(stream)
  {
  }
};

class MurxlaActionUntraceException : public MurxlaException
{
 public:
  MurxlaActionUntraceException(const std::string& msg) : MurxlaException(msg) {}
  MurxlaActionUntraceException(const std::stringstream& stream)
      : MurxlaException(stream)
  {
  }
};

class MurxlaSolverOptionException : public MurxlaException
{
 public:
  MurxlaSolverOptionException(const std::string& msg) : MurxlaException(msg) {}
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
  AbortStream();
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

/** Create a warning stream if given condition is not true. */
#define MURXLA_WARN(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & WarnStream().stream()

/** Create an abort stream if given condition is not true. */
#define MURXLA_ABORT(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & AbortStream().stream()

/**
 * Create an exit stream for general errors in the main process which exits
 * with exit code EXIT_ERROR if given condition is not true.
 */
#define MURXLA_EXIT_ERROR(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & ExitStream(false).stream()

/**
 * Create an exit stream for configuration errors in the main process which
 * exits with error code EXIT_ERROR_CONFIG if given condition is not true.
 */
#define MURXLA_EXIT_ERROR_CONFIG(cond) \
  !(cond) ? (void) 0                   \
          : OstreamVoider() & ExitStream(false, EXIT_ERROR_CONFIG).stream()

/**
 * Create an exit stream for general errors in the fork which exits with exit
 * code EXIT_ERROR if given condition is not true. Flag 'is_forked' inidcates
 * if process is indeed forked.
 */
#define MURXLA_EXIT_ERROR_FORK(cond, is_forked) \
  !(cond) ? (void) 0 : OstreamVoider() & ExitStream(is_forked).stream()

/**
 * Create an exit stream for configuration errors in the fork which exits with
 * error code EXIT_ERROR_CONFIG if given condition is not true. Flag
 * 'is_forked' indicates if process is indeed forked.
 */
#define MURXLA_EXIT_ERROR_CONFIG_FORK(cond, is_forked) \
  !(cond)                                              \
      ? (void) 0                                       \
      : OstreamVoider() & ExitStream(is_forked, EXIT_ERROR_CONFIG).stream()

/**
 * Create an exit stream for untrace errors in the fork which exits with
 * error code EXIT_ERROR_UNTRACE if given condition is not true. Flag
 * 'is_forked' indicates if process is indeed forked.
 */
#define MURXLA_EXIT_ERROR_UNTRACE_FORK(cond, is_forked) \
  !(cond)                                               \
      ? (void) 0                                        \
      : OstreamVoider() & ExitStream(is_forked, EXIT_ERROR_UNTRACE).stream()

/**
 * Create an exception stream which throws a MurxlaException if given condition
 * is not true.
 */
#define MURXLA_CHECK(cond) \
  (cond) ? (void) 0 : OstreamVoider() & ExceptionStream().stream()

/**
 * Create an exception stream which throws a MurxlaConfigException if given
 * condition is not true.
 */
#define MURXLA_CHECK_CONFIG(cond) \
  (cond) ? (void) 0 : OstreamVoider() & ConfigExceptionStream().stream()

/**
 * Create an exception stream which throws a MurxlaUntraceException if given
 * condition is not true.
 */
#define MURXLA_CHECK_TRACE(cond) \
  (cond) ? (void) 0 : OstreamVoider() & UntraceExceptionStream().stream()

/**
 * Check and create an UntraceExceptionStream if given trace tokens are empty.
 */
#define MURXLA_CHECK_TRACE_EMPTY(tokens) \
  MURXLA_CHECK_TRACE((tokens).empty())   \
      << "unexpected argument(s) to '" << get_kind() << "'";

/**
 * Check and create an UntraceExceptionStream if given trace tokens are not
 * empty.
 */
#define MURXLA_CHECK_TRACE_NOT_EMPTY(tokens) \
  MURXLA_CHECK_TRACE(!(tokens).empty())      \
      << "expected at least 1 argument to '" << get_kind() << "'";

/**
 * Check if given number of trace tokens matches the expected number and create
 * an UntraceExceptionStream if this is not the case.
 */
#define MURXLA_CHECK_TRACE_NTOKENS(expected, ntokens)                   \
  MURXLA_CHECK_TRACE((ntokens) == (expected))                           \
      << "expected " << (expected) << " argument(s) to '" << get_kind() \
      << "', got " << (ntokens);

/**
 * Check if at least as many number of trace tokens are given as the number of
 * (min) expected trace tokens and create an UntraceExceptionStream if this is
 * not the case. String 'what' specifies what kind of trace tokens were
 * expected.
 */
#define MURXLA_CHECK_TRACE_NTOKENS_MIN(expected, what, ntokens)              \
  MURXLA_CHECK_TRACE((ntokens) >= (expected))                                \
      << "expected at least " << (expected) << " argument(s)" << what "to '" \
      << get_kind() << "', got " << (ntokens);

/**
 * Check if given number of trace tokens matches the expected number and create
 * an UntraceExceptionStream if this is not the case. String 'sort' specifies
 * the expected sort of the given tokens.
 */
#define MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(expected, ntokens, sort)          \
  MURXLA_CHECK_TRACE((ntokens) == (expected))                                \
      << "expected " << ((expected) -1) << " argument(s) to '" << get_kind() \
      << "' of sort '" << (sort) << "', got " << ((ntokens) -1);

/**
 * Check if given untraced sort is not null. Create an UntraceExceptionStream
 * if this is the case (it is an unknown sort).
 */
#define MURXLA_CHECK_TRACE_SORT(sort, id) \
  MURXLA_CHECK_TRACE((sort) != nullptr) << "unknown sort id '" << (id) << "'";

/**
 * Check if given untraced term is not null. Create an UntraceExceptionStream
 * if this is the case (it is an unknown term).
 */
#define MURXLA_CHECK_TRACE_TERM(term, id) \
  MURXLA_CHECK_TRACE((term) != nullptr) << "unknown term id '" << (id) << "'";

/** Test assertion about a solver's behavior. */
#define MURXLA_TEST(cond)                                        \
  if (!(cond))                                                   \
  {                                                              \
    std::cerr << __FILE__ << ":" << __LINE__ << ": "             \
              << "Check `" << #cond << "' failed." << std::endl; \
    abort();                                                     \
  }

/* -------------------------------------------------------------------------- */
}  // namespace murxla

#endif
