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

class MurxlaActionUntraceException : public MurxlaException
{
 public:
  MurxlaActionUntraceException(const std::string& msg) : MurxlaException(msg) {}
  MurxlaActionUntraceException(const std::stringstream& stream)
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
  ~AbortStream();
  AbortStream(const AbortStream& astream) = default;

  std::ostream& stream();

 private:
  void flush();
};

class ExitStream
{
 public:
  ExitStream(ExitCode exit_code = EXIT_ERROR);
  ~ExitStream();
  ExitStream(const ExitStream& astream) = default;

  std::ostream& stream();

 private:
  void flush();
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

#define MURXLA_MESSAGE MessageStream().stream()

#define MURXLA_MESSAGE_DD MessageStream("dd:").stream()

#define MURXLA_WARN(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & WarnStream().stream()

#define MURXLA_ABORT(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & AbortStream().stream()

#define MURXLA_EXIT_ERROR(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & ExitStream().stream()

#define MURXLA_EXIT_ERROR_CONFIG(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & ExitStream(EXIT_ERROR_CONFIG).stream()

#define MURXLA_CHECK(cond) \
  (cond) ? (void) 0 : OstreamVoider() & ExceptionStream().stream()

#define MURXLA_CHECK_CONFIG(cond) \
  (cond) ? (void) 0 : OstreamVoider() & ConfigExceptionStream().stream()

#define MURXLA_CHECK_TRACE(cond) \
  (cond) ? (void) 0 : OstreamVoider() & UntraceExceptionStream().stream()

#define MURXLA_CHECK_TRACE_EMPTY(tokens) \
  MURXLA_CHECK_TRACE((tokens).empty())   \
      << "unexpected argument(s) to '" << get_kind() << "'";

#define MURXLA_CHECK_TRACE_NOT_EMPTY(tokens) \
  MURXLA_CHECK_TRACE(!(tokens).empty())      \
      << "expected at least 1 argument to '" << get_kind() << "'";

#define MURXLA_CHECK_TRACE_NTOKENS(expected, ntokens)                   \
  MURXLA_CHECK_TRACE((ntokens) == (expected))                           \
      << "expected " << (expected) << " argument(s) to '" << get_kind() \
      << "', got " << (ntokens);

#define MURXLA_CHECK_TRACE_NTOKENS_MIN(expected, what, ntokens)              \
  MURXLA_CHECK_TRACE((ntokens) >= (expected))                                \
      << "expected at least " << (expected) << " argument(s)" << what "to '" \
      << get_kind() << "', got " << (ntokens);

#define MURXLA_CHECK_TRACE_NTOKENS_OF_SORT(expected, ntokens, sort)          \
  MURXLA_CHECK_TRACE((ntokens) == (expected))                                \
      << "expected " << ((expected) -1) << " argument(s) to '" << get_kind() \
      << "' of sort '" << (sort) << "', got " << ((ntokens) -1);

#define MURXLA_CHECK_TRACE_SORT(sort, id) \
  MURXLA_CHECK_TRACE((sort) != nullptr) << "unknown sort id '" << (id) << "'";

#define MURXLA_CHECK_TRACE_TERM(term, id) \
  MURXLA_CHECK_TRACE((term) != nullptr) << "unknown term id '" << (id) << "'";

/* -------------------------------------------------------------------------- */
}  // namespace murxla

#endif
