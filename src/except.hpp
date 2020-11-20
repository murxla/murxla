#ifndef __SMTMBT__EXCEPT_HPP_INCLUDED
#define __SMTMBT__EXCEPT_HPP_INCLUDED

#include <sstream>

namespace smtmbt {

/* -------------------------------------------------------------------------- */

class SmtMbtException : public std::exception
{
 public:
  SmtMbtException(const std::string& msg) : d_msg(msg) {}
  SmtMbtException(const std::stringstream& stream) : d_msg(stream.str()) {}
  std::string get_msg() const { return d_msg; }
  const char* what() const noexcept override { return d_msg.c_str(); }

 protected:
  std::string d_msg;
};

class SmtMbtConfigException : public SmtMbtException
{
 public:
  SmtMbtConfigException(const std::string& msg) : SmtMbtException(msg) {}
  SmtMbtConfigException(const std::stringstream& stream)
      : SmtMbtException(stream)
  {
  }
};

class SmtMbtUntraceException : public SmtMbtException
{
 public:
  SmtMbtUntraceException(const std::string& trace_file_name,
                         uint32_t nline,
                         const std::string& msg)
      : SmtMbtException("")
  {
    std::stringstream ss;
    ss << "untrace: " << trace_file_name << ":" << nline << ": " << msg;
    d_msg = ss.str();
  }

  SmtMbtUntraceException(const std::string& trace_file_name,
                         uint32_t nline,
                         const std::stringstream& msg_stream)
      : SmtMbtException("")
  {
    std::stringstream ss;
    ss << "untrace: " << trace_file_name << ":" << nline << ": "
       << msg_stream.str();
    d_msg = ss.str();
  }
  std::string get_msg() const { return d_msg; }
  const char* what() const noexcept override { return d_msg.c_str(); }
};

class SmtMbtActionUntraceException : public SmtMbtException
{
 public:
  SmtMbtActionUntraceException(const std::string& msg) : SmtMbtException(msg) {}
  SmtMbtActionUntraceException(const std::stringstream& stream)
      : SmtMbtException(stream)
  {
  }
};

/* -------------------------------------------------------------------------- */

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

#define SMTMBT_WARN(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & WarnStream().stream()

#define SMTMBT_ABORT(cond) \
  !(cond) ? (void) 0 : OstreamVoider() & AbortStream().stream()

#define SMTMBT_CHECK_CONFIG(cond) \
  (cond) ? (void) 0 : OstreamVoider() & ConfigExceptionStream().stream()

#define SMTMBT_CHECK_TRACE(cond) \
  (cond) ? (void) 0 : OstreamVoider() & UntraceExceptionStream().stream()

#define SMTMBT_CHECK_TRACE_EMPTY(tokens) \
  SMTMBT_CHECK_TRACE((tokens).empty())   \
      << "unexpected argument(s) to '" << get_kind() << "'";

#define SMTMBT_CHECK_TRACE_NOT_EMPTY(tokens) \
  SMTMBT_CHECK_TRACE(!(tokens).empty())      \
      << "expected at least 1 argument to '" << get_kind() << "'";

#define SMTMBT_CHECK_TRACE_NTOKENS(expected, ntokens)                   \
  SMTMBT_CHECK_TRACE((ntokens) == (expected))                           \
      << "expected " << (expected) << " argument(s) to '" << get_kind() \
      << "', got " << (ntokens);

#define SMTMBT_CHECK_TRACE_NTOKENS_MIN(expected, what, ntokens)              \
  SMTMBT_CHECK_TRACE((ntokens) >= (expected))                                \
      << "expected at least " << (expected) << " argument(s)" << what "to '" \
      << get_kind() << "', got " << (ntokens);

#define SMTMBT_CHECK_TRACE_NTOKENS_OF_SORT(expected, ntokens, sort)          \
  SMTMBT_CHECK_TRACE((ntokens) == (expected))                                \
      << "expected " << ((expected) -1) << " argument(s) to '" << get_kind() \
      << "' of sort '" << (sort) << "', got " << ((ntokens) -1);

#define SMTMBT_CHECK_TRACE_SORT(sort, id) \
  SMTMBT_CHECK_TRACE((sort) != nullptr) << "unknown sort id '" << (id) << "'";

#define SMTMBT_CHECK_TRACE_TERM(term, id) \
  SMTMBT_CHECK_TRACE((term) != nullptr) << "unknown term id '" << (id) << "'";

/* -------------------------------------------------------------------------- */
}  // namespace smtmbt

#endif
