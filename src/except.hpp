#ifndef __SMTMBT__EXCEPT_HPP_INCLUDED
#define __SMTMBT__EXCEPT_HPP_INCLUDED

#include <sstream>

namespace smtmbt {

/* -------------------------------------------------------------------------- */

class SmtMbtException : public std::exception
{
 public:
  SmtMbtException(const std::string& str) : d_msg(str) {}
  SmtMbtException(const std::stringstream& stream) : d_msg(stream.str()) {}
  std::string get_msg() const { return d_msg; }
  const char* what() const noexcept override { return d_msg.c_str(); }

 private:
  std::string d_msg;
};

class SmtMbtConfigException : public SmtMbtException
{
 public:
  SmtMbtConfigException(const std::string& str) : SmtMbtException(str) {}
  SmtMbtConfigException(const std::stringstream& stream)
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

/* -------------------------------------------------------------------------- */
}  // namespace smtmbt

#endif
