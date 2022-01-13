#include "except.hpp"

#include <iostream>

namespace murxla {

MessageStream::MessageStream() { stream() << "[murxla] "; }

MessageStream::MessageStream(const std::string& prefix)
{
  stream() << "[murxla] " << prefix << " ";
}

MessageStream::~MessageStream() { flush(); }

std::ostream&
MessageStream::stream()
{
  return std::cout;
}

void
MessageStream::flush()
{
  stream() << std::endl;
  stream().flush();
}

WarnStream::WarnStream() { stream() << "murxla: WARNING: "; }

WarnStream::~WarnStream() { flush(); }

std::ostream&
WarnStream::stream()
{
  return std::cout;
}

void
WarnStream::flush()
{
  stream() << std::endl;
  stream().flush();
}

AbortStream::AbortStream(const std::string& msg_prefix)
{
  stream() << msg_prefix << " ";
}

AbortStream::~AbortStream()
{
  flush();
  std::abort();
}

std::ostream&
AbortStream::stream()
{
  return std::cerr;
}

void
AbortStream::flush()
{
  stream() << std::endl;
  stream().flush();
}

ExitStream::ExitStream(bool is_forked, ExitCode exit_code)
    : d_is_forked(is_forked), d_exit(exit_code)
{
  if (!d_is_forked)
  {
    stream() << "murxla: ERROR: ";
  }
}

ExitStream::~ExitStream()
{
  flush();
  std::exit(d_exit);
}

std::ostream&
ExitStream::stream()
{
  return std::cerr;
}

void
ExitStream::flush()
{
  stream() << std::endl;
  stream().flush();
}

ExceptionStream::ExceptionStream(const ExceptionStream& cstream)
{
  d_ss << cstream.d_ss.rdbuf();
}

ExceptionStream::~ExceptionStream() noexcept(false)
{
  flush();
  throw MurxlaException(d_ss);
}

std::ostream&
ExceptionStream::stream()
{
  return d_ss;
}

void
ExceptionStream::flush()
{
  stream() << std::endl;
  stream().flush();
}

ConfigExceptionStream::ConfigExceptionStream(
    const ConfigExceptionStream& cstream)
{
  d_ss << cstream.d_ss.rdbuf();
}

ConfigExceptionStream::~ConfigExceptionStream() noexcept(false)
{
  flush();
  throw MurxlaConfigException(d_ss);
}

std::ostream&
ConfigExceptionStream::stream()
{
  return d_ss;
}

void
ConfigExceptionStream::flush()
{
  stream() << std::endl;
  stream().flush();
}

UntraceExceptionStream::UntraceExceptionStream(
    const UntraceExceptionStream& cstream)
{
  d_ss << cstream.d_ss.rdbuf();
}

UntraceExceptionStream::~UntraceExceptionStream() noexcept(false)
{
  flush();
  throw MurxlaActionUntraceException(d_ss);
}

std::ostream&
UntraceExceptionStream::stream()
{
  return d_ss;
}

void
UntraceExceptionStream::flush()
{
  stream() << std::endl;
  stream().flush();
}

}  // namespace murxla
