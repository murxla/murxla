#include "except.hpp"

#include <iostream>

namespace murxla {

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

AbortStream::AbortStream() { stream() << "murxla: ERROR: "; }

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

ConfigExceptionStream::ConfigExceptionStream(
    const ConfigExceptionStream& cstream)
{
  d_ss << cstream.d_ss.rdbuf();
}

ConfigExceptionStream::~ConfigExceptionStream() noexcept(false)
{
  flush();
  throw SmtMbtConfigException(d_ss);
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
  throw SmtMbtActionUntraceException(d_ss);
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
