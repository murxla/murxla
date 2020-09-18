#ifndef __SMTMBT__EXCEPT_HPP_INCLUDED
#define __SMTMBT__EXCEPT_HPP_INCLUDED

#include <sstream>

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

#endif
