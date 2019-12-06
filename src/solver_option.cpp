#include "solver_option.hpp"

#include <iterator>
#include <sstream>

namespace smtmbt {

SolverOption::SolverOption(const std::string& name,
                           std::vector<std::string>& depends,
                           std::vector<std::string>& conflicts)
    : d_name(name), d_depends(depends), d_conflicts(conflicts){};

const std::string&
SolverOption::get_name() const
{
  return d_name;
}

const std::vector<std::string>&
SolverOption::get_conflicts() const
{
  return d_conflicts;
}
const std::vector<std::string>&
SolverOption::get_depends() const
{
  return d_depends;
}

SolverOptionBool::SolverOptionBool(const std::string& name,
                                   std::vector<std::string>& depends,
                                   std::vector<std::string>& conflicts)
    : SolverOption(name, depends, conflicts){};

std::string
SolverOptionBool::pick_value(RNGenerator& rng) const
{
  return rng.flip_coin() ? "true" : "false";
}

SolverOptionInt::SolverOptionInt(const std::string& name,
                                 std::vector<std::string>& depends,
                                 std::vector<std::string>& conflicts,
                                 int32_t min,
                                 int32_t max)
    : SolverOption(name, depends, conflicts), d_min(min), d_max(max){};

std::string
SolverOptionInt::pick_value(RNGenerator& rng) const
{
  std::stringstream ss;
  ss << rng.pick_int32(d_min, d_max);
  return ss.str();
}

SolverOptionList::SolverOptionList(const std::string& name,
                                   std::vector<std::string>& depends,
                                   std::vector<std::string>& conflicts,
                                   std::vector<std::string>& values)
    : SolverOption(name, depends, conflicts), d_values(values){};

std::string
SolverOptionList::pick_value(RNGenerator& rng) const
{
  return d_values[rng.pick_uint32() % d_values.size()];
}

}  // namespace smtmbt
