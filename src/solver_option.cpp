#include "solver_option.hpp"

#include <iterator>
#include <sstream>

namespace murxla {

SolverOption::SolverOption(const std::string& name,
                           const std::vector<std::string>& depends,
                           const std::vector<std::string>& conflicts)
    : d_name(name), d_depends(), d_conflicts()
{
  d_conflicts.insert(conflicts.begin(), conflicts.end());
  d_depends.insert(depends.begin(), depends.end());
};

const std::string&
SolverOption::get_name() const
{
  return d_name;
}

const std::unordered_set<std::string>&
SolverOption::get_conflicts() const
{
  return d_conflicts;
}
const std::unordered_set<std::string>&
SolverOption::get_depends() const
{
  return d_depends;
}

void
SolverOption::add_conflict(const std::string& opt_name)
{
  d_conflicts.insert(opt_name);
}

void
SolverOption::add_depends(const std::string& opt_name)
{
  d_depends.insert(opt_name);
}

SolverOptionBool::SolverOptionBool(const std::string& name,
                                   const std::vector<std::string>& depends,
                                   const std::vector<std::string>& conflicts)
    : SolverOption(name, depends, conflicts){};

std::string
SolverOptionBool::pick_value(RNGenerator& rng) const
{
  return rng.flip_coin() ? "true" : "false";
}

SolverOptionList::SolverOptionList(const std::string& name,
                                   const std::vector<std::string>& values,
                                   const std::vector<std::string>& depends,
                                   const std::vector<std::string>& conflicts)
    : SolverOption(name, depends, conflicts), d_values(values){};

std::string
SolverOptionList::pick_value(RNGenerator& rng) const
{
  return d_values[rng.pick<uint32_t>() % d_values.size()];
}

}  // namespace murxla
