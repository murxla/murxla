/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#include "solver_option.hpp"

#include <iterator>
#include <sstream>

namespace murxla {

SolverOption::SolverOption(const std::string& name)
    : d_name(name)
{
};

const std::string&
SolverOption::get_name() const
{
  return d_name;
}

SolverOptionBool::SolverOptionBool(const std::string& name,
                                   bool default_value)
    : SolverOption(name), d_default(default_value){};

std::string
SolverOptionBool::pick_value(RNGenerator& rng) const
{
  return rng.flip_coin() ? "true" : "false";
}

SolverOptionList::SolverOptionList(const std::string& name,
                                   const std::vector<std::string>& values,
                                   const std::string& default_value)
    : SolverOption(name),
      d_values(values),
      d_default(default_value){};

std::string
SolverOptionList::pick_value(RNGenerator& rng) const
{
  return d_values[rng.pick<uint32_t>() % d_values.size()];
}

}  // namespace murxla
