/***
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */
#ifndef __MURXLA__SOLVER_OPTION_H
#define __MURXLA__SOLVER_OPTION_H

#include <memory>
#include <sstream>
#include <type_traits>
#include <unordered_set>
#include <vector>

#include "rng.hpp"

namespace murxla {

/** Base class representing a solver option. */
class SolverOption
{
 public:
  SolverOption(const std::string& name);
  virtual ~SolverOption() = default;

  /** Pick a random option value. */
  virtual std::string pick_value(RNGenerator& rng) const = 0;

  /** Get the name of the option. */
  const std::string& get_name() const;

 private:
  /** The name of the option. */
  std::string d_name;
};

class SolverOptionBool : public SolverOption
{
 public:
  /** Constructor for Boolean options. */
  SolverOptionBool(const std::string& name, bool default_value);
  ~SolverOptionBool() = default;

  /** Pick random Boolean value. */
  std::string pick_value(RNGenerator& rng) const override;

 private:
  /** The default Boolean value of the option. */
  bool d_default;
};

template <typename T>
class SolverOptionNum : public SolverOption
{
 public:
  /** Constructor for numeric options. */
  SolverOptionNum(const std::string& name,
                  T min,
                  T max,
                  T default_value)
      : SolverOption(name),
        d_min(min),
        d_max(max),
        d_default(default_value){};
  ~SolverOptionNum() = default;

  /** Picks a random numeric value between d_min and d_max. */
  std::string pick_value(RNGenerator& rng) const override
  {
    std::stringstream ss;
    ss << rng.pick<T>(d_min, d_max);
    return ss.str();
  }

 private:
  /** The minimum numeric value of the option. */
  T d_min;
  /** The maximum numeric value of the option. */
  T d_max;
  /** The default numeric value of the option. */
  T d_default;
};

class SolverOptionList : public SolverOption
{
 public:
  /** Constructor for list options. */
  SolverOptionList(const std::string& name,
                   const std::vector<std::string>& values,
                   const std::string& default_value);
  ~SolverOptionList() = default;

  /** Picks a random option value from the list of available values. */
  std::string pick_value(RNGenerator& rng) const override;

 private:
  /** The list of valid option values. */
  std::vector<std::string> d_values;
  /** The default value of the option. */
  std::string d_default;
};

using SolverOptions =
    std::unordered_map<std::string, std::unique_ptr<SolverOption>>;

}  // namespace murxla

#endif
