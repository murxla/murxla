#ifndef __MURXLA__SOLVER_OPTION_H
#define __MURXLA__SOLVER_OPTION_H

#include <memory>
#include <sstream>
#include <type_traits>
#include <unordered_set>
#include <vector>

#include "rng.hpp"

namespace murxla {

// TODO: depends and conflicts handling in SolverOption

class SolverOption
{
 public:
  SolverOption(const std::string& name,
               std::vector<std::string>& depends,
               std::vector<std::string>& conflicts);
  virtual ~SolverOption() = default;

  virtual std::string pick_value(RNGenerator& rng) const = 0;

  const std::string& get_name() const;
  const std::unordered_set<std::string>& get_conflicts() const;
  const std::unordered_set<std::string>& get_depends() const;

  void add_conflict(std::string opt_name);
  void add_depends(std::string opt_name);

 private:
  std::string d_name;
  std::unordered_set<std::string> d_depends;
  std::unordered_set<std::string> d_conflicts;
};

class SolverOptionBool : public SolverOption
{
 public:
  SolverOptionBool(const std::string& name,
                   std::vector<std::string>& depends,
                   std::vector<std::string>& conflicts);
  ~SolverOptionBool() = default;
  std::string pick_value(RNGenerator& rng) const override;
};

template <typename T>
class SolverOptionNum : public SolverOption
{
 public:
  SolverOptionNum(const std::string& name,
                  std::vector<std::string>& depends,
                  std::vector<std::string>& conflicts,
                  T min,
                  T max)
      : SolverOption(name, depends, conflicts), d_min(min), d_max(max){};
  ~SolverOptionNum() = default;

  std::string pick_value(RNGenerator& rng) const override
  {
    std::stringstream ss;
    ss << rng.pick<T>(d_min, d_max);
    return ss.str();
  }

 private:
  T d_min;
  T d_max;
};

class SolverOptionList : public SolverOption
{
 public:
  SolverOptionList(const std::string& name,
                   std::vector<std::string>& depends,
                   std::vector<std::string>& conflicts,
                   std::vector<std::string>& values);
  ~SolverOptionList() = default;
  std::string pick_value(RNGenerator& rng) const override;

 private:
  std::vector<std::string> d_values;
};

using SolverOptions = std::vector<std::unique_ptr<SolverOption>>;

}  // namespace murxla

#endif
