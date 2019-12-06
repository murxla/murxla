#ifndef __SMTMBT__SOLVER_OPTION_H
#define __SMTMBT__SOLVER_OPTION_H

#include <memory>
#include <vector>

#include "util.hpp"

namespace smtmbt {

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
  const std::vector<std::string>& get_conflicts() const;
  const std::vector<std::string>& get_depends() const;

 private:
  std::string d_name;
  std::vector<std::string> d_depends;
  std::vector<std::string> d_conflicts;
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

class SolverOptionInt : public SolverOption
{
 public:
  SolverOptionInt(const std::string& name,
                  std::vector<std::string>& depends,
                  std::vector<std::string>& conflicts,
                  int32_t min,
                  int32_t max);
  ~SolverOptionInt() = default;
  std::string pick_value(RNGenerator& rng) const override;

 private:
  int32_t d_min;
  int32_t d_max;
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

}  // namespace smtmbt

#endif
