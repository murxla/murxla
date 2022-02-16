#include "solver/solver_profile.hpp"

#include "except.hpp"
#include "op.hpp"

namespace murxla {

using namespace nlohmann;

SolverProfile::SolverProfile(const std::string& json_str) : d_json_str(json_str)
{
  parse();

  for (int32_t i = 0; i < THEORY_ALL; ++i)
  {
    std::stringstream ss;
    Theory tid = static_cast<Theory>(i);
    ss << tid;
    d_str_to_theory.emplace(ss.str(), tid);
  }

  for (int32_t i = 0; i < SORT_ANY; ++i)
  {
    std::stringstream ss;
    SortKind sk = static_cast<SortKind>(i);
    ss << sk;
    d_str_to_sort_kind.emplace(ss.str(), sk);
  }
}

namespace {

std::string
join(const std::vector<std::string>& strings, const std::string& sep)
{
  std::stringstream ss;
  for (size_t i = 0; i < strings.size(); ++i)
  {
    if (i > 0)
    {
      ss << sep;
    }
    ss << strings[i];
  }
  return ss.str();
}

void
merge_json(json& merged, json& other, const std::string& key = "")
{
  if (merged.is_object() && other.is_object())
  {
    for (auto it = merged.begin(); it != merged.end(); ++it)
    {
      const auto& key = it.key();
      auto itt        = other.find(key);
      // Key exists in other object
      if (itt != other.end())
      {
        merge_json(*it, *itt, key);
      }
    }
    // Check for keys in `other` that are not in `merged`.
    for (auto it = other.begin(); it != other.end(); ++it)
    {
      const auto& key = it.key();
      auto itt        = merged.find(key);
      if (itt == merged.end())
      {
        merged[key] = *it;
      }
    }
  }
  // Merge arrays
  else if (merged.is_array() && other.is_array())
  {
    // Union of values
    if (key == "exclude")
    {
      merged.insert(merged.end(), other.begin(), other.end());
    }
    // Intersection of values
    else if (key == "include")
    {
      auto vm = merged.get<std::unordered_set<std::string>>();
      auto vo = other.get<std::unordered_set<std::string>>();
      merged.clear();
      for (const auto& v : vm)
      {
        if (vo.find(v) != vo.end())
        {
          merged.emplace_back(v);
        }
      }
    }
    // Ignore other keys
  }
}

}  // namespace

std::string
SolverProfile::merge(const std::string& json_str1, const std::string& json_str2)
{
  SolverProfile p1(json_str1);
  SolverProfile p2(json_str2);
  json j1 = p1.d_json;
  json j2 = p2.d_json;

  merge_json(j1, j2);
  return j1.dump();
}

TheoryVector
SolverProfile::get_supported_theories() const
{
  TheorySet solver_theories;
  for (const std::string& t : get_array({KEY_THEORIES, "include"}, true))
  {
    solver_theories.insert(to_theory(t));
  }
  // THEORY_BOOL is always enabled.
  solver_theories.insert(THEORY_BOOL);

  return TheoryVector(solver_theories.begin(), solver_theories.end());
}

std::unordered_map<Theory, std::vector<Theory>>
SolverProfile::get_unsupported_theory_combinations() const
{
  std::unordered_map<Theory, std::vector<Theory>> unsupported;

  auto it = d_json.find(KEY_THEORIES);
  if (it != d_json.end())
  {
    auto itt = it->find(KEY_THEORY_COMBINATIONS);
    if (itt != it->end())
    {
      for (auto i = itt->begin(); i != itt->end(); ++i)
      {
        Theory tid = to_theory(i.key());
        MURXLA_EXIT_ERROR(!i.value().is_array())
            << "Expected list for " << KEY_THEORIES
            << "::" << KEY_THEORY_COMBINATIONS << "::" << tid;
        std::unordered_set<Theory> theories;
        for (const auto& t : i.value())
        {
          Theory tid = to_theory(t.get<std::string>());
          MURXLA_EXIT_ERROR(tid == THEORY_BOOL)
              << tid << " cannot be excluded.";
          theories.insert(tid);
        }
        unsupported.emplace(
            tid, std::vector<Theory>(theories.begin(), theories.end()));
      }
    }
  }
  return unsupported;
}

OpKindSet
SolverProfile::get_unsupported_op_kinds() const
{
  OpKindSet unsupported;
  if (has_key(KEY_OPERATORS))
  {
    auto kinds = get_array({KEY_OPERATORS, "exclude"});
    unsupported.insert(kinds.begin(), kinds.end());
    // TODO: include
  }
  return unsupported;
}

SolverProfile::OpKindSortKindMap
SolverProfile::get_unsupported_op_sort_kinds() const
{
  auto it = d_json.find(KEY_OPERATORS);
  if (it == d_json.end())
  {
    return d_default_unsupported_op_sort_kinds;
  }
  auto itt = it->find(KEY_SORT_RESTR);
  if (itt == it->end())
  {
    return d_default_unsupported_op_sort_kinds;
  }
  MURXLA_EXIT_ERROR(!itt->is_object())
      << "Expected JSON object for `" << KEY_SORT_RESTR << "'";

  OpKindSortKindMap unsupported;
  for (auto i = itt->begin(); i != itt->end(); ++i)
  {
    Op::Kind k = i.key();
    MURXLA_EXIT_ERROR(!i.value().is_array())
        << "Expected list for " << KEY_OPERATORS << "::" << KEY_SORT_RESTR
        << "::" << k;
    SortKindSet sks;
    for (const auto& sk : i.value())
    {
      sks.insert(to_sort_kind(sk.get<std::string>()));
    }
    unsupported.emplace(k, sks);
  }
  return unsupported;
}

SortKindSet
SolverProfile::get_unsupported_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_var_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "var", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_array_index_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "array-index", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_array_element_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "array-element", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_bag_element_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "bag-element", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_dt_match_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "datatype-match", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_dt_sel_codomain_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "datatype-selector-codomain", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_fun_codomain_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "fun-codomain", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_fun_domain_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "fun-domain", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_fun_sort_codomain_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "fun-sort-codomain", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_fun_sort_domain_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "fun-sort-domain", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_get_value_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "get-value", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_seq_element_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "seq-element", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_set_element_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "set-element", "exclude"});
}

SortKindSet
SolverProfile::get_unsupported_sort_param_sort_kinds() const
{
  return get_sort_kinds({KEY_SORTS, "sort-param", "exclude"});
}

std::vector<std::string>
SolverProfile::get_errors() const
{
  std::vector<std::string> errors;
  // Load excluded errors
  auto it = d_json.find(KEY_ERRORS);
  if (it != d_json.end())
  {
    auto itt = it->find("exclude");
    if (itt != it->end() && itt->is_array())
    {
      for (const auto& err : *itt)
      {
        errors.emplace_back(err.get<std::string>());
      }
    }
  }
  return errors;
}

void
SolverProfile::parse()
{
  try
  {
    d_json = nlohmann::json::parse(d_json_str);
  }
  catch (const nlohmann::detail::parse_error& e)
  {
    MURXLA_EXIT_ERROR(true) << e.what() << std::endl;
  }
}

bool
SolverProfile::has_key(const std::string& key) const
{
  return d_json.find(key) != d_json.end();
}

Theory
SolverProfile::to_theory(const std::string& str) const
{
  auto it = d_str_to_theory.find(str);
  MURXLA_EXIT_ERROR_CONFIG(it == d_str_to_theory.end())
      << "Invalid theory id `" << str << "' encountered.";
  return it->second;
}

SortKind
SolverProfile::to_sort_kind(const std::string& str) const
{
  auto it = d_str_to_sort_kind.find(str);
  MURXLA_EXIT_ERROR(it == d_str_to_sort_kind.end())
      << "Unknown sort kind `" << str << "' encountered";
  return it->second;
}

std::vector<std::string>
SolverProfile::get_array(const std::vector<std::string>& keys,
                         bool required) const
{
  std::vector<std::string> res;
  size_t i = 0;
  auto it  = d_json.find(keys[i++]);
  auto end = d_json.end();
  while (it != end && i < keys.size())
  {
    end = it->end();
    it  = it->find(keys[i++]);
  }
  if (it != end)
  {
    MURXLA_EXIT_ERROR_CONFIG(!it->is_array())
        << "Expected list for " << join(keys, "::");
    for (const auto& s : *it)
    {
      res.push_back(s.get<std::string>());
    }
  }
  else if (required)
  {
    MURXLA_EXIT_ERROR_CONFIG(!it->is_array())
        << "Expected list for " << join(keys, "::");
  }
  return res;
}

SortKindSet
SolverProfile::get_sort_kinds(const std::vector<std::string>& keys,
                              bool required) const
{
  SortKindSet kinds;
  for (const auto& k : get_array(keys, required))
  {
    kinds.insert(to_sort_kind(k));
  }
  return kinds;
}

}  // namespace murxla
