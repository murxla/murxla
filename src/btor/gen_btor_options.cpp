#include <boolector/boolector.h>

#include <iostream>
#include <sstream>
#include <unordered_map>
#include <vector>

std::string
join_options(const std::vector<std::string>& opts)
{
  std::stringstream ss;
  for (size_t i = 0; i < opts.size(); ++i)
  {
    if (i != 0) ss << ", ";
    ss << "\"" << opts[i] << "\"";
  }
  return ss.str();
}

int
main(int argc, char* argv[])
{
  std::unordered_map<std::string, std::vector<std::string>> conflicts;
  std::unordered_map<std::string, std::vector<std::string>> depends;

  // Option conflicts
  conflicts.emplace(std::make_pair(
      "ucopt", std::vector<std::string>({"incremental", "model-gen"})));
  conflicts.emplace(
      std::make_pair("fun-just", std::vector<std::string>({"fun-dual-prop"})));
  conflicts.emplace(std::make_pair(
      "nondestr-subst", std::vector<std::string>({"fun-dual-prop"})));

  // Option dependencies

  Btor* btor = boolector_new();

  std::stringstream ss;
  for (BtorOption opt = boolector_first_opt(btor); boolector_has_opt(btor, opt);
       opt            = boolector_next_opt(btor, opt))
  {
    std::string name = boolector_get_opt_lng(btor, opt);

    ss << "[[option]]" << std::endl;
    ss << "  name =  \"" << name << "\"" << std::endl;
    ss << "  type = \"int\"" << std::endl;
    ss << "  min = " << boolector_get_opt_min(btor, opt) << std::endl;
    ss << "  max = " << boolector_get_opt_max(btor, opt) << std::endl;

    ss << "  depends = [";
    if (depends.find(name) != depends.end())
    {
      ss << join_options(depends.at(name));
    }
    ss << "]" << std::endl;

    ss << "  conflicts = [";
    if (conflicts.find(name) != conflicts.end())
    {
      ss << join_options(conflicts.at(name));
    }
    ss << "]" << std::endl;
  }
  std::cout << ss.str() << std::endl;

  boolector_delete(btor);
  return 0;
}
