#include <iostream>
#include <regex>
#include <sstream>
#include <toml.hpp>
#include <unordered_map>
#include <vector>

std::string
join(const std::vector<std::string>& opts)
{
  std::stringstream ss;
  for (size_t i = 0; i < opts.size(); ++i)
  {
    if (i != 0) ss << ", ";
    ss << "\"" << opts[i] << "\"";
  }
  return ss.str();
}

void
parse_and_export_options(const char* filename)
{
  /* Read the whole file into a string since we have to fix the
   * [[option.mode.*]] lines since toml11 has issues parsing them.
   */
  std::ifstream infile(filename, std::istream::in);
  std::stringstream ss;
  ss << infile.rdbuf();

  /* Replace [[option.mode.<MODE>]] with [[option.mode]]. */
  std::regex r("\\[\\[option.mode..*\\]\\]");
  std::string contents = std::regex_replace(ss.str(), r, "[[option.mode]]");

  /* Parse fixed toml file */
  std::istringstream fixed_contents(contents);
  const auto data = toml::parse(fixed_contents);

  const std::vector<toml::table> tables =
      toml::find_or<std::vector<toml::table>>(
          data, "option", std::vector<toml::table>());

  size_t pos;
  std::string name, type;
  for (const toml::table& table : tables)
  {
    if (table.find("long") == table.end()) continue;

    std::string lng = toml::get<std::string>(table.at("long"));
    pos             = lng.rfind("=");
    name            = (pos == std::string::npos) ? lng : lng.substr(0, pos);
    type            = toml::get<std::string>(table.at("type"));

    std::vector<std::string> mode_values;

    if (type == "bool" || type == "double" || type.rfind("int", 0) == 0
        || type.rfind("unsigned", 0) == 0 || type.rfind("uint", 0) == 0)
    {
    }
    else if (table.find("mode") != table.end())
    {
      type = "list";
      std::vector<toml::table> modes =
          toml::get<std::vector<toml::table>>(table.at("mode"));
      for (const auto& m : modes)
      {
        mode_values.push_back(toml::get<std::string>(m.at("name")));
      }
    }
    else
    {
      /* Skip options with unsupported types. */
      continue;
    }

    std::stringstream ss;
    ss << "[[option]]" << std::endl;
    ss << "  name =  \"" << name << "\"" << std::endl;
    ss << "  type = \"" << type << "\"" << std::endl;

    if (type == "list")
    {
      ss << "  values = [" << join(mode_values) << "]" << std::endl;
    }

    // TODO:
    ss << "  depends = []" << std::endl;
    ss << "  conflicts = []" << std::endl;

    // ss << "  depends = [";
    // if (depends.find(name) != depends.end())
    //{
    //  ss << join_options(depends.at(name));
    //}
    // ss << "]" << std::endl;

    // ss << "  conflicts = [";
    // if (conflicts.find(name) != conflicts.end())
    //{
    //  ss << join_options(conflicts.at(name));
    //}
    // ss << "]" << std::endl;

    std::cout << ss.str() << std::endl;
  }
}

int
main(int argc, char* argv[])
{
  if (argc <= 1)
  {
    std::cerr << "error: no cvc5 *_options.toml files specified." << std::endl;
    return 1;
  }

  for (int i = 1; i < argc; ++i)
  {
    std::cout << "# " << argv[i] << std::endl;
    parse_and_export_options(argv[i]);
  }
  return 0;
}
