#include "smt2_solver.hpp"

#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <cassert>
#include <unordered_map>

#include "exit.hpp"
#include "murxla.hpp"

namespace murxla {
namespace smt2 {

/* -------------------------------------------------------------------------- */
/* Smt2Sort                                                                   */
/* -------------------------------------------------------------------------- */

size_t
Smt2Sort::hash() const
{
  return std::hash<std::string>{}(d_repr);
}

bool
Smt2Sort::equals(const Sort& other) const
{
  return d_repr == static_cast<Smt2Sort*>(other.get())->get_repr();
}

std::string
Smt2Sort::to_string() const
{
  return d_repr;
}

bool
Smt2Sort::is_array() const
{
  return d_kind == SORT_ARRAY;
}

bool
Smt2Sort::is_bool() const
{
  return d_kind == SORT_BOOL;
}

bool
Smt2Sort::is_bv() const
{
  return d_kind == SORT_BV;
}

bool
Smt2Sort::is_int() const
{
  return d_kind == SORT_INT;
}

bool
Smt2Sort::is_fp() const
{
  return d_kind == SORT_FP;
}

bool
Smt2Sort::is_fun() const
{
  return d_kind == SORT_FUN;
}

bool
Smt2Sort::is_real() const
{
  return d_kind == SORT_INT || d_kind == SORT_REAL;
}

bool
Smt2Sort::is_rm() const
{
  return d_kind == SORT_RM;
}

bool
Smt2Sort::is_seq() const
{
  return d_kind == SORT_SEQ;
}

bool
Smt2Sort::is_string() const
{
  return d_kind == SORT_STRING;
}

bool
Smt2Sort::is_reglan() const
{
  return d_kind == SORT_REGLAN;
}

uint32_t
Smt2Sort::get_bv_size() const
{
  return d_bv_size;
}

uint32_t
Smt2Sort::get_fp_exp_size() const
{
  return d_bv_size;
}

uint32_t
Smt2Sort::get_fp_sig_size() const
{
  return d_sig_size;
}

const std::string&
Smt2Sort::get_repr() const
{
  return d_repr;
}

Sort
Smt2Sort::get_array_index_sort() const
{
  assert(is_array());
  const Smt2Sort* smt2_index_sort =
      static_cast<const Smt2Sort*>(d_sorts[0].get());
  return std::shared_ptr<Smt2Sort>(new Smt2Sort(smt2_index_sort->get_repr()));
}

Sort
Smt2Sort::get_array_element_sort() const
{
  assert(is_array());
  const Smt2Sort* smt2_element_sort =
      static_cast<const Smt2Sort*>(d_sorts[1].get());
  return std::shared_ptr<Smt2Sort>(new Smt2Sort(smt2_element_sort->get_repr()));
}

uint32_t
Smt2Sort::get_fun_arity() const
{
  assert(is_fun());
  return d_sorts.size() - 1;
}

Sort
Smt2Sort::get_fun_codomain_sort() const
{
  assert(is_fun());
  const Smt2Sort* smt2_codomain_sort =
      static_cast<const Smt2Sort*>(d_sorts.back().get());
  return std::shared_ptr<Smt2Sort>(
      new Smt2Sort(smt2_codomain_sort->get_repr()));
}

std::vector<Sort>
Smt2Sort::get_fun_domain_sorts() const
{
  assert(is_fun());
  assert(d_sorts.size() > 1);
  std::vector<Sort> res;
  for (size_t i = 0, size = d_sorts.size(); i < size - 1; ++i)
  {
    const Smt2Sort* smt2_domain_sort =
        static_cast<const Smt2Sort*>(d_sorts[i].get());
    res.emplace_back(new Smt2Sort(smt2_domain_sort->get_repr()));
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* Smt2Term                                                                   */
/* -------------------------------------------------------------------------- */

size_t
Smt2Term::hash() const
{
  return d_id;
}

bool
Smt2Term::equals(const Term& other) const
{
  const Smt2Term* smt2_term     = static_cast<const Smt2Term*>(other.get());
  const std::vector<Term>& args = smt2_term->get_args();
  const std::vector<uint32_t>& params = smt2_term->get_indices_uint32();
  bool res = d_kind == smt2_term->get_kind() && d_args.size() == args.size()
             && d_indices.size() == params.size();
  if (res)
  {
    for (size_t i = 0, n = args.size(); i < n; ++i)
    {
      if (d_args[i] != args[i])
      {
        res = false;
        break;
      }
    }
  }

  if (res)
  {
    for (size_t i = 0, n = params.size(); i < n; ++i)
    {
      if (d_indices[i] != params[i])
      {
        res = false;
        break;
      }
    }
  }
  return res;
}

std::string
Smt2Term::to_string() const
{
  return d_repr;
}

const std::string&
Smt2Term::get_kind() const
{
  return d_kind;
}

std::vector<Term>
Smt2Term::get_children() const
{
  return d_args;
}

const std::vector<Term>&
Smt2Term::get_args() const
{
  return d_args;
}

const std::vector<uint32_t>&
Smt2Term::get_indices_uint32() const
{
  return d_indices;
}

const Smt2Term*
to_smt2_term(const Term& t)
{
  return static_cast<const Smt2Term*>(t.get());
}

const std::string
Smt2Term::get_repr() const
{
  std::vector<const Smt2Term*> visit;
  std::unordered_map<const Smt2Term*, std::string> cache;
  std::unordered_map<const Smt2Term*, uint64_t> refs;
  std::vector<std::string> lets;

  // Compute references
  visit.push_back(this);
  while (!visit.empty())
  {
    const Smt2Term* cur = visit.back();
    visit.pop_back();

    const auto& it = cache.find(cur);
    if (it == cache.end())
    {
      cache.emplace(cur, "");
      /* Do not go below quantifiers. */
      if (cur->d_kind == Op::FORALL || cur->d_kind == Op::EXISTS)
      {
        continue;
      }
      for (const auto& arg : cur->d_args)
      {
        visit.push_back(to_smt2_term(arg));
        refs[visit.back()] += 1;
      }
      continue;
    }
  }

  cache.clear();
  visit.push_back(this);
  while (!visit.empty())
  {
    const Smt2Term* cur = visit.back();

    const auto& it = cache.find(cur);
    if (it == cache.end())
    {
      cache.emplace(cur, "");
      for (const auto& arg : cur->d_args)
      {
        visit.push_back(to_smt2_term(arg));
      }
      continue;
    }
    else
    {
      std::stringstream res;

      size_t i = 0;
      if (cur->d_leaf_kind != LeafKind::NONE)
      {
        assert(!cur->d_repr.empty());
        res << cur->d_repr;
      }
      else
      {
        if (cur->d_indices.empty())
        {
          res << "(";
          if (cur->d_kind == Op::UF_APPLY)
          {
            res << to_smt2_term(cur->d_args[0])->get_repr();
            i += 1;
          }
          else
          {
            res << d_op_kind_to_str.at(cur->d_kind);
          }
          if (cur->d_kind == Op::FORALL || cur->d_kind == Op::EXISTS)
          {
            assert(cur->d_args.size() > 1);
            /* print bound variables, body is last argument term in d_args */
            res << " (";
            for (size_t size = cur->d_args.size() - 1; i < size; ++i)
            {
              if (i > 0) res << " ";
              const Smt2Term* smt2_term = to_smt2_term(cur->d_args[i]);
              assert(smt2_term->d_leaf_kind == LeafKind::VAR);
              Smt2Sort* smt2_sort =
                  static_cast<Smt2Sort*>(cur->d_args[i]->get_sort().get());

              const auto itt = cache.find(smt2_term);
              assert(itt != cache.end());
              assert(!itt->second.empty());

              res << "(" << itt->second << " " << smt2_sort->get_repr() << ")";
            }
            res << ")";
          }
        }
        else
        {
          res << "((_ " << d_op_kind_to_str.at(cur->d_kind);
          for (uint32_t p : cur->d_indices)
          {
            res << " " << p;
          }
          res << ")";
        }
        for (size_t size = cur->d_args.size(); i < size; ++i)
        {
          const auto itt = cache.find(to_smt2_term(cur->d_args[i]));
          assert(itt != cache.end());
          assert(!itt->second.empty());
          res << " " << itt->second;
        }
        res << ")";
      }

      if (it->second.empty())
      {
        uint64_t nrefs = refs[cur];

        if (nrefs > 1 && cur->d_leaf_kind == LeafKind::NONE)
        {
          std::stringstream let;
          let << "_let" << lets.size() / 2;
          lets.push_back(let.str());
          lets.push_back(res.str());
          it->second = let.str();
        }
        else
        {
          it->second = res.str();
        }
      }
    }
    visit.pop_back();
  }

  auto itt = cache.find(this);
  assert(itt != cache.end());
  assert(!itt->second.empty());
  std::string t = itt->second;

  std::stringstream res;
  if (!lets.empty())
  {
    std::stringstream close;
    for (size_t i = 0; i < lets.size(); i += 2)
    {
      res << "(let ((" << lets[i] << " " << lets[i + 1] << "))";
      close << ")";
    }
    res << itt->second << close.str();
  }
  else
  {
    res << itt->second;
  }

  return res.str();
}

/* -------------------------------------------------------------------------- */
/* Smt2Solver                                                                 */
/* -------------------------------------------------------------------------- */

/* Trim whitespaces (in place) from given str. */
static void
trim_str(std::string& s)
{
  /* trim from left */
  s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](int ch) {
            return !std::isspace(ch);
          }));
  /* trim from right */
  s.erase(std::find_if(
              s.rbegin(), s.rend(), [](int ch) { return !std::isspace(ch); })
              .base(),
          s.end());
}

void
Smt2Solver::push_to_external(std::string s, ResponseKind expected)
{
  assert(d_file_to);
  assert(d_file_from);
  fputs(s.c_str(), d_file_to);
  fputc('\n', d_file_to);
  fflush(d_file_to);
  std::string res = get_from_external();
  trim_str(res);
  switch (expected)
  {
    case ResponseKind::SMT2_SUCCESS:
      if (res != "success")
      {
        std::cerr << "[murxla] SMT2: Error: expected 'success' response from "
                     "online solver but got '"
                  << res << "'" << std::endl;
        exit(EXIT_ERROR);
      }
      break;
    case ResponseKind::SMT2_SAT:
      if (res != "sat" && res != "unsat" && res != "unknown")
      {
        std::cerr << "[murxla] SMT2: Error: expected 'sat', 'unsat' or "
                     "'unknown' response from online solver but got '"
                  << res << "'" << std::endl;
        exit(EXIT_ERROR);
      }
      if (res == "sat")
      {
        d_last_result = Solver::Result::SAT;
      }
      else if (res == "unsat")
      {
        d_last_result = Solver::Result::UNSAT;
      }
      else if (res == "unknown")
      {
        d_last_result = Solver::Result::UNKNOWN;
      }
      break;
    default:
      assert(expected == ResponseKind::SMT2_SEXPR);
      if (res[0] != '(' || res.find("error") != std::string::npos
          || res.find("Error") != std::string::npos
          || res.find("ERROR") != std::string::npos)
      {
        std::cerr << "[murxla] SMT2: Error: expected S-expression response "
                     "from online solver but got '"
                  << res << "'" << std::endl;
        exit(EXIT_ERROR);
      }
  }
}

/**
 * Either parses one line or an s-expression if the first character of the
 * stream is '('.
 */
std::string
Smt2Solver::get_from_external() const
{
  std::vector<std::string> lines;
  std::stringstream ss;
  size_t in_sexpr = 0;
  size_t nchars   = 0;
  while (true)
  {
    int32_t c = fgetc(d_file_from);
    ++nchars;
    if (c == EOF)
    {
      return "[EOF]";
    }
    else if (c == '(' && (in_sexpr || nchars == 1))
    {
      ++in_sexpr;
    }
    else if (c == ')' && in_sexpr)
    {
      --in_sexpr;
    }

    ss << ((char) c);
    if (c == '\n')
    {
      lines.push_back(ss.str());
      ss.str("");
      ss.clear();
    }
    if (c == '\n' && !in_sexpr)
    {
      break;
    }
  }
  std::string res;
  for (auto& line : lines)
  {
    d_out << "; " << line;
    res += line;
  }
  d_out << std::flush;
  return res;
}

void
Smt2Solver::dump_smt2(std::string s, ResponseKind expected)
{
  d_out << s << std::endl << std::flush;
  if (d_online) push_to_external(s, expected);
}

Smt2Solver::Smt2Solver(SolverSeedGenerator& sng,
                       std::ostream& out,
                       const std::string& solver_binary)
    : Solver(sng),
      d_out(out),
      d_online(!solver_binary.empty()),
      d_file_to(nullptr),
      d_file_from(nullptr),
      d_solver_call(solver_binary)
{
  if (d_online)
  {
    int32_t fd_to[2], fd_from[2];

    /* Open input/output pipes from and to the external online solver. */
    MURXLA_EXIT_ERROR(pipe(fd_to) != 0) << "creating input pipe failed";
    MURXLA_EXIT_ERROR(pipe(fd_from) != 0) << "creating output pipe failed";

    d_online_pid = fork();

    MURXLA_EXIT_ERROR_FORK(d_online_pid < 0, true)
        << "forking solver process failed.";

    /* Online solver process. */
    if (d_online_pid == 0)
    {
      close(fd_to[SMT2_WRITE_END]);
      dup2(fd_to[SMT2_READ_END], STDIN_FILENO);

      close(fd_from[SMT2_READ_END]);
      /* Redirect stdout of external solver to write end. */
      dup2(fd_from[SMT2_WRITE_END], STDOUT_FILENO);
      /* Redirect stderr of external solver to write end. */
      dup2(fd_from[SMT2_WRITE_END], STDERR_FILENO);

      std::vector<char*> execv_args;
      std::string arg;
      std::stringstream ss(d_solver_call);
      while (std::getline(ss, arg, ' '))
      {
        execv_args.push_back(strdup(arg.c_str()));
      }
      execv_args.push_back(nullptr);

      execv(execv_args[0], execv_args.data());

      for (char* s : execv_args)
      {
        free(s);
      }

      MURXLA_EXIT_ERROR_FORK(true, true)
          << "'" << d_solver_call << "' is not executable";
    }

    close(fd_to[SMT2_READ_END]);
    close(fd_from[SMT2_WRITE_END]);
    d_file_to   = fdopen(fd_to[SMT2_WRITE_END], "w");
    d_file_from = fdopen(fd_from[SMT2_READ_END], "r");

    MURXLA_EXIT_ERROR_FORK(d_file_to == nullptr, true)
        << "opening read channel to external solver failed";
    MURXLA_EXIT_ERROR_FORK(d_file_from == nullptr, true)
        << "opening write channel to external solver failed";
  }
}

Smt2Solver::~Smt2Solver()
{
  if (d_online)
  {
    assert(d_online_pid);
    waitpid(d_online_pid, nullptr, 0);
  }
}

void
Smt2Solver::new_solver()
{
  d_initialized = true;
  if (d_online)
  {
    dump_smt2("(set-option :print-success true)");
  }
  dump_smt2("(set-logic ALL)");
}

void
Smt2Solver::delete_solver()
{
  dump_smt2("(exit)");
}

bool
Smt2Solver::is_initialized() const
{
  return d_initialized;
}

const std::string
Smt2Solver::get_name() const
{
  return "Smt2";
}

Term
Smt2Solver::mk_var(Sort sort, const std::string& name)
{
  std::string symbol = name;
  if (name.empty())
  {
    std::stringstream ss;
    ss << "_v" << d_n_unnamed_vars++;
    symbol = ss.str();
  }
  return std::shared_ptr<Smt2Term>(
      new Smt2Term(Op::UNDEFINED, {}, {}, Smt2Term::LeafKind::VAR, symbol));
}

Term
Smt2Solver::mk_const(Sort sort, const std::string& name)
{
  std::stringstream smt2;
  std::string symbol = name;

  Smt2Sort* smt2_sort = static_cast<Smt2Sort*>(sort.get());
  if (sort->get_kind() == SORT_FUN)
  {
    if (name.empty())
    {
      std::stringstream ss;
      ss << "_f" << d_n_unnamed_ufs++;
      symbol = ss.str();
    }
    smt2 << "(declare-fun " << symbol << " " << smt2_sort->get_repr() << ")";
  }
  else
  {
    if (name.empty())
    {
      std::stringstream ss;
      ss << "_c" << d_n_unnamed_consts++;
      symbol = ss.str();
    }
    smt2 << "(declare-const " << symbol << " " << smt2_sort->get_repr() << ")";
  }
  dump_smt2(smt2.str());
  return std::shared_ptr<Smt2Term>(
      new Smt2Term(Op::UNDEFINED, {}, {}, Smt2Term::LeafKind::CONST, symbol));
}

Term
Smt2Solver::mk_fun(Sort sort, const std::string& name)
{
  // TODO
  return nullptr;
}

Term
Smt2Solver::mk_value(Sort sort, bool value)
{
  assert(sort->is_bool());
  std::string val = value ? "true" : "false";
  return std::shared_ptr<Smt2Term>(
      new Smt2Term(Op::UNDEFINED, {}, {}, Smt2Term::LeafKind::VALUE, val));
}

Term
Smt2Solver::mk_value(Sort sort, std::string value)
{
  SortKind sort_kind = sort->get_kind();
  std::stringstream val;

  switch (sort_kind)
  {
    case SORT_FP:
    {
      val << "(fp ";
      uint32_t ew      = sort->get_fp_exp_size();
      std::string sign = value.substr(0, 1);
      std::string exp  = value.substr(1, ew);
      std::string sig  = value.substr(1 + ew);
      val << "#b" << sign << " #b" << exp << " #b" << sig << ")";
    }
    break;

    case SORT_INT:
      assert(sort->is_int());
      val << value;
      break;

    case SORT_REAL:
    {
      assert(sort->is_real());
      size_t pos = value.find('/');
      if (pos != std::string::npos)
      {
        assert(pos > 0);
        std::string num = value.substr(0, pos - 1);
        std::string den = value.substr(pos + 1);
        val << "(/ " << num << " " << den << ")";
      }
      else
      {
        val << value;
      }
    }
    break;

    case SORT_STRING:
      assert(sort->is_string());
      val << "\"" << value << "\"";
      break;

    default: assert(false);
  }
  return std::shared_ptr<Smt2Term>(new Smt2Term(
      Op::UNDEFINED, {}, {}, Smt2Term::LeafKind::VALUE, val.str()));
}

Term
Smt2Solver::mk_value(Sort sort, std::string num, std::string den)
{
  assert(sort->is_real());
  std::stringstream val;
  val << "(/ " << num << " " << den << ")";
  return std::shared_ptr<Smt2Term>(new Smt2Term(
      Op::UNDEFINED, {}, {}, Smt2Term::LeafKind::VALUE, val.str()));
}

Term
Smt2Solver::mk_value(Sort sort, std::string value, Base base)
{
  assert(sort->is_bv());
  std::stringstream val;

  switch (base)
  {
    case DEC:
      val << "(_ bv" << value << " " << sort->get_bv_size() << ")";
      break;

    case HEX:
      assert(sort->get_bv_size() % 4 == 0);
      val << "#x" << value;
      break;

    default:
      assert(base == BIN);
      assert(sort->get_bv_size() == value.size());
      val << "#b" << value;
      break;
  }
  return std::shared_ptr<Smt2Term>(new Smt2Term(
      Op::UNDEFINED, {}, {}, Smt2Term::LeafKind::VALUE, val.str()));
}

Term
Smt2Solver::mk_special_value(Sort sort, const AbsTerm::SpecialValueKind& value)
{
  std::stringstream val;

  switch (sort->get_kind())
  {
    case SORT_BV:
    {
      uint32_t bw = sort->get_bv_size();
      if (value == AbsTerm::SPECIAL_VALUE_BV_ZERO)
      {
        val << "#b" << bv_special_value_zero_str(bw);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_ONE)
      {
        val << "#b" << bv_special_value_one_str(bw);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_ONES)
      {
        val << "#b" << bv_special_value_ones_str(bw);
      }
      else if (value == AbsTerm::SPECIAL_VALUE_BV_MIN_SIGNED)
      {
        val << "#b" << bv_special_value_min_signed_str(bw);
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_BV_MAX_SIGNED);
        val << "#b" << bv_special_value_zero_str(bw);
      }
    }
    break;

    case SORT_FP:
    {
      if (value == AbsTerm::SPECIAL_VALUE_FP_POS_INF)
      {
        val << "(_ +oo ";
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_NEG_INF)
      {
        val << "(_ -oo ";
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_POS_ZERO)
      {
        val << "(_ +zero ";
      }
      else if (value == AbsTerm::SPECIAL_VALUE_FP_NEG_ZERO)
      {
        val << "(_ -zero ";
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_FP_NAN);
        val << "(_ NaN ";
      }
      val << sort->get_fp_exp_size() << " " << sort->get_fp_sig_size() << ")";
    }
    break;

    case SORT_RM:
      if (value == AbsTerm::SPECIAL_VALUE_RM_RNE)
      {
        val << (d_rng.flip_coin() ? "RNE" : "roundNearestTiesToEven");
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RNA)
      {
        val << (d_rng.flip_coin() ? "RNA" : "roundNearestTiesToAway");
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RTN)
      {
        val << (d_rng.flip_coin() ? "RTN" : "roundTowardNegative");
      }
      else if (value == AbsTerm::SPECIAL_VALUE_RM_RTP)
      {
        val << (d_rng.flip_coin() ? "RTP" : "roundTowardPositive");
      }
      else
      {
        assert(value == AbsTerm::SPECIAL_VALUE_RM_RTZ);
        val << (d_rng.flip_coin() ? "RTZ" : "roundTowardZero");
      }
      break;

    default: assert(false);
  }
  return std::shared_ptr<Smt2Term>(new Smt2Term(
      Op::UNDEFINED, {}, {}, Smt2Term::LeafKind::VALUE, val.str()));
}

static std::string
get_bool_sort_string()
{
  return "Bool";
}

static std::string
get_int_sort_string()
{
  return "Int";
}

static std::string
get_real_sort_string()
{
  return "Real";
}

static std::string
get_rm_sort_string()
{
  return "RoundingMode";
}

static std::string
get_string_sort_string()
{
  return "String";
}

static std::string
get_reglan_sort_string()
{
  return "RegLan";
}

static std::string
get_bv_sort_string(uint32_t size)
{
  std::stringstream sort;
  sort << "(_ BitVec " << size << ")";
  return sort.str();
}

static std::string
get_fp_sort_string(uint32_t esize, uint32_t ssize)
{
  std::stringstream sort;
  sort << "(_ FloatingPoint " << esize << " " << ssize << ")";
  return sort.str();
}

static std::string
get_array_sort_string(const std::vector<Sort>& sorts)
{
  std::stringstream sort;
  sort << "(Array";
  for (const Sort& s : sorts)
  {
    sort << " " << static_cast<const Smt2Sort*>(s.get())->get_repr();
  }
  sort << ")";
  return sort.str();
}

static std::string
get_fun_sort_string(const std::vector<Sort>& sorts)
{
  std::stringstream sort;
  sort << "(";
  for (auto it = sorts.begin(); it < sorts.end() - 1; ++it)
  {
    if (it > sorts.begin())
    {
      sort << " ";
    }
    sort << static_cast<const Smt2Sort*>(it->get())->get_repr();
  }
  sort << ") ";
  sort << static_cast<const Smt2Sort*>(sorts.back().get())->get_repr();
  return sort.str();
}

static std::string
get_seq_sort_string(const std::vector<Sort>& sorts)
{
  assert(sorts.size() == 1);
  std::stringstream sort;
  sort << "(Seq";
  sort << " " << static_cast<const Smt2Sort*>(sorts[0].get())->get_repr();
  sort << ") ";
  return sort.str();
}

Sort
Smt2Solver::mk_sort(const std::string name, uint32_t arity)
{
  // TODO
  return nullptr;
}

Sort
Smt2Solver::mk_sort(SortKind kind)
{
  std::string sort;
  switch (kind)
  {
    case SORT_BOOL: sort = get_bool_sort_string(); break;
    case SORT_INT: sort = get_int_sort_string(); break;
    case SORT_REAL: sort = get_real_sort_string(); break;
    case SORT_RM: sort = get_rm_sort_string(); break;
    case SORT_STRING: sort = get_string_sort_string(); break;
    case SORT_REGLAN: sort = get_reglan_sort_string(); break;
    default: assert(false);
  }
  return std::shared_ptr<Smt2Sort>(new Smt2Sort(sort));
}

Sort
Smt2Solver::mk_sort(SortKind kind, uint32_t size)
{
  std::string sort;
  switch (kind)
  {
    case SORT_BV: sort = get_bv_sort_string(size); break;
    default: assert(false);
  }
  return std::shared_ptr<Smt2Sort>(new Smt2Sort(sort, size));
}

Sort
Smt2Solver::mk_sort(SortKind kind, uint32_t esize, uint32_t ssize)
{
  std::string sort;
  switch (kind)
  {
    case SORT_FP: sort = get_fp_sort_string(esize, ssize); break;
    default: assert(false);
  }
  return std::shared_ptr<Smt2Sort>(new Smt2Sort(sort, esize, ssize));
}

Sort
Smt2Solver::mk_sort(SortKind kind, const std::vector<Sort>& sorts)
{
  std::string sort;
  switch (kind)
  {
    case SORT_ARRAY: sort = get_array_sort_string(sorts); break;
    case SORT_FUN: sort = get_fun_sort_string(sorts); break;
    case SORT_SEQ: sort = get_seq_sort_string(sorts); break;
    default: assert(false);
  }
  return std::shared_ptr<Smt2Sort>(new Smt2Sort(sort));
}

Term
Smt2Solver::mk_term(const Op::Kind& kind,
                    const std::vector<Term>& args,
                    const std::vector<uint32_t>& params)
{
  return std::shared_ptr<Smt2Term>(
      new Smt2Term(kind, args, params, Smt2Term::LeafKind::NONE, ""));
}

Sort
Smt2Solver::get_sort(Term term, SortKind sort_kind) const
{
  /* Already computed sort for `term`.*/
  if (term->get_sort() != nullptr)
  {
    return term->get_sort();
  }

  assert(sort_kind != SORT_ANY);

  /* Compute sort for `term`. */
  Smt2Term* smt2_term                 = static_cast<Smt2Term*>(term.get());
  const std::vector<Term>& args       = smt2_term->get_args();
  const std::vector<uint32_t>& params = smt2_term->get_indices_uint32();
  const Op::Kind kind                 = smt2_term->get_kind();
  uint32_t bv_size                    = 0;
  uint32_t sig_size                   = 0;
  std::string sort;

  if (kind == Op::ITE)
  {
    assert(args.size() == 3);
    return args[2]->get_sort();
  }

  if (kind == Op::ARRAY_SELECT)
  {
    assert(args.size() == 2);
    assert(args[0]->get_sort()->get_kind() == SORT_ARRAY);
    assert(args[0]->get_sort()->get_sorts().size() == 2);
    return args[0]->get_sort()->get_sorts()[1];
  }

  if (kind == Op::UF_APPLY)
  {
    assert(args[0]->get_sort()->get_kind() == SORT_FUN);
    return args[0]->get_sort()->get_sorts().back();
  }

  if (kind == Op::SEQ_NTH)
  {
    assert(args.size() == 2);
    assert(args[0]->get_sort()->get_kind() == SORT_SEQ);
    assert(args[0]->get_sort()->get_sorts().size() == 1);
    return args[0]->get_sort()->get_sorts()[0];
  }

  switch (sort_kind)
  {
    case SORT_BOOL: sort = get_bool_sort_string(); break;

    case SORT_INT: sort = get_int_sort_string(); break;

    case SORT_REAL: sort = get_real_sort_string(); break;

    case SORT_RM: sort = get_rm_sort_string(); break;

    case SORT_STRING: sort = get_string_sort_string(); break;

    case SORT_REGLAN: sort = get_reglan_sort_string(); break;

    case SORT_ARRAY:
    {
      assert(args.size() >= 2);
      assert(args[0]->get_sort()->get_kind() == SORT_ARRAY);
      const std::vector<Sort>& sorts = args[0]->get_sort()->get_sorts();
      assert(sorts.size() == 2);
      sort = get_array_sort_string(sorts);
    }
    break;

    case SORT_FUN:
    {
      sort = get_fun_sort_string(term->get_sort()->get_sorts());
    }
    break;

    case SORT_BV:
      if (kind == Op::BV_CONCAT)
      {
        for (const Term& a : args)
        {
          assert(a->get_sort()->is_bv());
          bv_size += a->get_sort()->get_bv_size();
          sort = get_bv_sort_string(bv_size);
        }
      }
      else if (kind == Op::BV_EXTRACT)
      {
        assert(params.size() == 2);
        assert(params[0] >= params[1]);
        bv_size = params[0] - params[1] + 1;
        sort    = get_bv_sort_string(bv_size);
      }
      else if (kind == Op::BV_ZERO_EXTEND || kind == Op::BV_SIGN_EXTEND)
      {
        assert(args[0]->get_sort()->is_bv());
        bv_size = args[0]->get_sort()->get_bv_size() + params[0];
        sort    = get_bv_sort_string(bv_size);
      }
      else if (kind == Op::BV_REPEAT)
      {
        assert(args[0]->get_sort()->is_bv());
        bv_size = args[0]->get_sort()->get_bv_size() * params[0];
        sort    = get_bv_sort_string(bv_size);
      }
      else if (kind == Op::BV_COMP)
      {
        assert(args[0]->get_sort()->is_bv());
        bv_size = 1;
        sort    = get_bv_sort_string(bv_size);
      }
      else if (kind == Op::FP_TO_SBV || kind == Op::FP_TO_UBV)
      {
        assert(params.size() == 1);
        bv_size = params[0];
        sort    = get_bv_sort_string(bv_size);
      }
      else
      {
        assert(args[0]->get_sort()->is_bv());
        return args[0]->get_sort();
      }
      break;

    case SORT_FP:
      if (kind == Op::FP_TO_FP_FROM_BV || kind == Op::FP_TO_FP_FROM_SBV
          || kind == Op::FP_TO_FP_FROM_FP || kind == Op::FP_TO_FP_FROM_UBV
          || kind == Op::FP_TO_FP_FROM_REAL)
      {
        assert(params.size() == 2);
        bv_size  = params[0];
        sig_size = params[1];
        sort     = get_fp_sort_string(bv_size, sig_size);
      }
      else if (kind == Op::FP_FP)
      {
        assert(args.size() == 3);
        Term sign        = args[0];
        Term exp         = args[1];
        Term significand = args[2];
        assert(sign->get_sort()->is_bv());
        assert(exp->get_sort()->is_bv());
        assert(significand->get_sort()->is_bv());
        bv_size  = exp->get_sort()->get_bv_size();
        sig_size = sign->get_sort()->get_bv_size()
                   + significand->get_sort()->get_bv_size();
        sort = get_fp_sort_string(bv_size, sig_size);
      }
      else
      {
        assert(args.size() > 0);
        size_t idx = args.size() - 1;
        assert(args[idx]->get_sort()->is_fp());
        return args[idx]->get_sort();
      }
      break;

    case SORT_SEQ:
      assert(kind == Op::SEQ_UNIT);
      assert(args.size() >= 1);
      sort = get_seq_sort_string({args[0]->get_sort()});
      break;

    default: assert(false);
  }
  assert(!sort.empty());
  return std::shared_ptr<Smt2Sort>(new Smt2Sort(sort, bv_size, sig_size));
}

void
Smt2Solver::assert_formula(const Term& t)
{
  std::stringstream smt2;
  Smt2Term* smt2_term = static_cast<Smt2Term*>(t.get());
  smt2 << "(assert " << smt2_term->get_repr() << ")";
  dump_smt2(smt2.str());
}

Solver::Result
Smt2Solver::check_sat()
{
  dump_smt2("(check-sat)", ResponseKind::SMT2_SAT);
  return d_last_result;
}

Solver::Result
Smt2Solver::check_sat_assuming(std::vector<Term>& assumptions)
{
  std::stringstream smt2;
  smt2 << "(check-sat-assuming ( ";
  for (size_t i = 0, n = assumptions.size(); i < n; ++i)
  {
    Smt2Term* smt2_term = static_cast<Smt2Term*>(assumptions[i].get());
    if (i > 0) smt2 << " ";
    smt2 << smt2_term->get_repr();
  }
  smt2 << "))";
  dump_smt2(smt2.str(), ResponseKind::SMT2_SAT);
  return d_last_result;
}

std::vector<Term>
Smt2Solver::get_unsat_assumptions()
{
  dump_smt2("(get-unsat-assumptions)", ResponseKind::SMT2_SEXPR);
  return std::vector<Term>();
}

std::vector<Term>
Smt2Solver::get_unsat_core()
{
  dump_smt2("(get-unsat-core)", ResponseKind::SMT2_SEXPR);
  return std::vector<Term>();
}

void
Smt2Solver::push(uint32_t n_levels)
{
  std::stringstream smt2;
  smt2 << "(push " << n_levels << ")";
  dump_smt2(smt2.str());
}

void
Smt2Solver::pop(uint32_t n_levels)
{
  std::stringstream smt2;
  smt2 << "(pop " << n_levels << ")";
  dump_smt2(smt2.str());
}

void
Smt2Solver::print_model()
{
  dump_smt2("(get-model)", ResponseKind::SMT2_SEXPR);
}

void
Smt2Solver::reset()
{
  dump_smt2("(reset)");
}

void
Smt2Solver::reset_assertions()
{
  dump_smt2("(reset-assertions)");
}

void
Smt2Solver::set_opt(const std::string& opt, const std::string& value)
{
  // :incremental option is not in the SMT-LIB standard
  if (opt == get_option_name_incremental()) return;

  std::stringstream smt2;
  smt2 << "(set-option :" << opt << " " << value << ")";
  dump_smt2(smt2.str());
  if (opt == get_option_name_model_gen())
  {
    d_model_gen = value == "true" ? true : false;
  }
  if (opt == get_option_name_unsat_assumptions())
  {
    d_unsat_assumptions = value == "true" ? true : false;
  }
  if (opt == get_option_name_unsat_cores())
  {
    d_unsat_cores = value == "true" ? true : false;
  }
}

std::string
Smt2Solver::get_option_name_incremental() const
{
  return "incremental";
}

std::string
Smt2Solver::get_option_name_model_gen() const
{
  return "produce-models";
}

std::string
Smt2Solver::get_option_name_unsat_assumptions() const
{
  return "produce-unsat-assumptions";
}

std::string
Smt2Solver::get_option_name_unsat_cores() const
{
  return "produce-unsat-cores";
}

bool
Smt2Solver::option_incremental_enabled() const
{
  // SMT-LIB is by default incremental
  return true;
}

bool
Smt2Solver::option_model_gen_enabled() const
{
  return d_model_gen;
}

bool
Smt2Solver::option_unsat_assumptions_enabled() const
{
  return d_unsat_assumptions;
}

bool
Smt2Solver::option_unsat_cores_enabled() const
{
  return d_unsat_cores;
}

bool
Smt2Solver::is_unsat_assumption(const Term& t) const
{
  return true;
}

std::vector<Term>
Smt2Solver::get_value(std::vector<Term>& terms)
{
  std::stringstream smt2;
  smt2 << "(get-value (";
  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    Smt2Term* smt2_term = static_cast<Smt2Term*>(terms[i].get());
    if (i > 0) smt2 << " ";
    smt2 << smt2_term->get_repr();
  }
  smt2 << "))";
  dump_smt2(smt2.str(), ResponseKind::SMT2_SEXPR);
  return terms;
}

}  // namespace smt2
}  // namespace murxla
