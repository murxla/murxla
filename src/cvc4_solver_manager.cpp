#include "cvc4_solver_manager.hpp"

#include <cassert>
#include <iostream>

#include "util.hpp"

using namespace CVC4::api;

namespace smtmbt {
namespace cvc4 {

/* -------------------------------------------------------------------------- */

#define SMTMBT_CVC4_MKTERM_N_ARGS -1

#define SMTMBT_CVC4_BW_MIN 1
#define SMTMBT_CVC4_BW_MAX 128

/* -------------------------------------------------------------------------- */

class CVC4Action : public Action
{
 public:
  CVC4Action(CVC4SolverManagerBase* smgr, const std::string& id)
      : Action(smgr->get_rng(), id),
        d_smgr(static_cast<CVC4SolverManager*>(smgr))
  {
  }

 protected:
  CVC4SolverManager* d_smgr;
};

/* -------------------------------------------------------------------------- */

/* Transition-only actions (these actions are only used to make transitions
 * without executing any action). */

/**
 * Default transition action (no condition checked).
 *
 * State:      any state if applicable
 * Transition: unconditional
 */
class CVC4ActionNone : public CVC4Action
{
 public:
  CVC4ActionNone(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "") {}
  bool run() override { return true; }
};

/**
 * Transition from creating inputs to the next state.
 *
 * State:      create inputs
 * Transition: if there exists at least one input
 */
class CVC4ActionNoneCreateInputs : public CVC4Action
{
 public:
  CVC4ActionNoneCreateInputs(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "")
  {
  }
  bool run() override { return d_smgr->d_stats.inputs > 0; }
};

/* -------------------------------------------------------------------------- */

class CVC4ActionNew : public CVC4Action
{
 public:
  CVC4ActionNew(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "new") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Solver* cvc4 = d_smgr->get_solver();
    if (cvc4 != nullptr) delete (cvc4);
    d_smgr->set_solver(new Solver());
    return true;
  }
  // void untrace(const char* s) override;
};

class CVC4ActionDelete : public CVC4Action
{
 public:
  CVC4ActionDelete(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "delete") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Solver* cvc4 = d_smgr->get_solver();
    d_smgr->clear();
    assert(cvc4);
    delete cvc4;
    d_smgr->set_solver(nullptr);
    return true;
  }
  // void untrace(const char* s) override;
};

////// Result
// bool Result::isSat() const;
// bool Result::isUnsat() const;
// bool Result::isSatUnknown() const;
// bool Result::isValid() const;
// bool Result::isInvalid() const;
// bool Result::isValidUnknown() const;
// bool Result::operator==(const Result& r) const;
// bool Result::operator!=(const Result& r) const;
// std::string Result::getUnknownExplanation() const;
// std::string Result::toString() const;
// std::ostream& operator<<(std::ostream& out, const Result& r);

////// Sort
// bool Sort::operator==(const Sort& s) const;
// bool Sort::operator!=(const Sort& s) const;
// bool Sort::isNull() const;
// bool Sort::isBoolean() const;
// bool Sort::isInteger() const;
// bool Sort::isReal() const;
// bool Sort::isString() const;
// bool Sort::isRegExp() const;
// bool Sort::isRoundingMode() const;
// bool Sort::isBitVector() const;
// bool Sort::isFloatingPoint() const;
// bool Sort::isDatatype() const;
// bool Sort::isParametricDatatype() const;
// bool Sort::isFunction() const;
// bool Sort::isPredicate() const;
// bool Sort::isTuple() const;
// bool Sort::isRecord() const;
// bool Sort::isArray() const;
// bool Sort::isSet() const;
// bool Sort::isUninterpretedSort() const;
// bool Sort::isSortConstructor() const;
// bool Sort::isFirstClass() const;
// bool Sort::isFunctionLike() const;
// Datatype Sort::getDatatype() const;
// Sort Sort::instantiate(const std::vector<Sort>& params) const;
// void Sort::toStream(std::ostream& out) const;
// std::string Sort:: toString() const;

//// Function sort
// size_t Sort:: getFunctionArity() const;
// std::vector<Sort> Sort::getFunctionDomainSorts() const;
// Sort Sort::getFunctionCodomainSort() const;

//// Array sort
// Sort Sort::getArrayIndexSort() const;
// Sort Sort::getArrayElementSort() const;

// Set sort
// Sort Sort::getSetElementSort() const;

//// Uninterpreted sort
// std::string Sort::getUninterpretedSortName() const;
// bool Sort::isUninterpretedSortParameterized() const;
// std::vector<Sort> Sort::getUninterpretedSortParamSorts() const;

// Sort constructor sort
// std::string Sort::getSortConstructorName() const;
// size_t Sort::getSortConstructorArity() const;

//// Bit-vector sort
// uint32_t Sort::getBVSize() const;

//// Floating-point sort
// uint32_t Sort::getFPExponentSize() const;
// uint32_t Sort::getFPSignificandSize() const;

//// Datatype sort
// std::vector<Sort> Sort::getDatatypeParamSorts() const;
// size_t Sort::getDatatypeArity() const;

//// Tuple sort
// size_t Sort::getTupleLength() const;
// std::vector<Sort> Sort::getTupleSorts() const;
// std::ostream& operator<<(std::ostream& out, const Sort& s);

////// Term
// bool Term::operator==(const Term& t) const;
// bool Term::operator!=(const Term& t) const;
// Kind Term::getKind() const;
// Sort Term::getSort() const;
// bool Term::isNull() const;
// Term Term::notTerm() const;
// Term Term::andTerm(const Term& t) const;
// Term Term::orTerm(const Term& t) const;
// Term Term::xorTerm(const Term& t) const;
// Term Term::eqTerm(const Term& t) const;
// Term Term::impTerm(const Term& t) const;
// Term Term::iteTerm(const Term& then_t, const Term& else_t) const;
// std::string Term::toString() const;

//// Term::const_iterator
// const_iterator& Term::const_iterator::operator=(const const_iterator& it);
// bool Term::const_iterator::operator==(const const_iterator& it) const;
// bool Term::const_iterator::operator!=(const const_iterator& it) const;
// const_iterator& Term::const_iterator::operator++();
// const_iterator Term::const_iterator::operator++(int);
// Term Term::const_iterator::operator*() const;

// const_iterator Term::begin() const;
// const_iterator Term::end() const;

// std::ostream& operator<<(std::ostream& out, const Term& t);
// std::ostream& operator<<(std::ostream& out, const std::vector<Term>& vector);
// std::ostream& operator<<(std::ostream& out, const std::set<Term>& set) ;
// std::ostream& operator<<(std::ostream& out, const std::unordered_set<Term, TermHashFunction>& unordered_set);
// template <typename V> std::ostream& operator<<(std::ostream& out, const std::map<Term, V>& map);
// template <typename V> std::ostream& operator<<(std::ostream& out, const std::unordered_map<Term, V, TermHashFunction>& unordered_map);


//// OpTerm
// bool OpTerm::operator==(const OpTerm& t) const;
// bool OpTerm::operator!=(const OpTerm& t) const;
// Kind OpTerm::getKind() const;
// Sort OpTerm::getSort() const;
// bool OpTerm::isNull() const;
// std::string OpTerm::toString() const;
// std::ostream& OpTerm::operator<<(std::ostream& out, const OpTerm& t);

////// DatatypeSelectorDecl
// std::string DatatypeSelectorDecl::toString() const;

////// DatatypeConstructorDecl
// void DatatypeConstructorDecl::addSelector(const DatatypeSelectorDecl& stor);
// std::string DatatypeConstructorDecl::toString() const;

////// DatatypeDecl
// void DatatypeDecl::addConstructor(const DatatypeConstructorDecl& ctor);
// size_t DatatyepDecl::getNumConstructors() const;
// bool DatatypeDecl::isParametric() const;
// std::string DatatypeDecl::toString() const;

////// DatatypeSelector
// std::string DatatypeSelector::toString() const;

////// DatatypeConstructor
// bool DatatypeConstructor::isResolved() const;
// Term DatatypeConstructor::getConstructorTerm() const;
// DatatypeSelector DatatypeConstructor::operator[](const std::string& name) const;
// DatatypeSelector DatatypeConstructor::getSelector(const std::string& name) const;
// Term DatatypeConstructor::getSelectorTerm(const std::string& name) const;
// std::string DatatypeConstructor::toString() const;

////// DatatypeConstructor::const_iterator
// const_iterator& DatatypeConstructor::const_iterator::operator=(const const_iterator& it);
// bool DatatypeConstructor::const_iterator::operator==(const const_iterator& it) const;
// bool DatatypeConstructor::const_iterator::operator!=(const const_iterator& it) const;
// const_iterator& DatatypeConstructor::const_iterator::operator++();
// const_iterator DatatypeConstructor::const_iterator::operator++(int);
// const DatatypeSelector& DatatypeConstructor::const_iterator::operator*() const;
// const DatatypeSelector* DatatypeConstructor::const_iterator::operator->() const;
// const_iterator DatatypeConstructor::begin() const;
// const_iterator DatatypeConstructor::end() const;

////// Datatype
// DatatypeConstructor Datatype::operator[](size_t idx) const;
// DatatypeConstructor Datatype::operator[](const std::string& name) const;
// DatatypeConstructor Datatype::getConstructor(const std::string& name) const;
// Term Datatype::getConstructorTerm(const std::string& name) const;
// size_t Datatype::getNumConstructors() const;
// bool Datatype::isParametric() const;
// std::string Datatype::toString() const;

////// Datatype::const_iterator
//const_iterator& Datatype::const_iterator::operator=(const const_iterator& it);
// bool Datatype::const_iterator::operator==(const const_iterator& it) const;
// bool Datatype::const_iterator::operator!=(const const_iterator& it) const;
// const_iterator& Datatype::const_iterator::operator++();
// const_iterator Datatype::const_iterator::operator++(int);
// const DatatypeConstructor& Datatype::const_iterator::operator*() const;
// const DatatypeConstructor* Datatype::const_iterator::operator->() const;

// const_iterator Datatype::begin() const;
// const_iterator Datatype::end() const;
// std::ostream& operator<<(std::ostream& out, const DatatypeDecl& dtdecl);
// std::ostream& operator<<(std::ostream& out, const DatatypeConstructorDecl& ctordecl);
// std::ostream& operator<<(std::ostream& out, const DatatypeSelectorDecl& stordecl);
// std::ostream& operator<<(std::ostream& out, const Datatype& dtype);
// std::ostream& operator<<(std::ostream& out, const DatatypeConstructor& ctor);
// std::ostream& operator<<(std::ostream& out, const DatatypeSelector& stor);


////// Solver
// Solver& Solver::operator=(const Solver&) = delete;

// Sort Solver::getNullSort() const;
class CVC4ActionGetNullSort : public CVC4Action
{
 public:
  CVC4ActionGetNullSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "getNullSort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    (void) d_smgr->get_solver()->getNullSort();
    return true;
  }
  // void untrace(const char* s) override;
};

// Sort Solver::getBooleanSort() const;
class CVC4ActionGetBooleanSort : public CVC4Action
{
 public:
  CVC4ActionGetBooleanSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "getBooleanSort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    (void) d_smgr->get_solver()->getBooleanSort();
    return true;
  }
  // void untrace(const char* s) override;
};

// Sort Solver::getIntegerSort() const;
class CVC4ActionGetIntegerSort : public CVC4Action
{
 public:
  CVC4ActionGetIntegerSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "getIntegerSort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    (void) d_smgr->get_solver()->getIntegerSort();
    return true;
  }
  // void untrace(const char* s) override;
};

// Sort Solver::getRealSort() const;
class CVC4ActionGetRealSort : public CVC4Action
{
 public:
  CVC4ActionGetRealSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "getRealSort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    (void) d_smgr->get_solver()->getRealSort();
    return true;
  }
  // void untrace(const char* s) override;
};

// Sort Solver::getRegExpSort() const;
class CVC4ActionGetRegExpSort : public CVC4Action
{
 public:
  CVC4ActionGetRegExpSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "getRegExpSort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    (void) d_smgr->get_solver()->getRegExpSort();
    return true;
  }
  // void untrace(const char* s) override;
};

// Sort Solver::getRoundingmodeSort() const;
class CVC4ActionGetRoundingmodeSort : public CVC4Action
{
 public:
  CVC4ActionGetRoundingmodeSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "getRoundingmodeSort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    (void) d_smgr->get_solver()->getRoundingmodeSort();
    return true;
  }
  // void untrace(const char* s) override;
};

// Sort Solver::getStringSort() const;
class CVC4ActionGetStringSort : public CVC4Action
{
 public:
  CVC4ActionGetStringSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "getStringSort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    (void) d_smgr->get_solver()->getStringSort();
    return true;
  }
  // void untrace(const char* s) override;
};

// Sort Solver::mkArraySort(Sort indexSort, Sort elemSort) const;

// Sort Solver::mkBitVectorSort(uint32_t size) const;
class CVC4ActionMkBitVectorSort : public CVC4Action
{
 public:
  CVC4ActionMkBitVectorSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "mkBitVectorSort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    RNGenerator& rng = d_smgr->get_rng();
    uint32_t bw      = rng.pick_uint32(SMTMBT_CVC4_BW_MIN, SMTMBT_CVC4_BW_MAX);
    Sort res         = cvc4->mkBitVectorSort(bw);
    d_smgr->add_sort(res, THEORY_BV);
    return true;
  }
  // void untrace(const char* s) override;
};

// Sort Solver::mkFloatingPointSort(uint32_t exp, uint32_t sig) const;
// Sort Solver::mkDatatypeSort(DatatypeDecl dtypedecl) const;
// Sort Solver::mkFunctionSort(Sort domain, Sort codomain) const;
// Sort Solver::mkFunctionSort(const std::vector<Sort>& sorts, Sort codomain) const;
// Sort Solver::mkParamSort(const std::string& symbol) const;
// Sort Solver::mkPredicateSort(const std::vector<Sort>& sorts) const;
// Sort Solver::mkRecordSort(const std::vector<std::pair<std::string, Sort>>& fields) const;
// Sort Solver::mkSetSort(Sort elemSort) const;
// Sort Solver::mkUninterpretedSort(const std::string& symbol) const;
// Sort Solver::mkSortConstructorSort(const std::string& symbol, size_t arity) const;
// Sort Solver::mkTupleSort(const std::vector<Sort>& sorts) const;

// Term Solver::mkTerm(Kind kind) const;
class CVC4ActionMkTerm0 : public CVC4Action
{
 public:
  CVC4ActionMkTerm0(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTerm0")
  {
    /* Note that this function is a special case since it does not expect term
     * arguments. We treat this as if the theory of the arguments is the same
     * as the theory of the created term. */
    // TODO (no BV and BOOL kinds match this, thus empty for now)
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick theory of term argument(s). Note that this function is a special
     * case since it does not expect term arguments. We treat this as if the
     * theory of the arguments is the same as the theory of the created term. */
    TheoryId theory_args = d_smgr->pick_theory_with_terms();
    /* Nothing to do if no kind with term arguments of picked theory exists. */
    if (d_kinds.find(theory_args) == d_kinds.end()
        && d_kinds.find(THEORY_ALL) == d_kinds.end())
    {
      return false;
    }
    Solver* cvc4 = d_smgr->get_solver();
    /* Pick kind that expects arguments of picked theory. (See note above.) */
    KindData& kd = d_smgr->pick_kind(d_kinds[theory_args]);
    d_smgr->add_term(cvc4->mkTerm(kd.d_kind), kd.d_theory_term);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /**
   * Mapping from TheoryId of the term arguments to this function to Kind and
   * TheoryId of the created term.
   *
   * Note that this function is a special case since it does not expect term
   * arguments. We treat this as if the theory of the arguments is the same
   * as the theory of the created term.
   */
  std::unordered_map<TheoryId, std::vector<Kind>> d_kinds;
};

// Term Solver::mkTerm(Kind kind, Term child) const;
class CVC4ActionMkTerm1 : public CVC4Action
{
 public:
  CVC4ActionMkTerm1(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTerm1")
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if (k.second.d_arity == 1 && !k.second.d_parameterized)
        d_kinds[k.second.d_theory_args].push_back(k.first);
    }
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick theory of term argument(s).*/
    TheoryId theory_args = d_smgr->pick_theory_with_terms();
    /* Nothing to do if no kind with term arguments of picked theory exists. */
    if (d_kinds.find(theory_args) == d_kinds.end()
        && d_kinds.find(THEORY_ALL) == d_kinds.end())
    {
      return false;
    }
    Solver* cvc4 = d_smgr->get_solver();
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd = d_smgr->pick_kind(d_kinds[theory_args]);
    /* Pick child term. */
    Term child = d_smgr->pick_term(theory_args);
    /* Create term. */
    Term res = cvc4->mkTerm(kd.d_kind, child);
    std::cout << "res " << res << std::endl;
    d_smgr->add_term(
        res, kd.d_theory_term == THEORY_ALL ? theory_args : kd.d_theory_term);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Mapping from TheoryId of the term arguments to this function to Kinds
   * of the created term that expect arguments of this theory. */
  std::unordered_map<TheoryId, std::vector<Kind>> d_kinds;
};

// Term Solver::mkTerm(Kind kind, Term child1, Term child2) const;
class CVC4ActionMkTerm2 : public CVC4Action
{
 public:
  CVC4ActionMkTerm2(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTerm2")
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if ((k.second.d_arity == SMTMBT_CVC4_MKTERM_N_ARGS
           || k.second.d_arity == 2)
          && !k.second.d_parameterized)
        d_kinds[k.second.d_theory_args].push_back(k.first);
    }
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick theory of term argument(s).*/
    TheoryId theory_args = d_smgr->pick_theory_with_terms();
    /* Nothing to do if no kind with term arguments of picked theory exists. */
    if (d_kinds.find(theory_args) == d_kinds.end()
        && d_kinds.find(THEORY_ALL) == d_kinds.end())
    {
      return false;
    }
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd = d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);
    Solver* cvc4 = d_smgr->get_solver();
    /* Pick child terms. */
    Term child1 = d_smgr->pick_term(theory_args);
    Term child2;
    switch (kd.d_kind)
    {
      case BITVECTOR_CONCAT: child2 = d_smgr->pick_term(theory_args); break;
      default: child2 = d_smgr->pick_term(d_smgr->get_sort(child1));
    }
    /* Create term. */
    Term res = cvc4->mkTerm(kd.d_kind, child1, child2);
    std::cout << "res " << res << std::endl;
    d_smgr->add_term(
        res, kd.d_theory_term == THEORY_ALL ? theory_args : kd.d_theory_term);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Mapping from TheoryId of the term arguments to this function to Kinds
   * of the created term that expect arguments of this theory. */
  std::unordered_map<TheoryId, std::vector<Kind>> d_kinds;
};

// Term Solver::mkTerm(Kind kind, Term child1, Term child2, Term child3) const;
class CVC4ActionMkTerm3 : public CVC4Action
{
 public:
  CVC4ActionMkTerm3(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTerm3")
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if ((k.second.d_arity == SMTMBT_CVC4_MKTERM_N_ARGS
           || k.second.d_arity == 3)
          && !k.second.d_parameterized)
        d_kinds[k.second.d_theory_args].push_back(k.first);
    }
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick theory of term argument(s).*/
    TheoryId theory_args = d_smgr->pick_theory_with_terms();
    /* Nothing to do if no kind with term arguments of picked theory exists. */
    if (d_kinds.find(theory_args) == d_kinds.end()
        && d_kinds.find(THEORY_ALL) == d_kinds.end())
    {
      return false;
    }
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd = d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);
    Solver* cvc4 = d_smgr->get_solver();
    /* Pick child terms. */
    Term child1 = d_smgr->pick_term(theory_args);
    Term child2, child3;
    switch (kd.d_kind)
    {
      case BITVECTOR_CONCAT:
        child2 = d_smgr->pick_term(theory_args);
        child3 = d_smgr->pick_term(theory_args);
        break;
      case ITE:
        child1 = d_smgr->pick_term(THEORY_BOOL);
        child2 = d_smgr->pick_term(theory_args);
        child3 = d_smgr->pick_term(d_smgr->get_sort(child2));
        break;
      default:
        auto sort = d_smgr->get_sort(child1);
        child2    = d_smgr->pick_term(sort);
        child3    = d_smgr->pick_term(sort);
    }
    /* Create term. */
    Term res = cvc4->mkTerm(kd.d_kind, child1, child2, child3);
    std::cout << "res " << res << std::endl;
    d_smgr->add_term(
        res, kd.d_theory_term == THEORY_ALL ? theory_args : kd.d_theory_term);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Mapping from TheoryId of the term arguments to this function to Kinds
   * of the created term that expect arguments of this theory. */
  std::unordered_map<TheoryId, std::vector<Kind>> d_kinds;
};

// Term Solver::mkTerm(Kind kind, const std::vector<Term>& children) const;
class CVC4ActionMkTermN : public CVC4Action
{
 public:
  CVC4ActionMkTermN(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "mkTermN"), d_max_arity(11)
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if ((k.second.d_arity == SMTMBT_CVC4_MKTERM_N_ARGS
           || k.second.d_arity >= 1)
          && !k.second.d_parameterized)
        d_kinds[k.second.d_theory_args].push_back(k.first);
    }
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick theory of term argument(s).*/
    TheoryId theory_args = d_smgr->pick_theory_with_terms();
    /* Nothing to do if no kind with term arguments of picked theory exists. */
    if (d_kinds.find(theory_args) == d_kinds.end()
        && d_kinds.find(THEORY_ALL) == d_kinds.end())
    {
      return false;
    }
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd = d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);
    Solver* cvc4 = d_smgr->get_solver();
    /* Pick arity. */
    uint32_t arity = kd.d_arity;
    assert(arity != 0);
    if (arity == SMTMBT_CVC4_MKTERM_N_ARGS)
      arity = d_rng.pick_uint32(2, d_max_arity);
    /* Pick child terms. */
    std::vector<Term> children;
    for (size_t i = 0; i < arity; ++i)
    {
      switch (kd.d_kind)
      {
        case BITVECTOR_CONCAT:
          children.push_back(d_smgr->pick_term(theory_args));
          break;
        case ITE:
          if (children.empty())
            children.push_back(d_smgr->pick_term(THEORY_BOOL));
          else if (children.size() == 1)
            children.push_back(d_smgr->pick_term(theory_args));
          else
            children.push_back(
                d_smgr->pick_term(d_smgr->get_sort(children.back())));
          break;
        default:
          if (children.empty())
            children.push_back(d_smgr->pick_term(theory_args));
          else
            children.push_back(
                d_smgr->pick_term(d_smgr->get_sort(children.back())));
      }
    }
    /* Create term. */
    Term res = cvc4->mkTerm(kd.d_kind, children);
    std::cout << "res " << res << std::endl;
    d_smgr->add_term(
        res, kd.d_theory_term == THEORY_ALL ? theory_args : kd.d_theory_term);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Mapping from TheoryId of the term arguments to this function to Kinds
   * of the created term that expect arguments of this theory. */
  std::unordered_map<TheoryId, std::vector<Kind>> d_kinds;
  uint32_t d_max_arity;
};

// Term Solver::mkTerm(OpTerm opTerm, Term child) const;
// Term Solver::mkTerm(OpTerm opTerm, Term child1, Term child2) const;
// Term Solver::mkTerm(OpTerm opTerm, Term child1, Term child2, Term child3) const;
// Term Solver::mkTerm(OpTerm opTerm, const std::vector<Term>& children) const;
// Term Solver::mkTuple(const std::vector<Sort>& sorts, const std::vector<Term>& terms) const;
// OpTerm Solver::mkOpTerm(Kind kind, Kind k);
// OpTerm Solver::mkOpTerm(Kind kind, const std::string& arg);
// OpTerm Solver::mkOpTerm(Kind kind, uint32_t arg);
// OpTerm Solver::mkOpTerm(Kind kind, uint32_t arg1, uint32_t arg2);

// Term Solver::mkTrue() const;
class CVC4ActionMkTrue : public CVC4Action
{
 public:
  CVC4ActionMkTrue(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTrue") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Term res = d_smgr->get_solver()->mkTrue();
    d_smgr->add_input(res, THEORY_BOOL);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Solver::mkFalse() const;
class CVC4ActionMkFalse : public CVC4Action
{
 public:
  CVC4ActionMkFalse(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkFalse")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Term res = d_smgr->get_solver()->mkFalse();
    d_smgr->add_input(res, THEORY_BOOL);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Solver::mkBoolean(bool val) const;
// Term Solver::mkPi() const;
// Term Solver::mkReal(const char* s) const;
// Term Solver::mkReal(const std::string& s) const;
// Term Solver::mkReal(int32_t val) const;
// Term Solver::mkReal(int64_t val) const;
// Term Solver::mkReal(uint32_t val) const;
// Term Solver::mkReal(uint64_t val) const;
// Term Solver::mkReal(int32_t num, int32_t den) const;
// Term Solver::mkReal(int64_t num, int64_t den) const;
// Term Solver::mkReal(uint32_t num, uint32_t den) const;
// Term Solver::mkReal(uint64_t num, uint64_t den) const;
// Term Solver::mkRegexpEmpty() const;
// Term Solver::mkRegexpSigma() const;
// Term Solver::mkEmptySet(Sort s) const;
// Term Solver::mkSepNil(Sort sort) const;
// Term Solver::mkString(const char* s, bool useEscSequences = false) const;
// Term Solver::mkString(const std::string& s, bool useEscSequences = false) const;
// Term Solver::mkString(const unsigned char c) const;
// Term Solver::mkString(const std::vector<unsigned>& s) const;
// Term Solver::mkUniverseSet(Sort sort) const;
// Term Solver::mkBitVector(uint32_t size, uint64_t val = 0) const;
// Term Solver::mkBitVector(const char* s, uint32_t base = 2) const;
// Term Solver::mkBitVector(const std::string& s, uint32_t base = 2) const;
// Term Solver::mkBitVector(uint32_t size, const char* s, uint32_t base) const;
// Term Solver::mkBitVector(uint32_t size, std::string& s, uint32_t base) const;
// Term Solver::mkPosInf(uint32_t exp, uint32_t sig) const;
// Term Solver::mkNegInf(uint32_t exp, uint32_t sig) const;
// Term Solver::mkNaN(uint32_t exp, uint32_t sig) const;
// Term Solver::mkPosZero(uint32_t exp, uint32_t sig) const;
// Term Solver::mkNegZero(uint32_t exp, uint32_t sig) const;
// Term Solver::mkRoundingMode(RoundingMode rm) const;
// Term Solver::mkUninterpretedConst(Sort sort, int32_t index) const;
// Term Solver::mkAbstractValue(const std::string& index) const;
// Term Solver::mkAbstractValue(uint64_t index) const;
// Term Solver::mkFloatingPoint(uint32_t exp, uint32_t sig, Term val) const;
// Term Solver::mkVar(const std::string& symbol, Sort sort) const;
// Term Solver::mkVar(Sort sort) const;
// Term Solver::mkBoundVar(const std::string& symbol, Sort sort) const;
// Term Solver::mkBoundVar(Sort sort) const;
// Term Solver::simplify(const Term& t);
// void Solver::assertFormula(Term term) const;

// Result Solver::checkSat() const;
class CVC4ActionCheckSat : public CVC4Action
{
 public:
  CVC4ActionCheckSat(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "checkSat") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    // TODO query result
    (void)d_smgr->get_solver()->checkSat();
    return true;
  }
  // void untrace(const char* s) override;
};

// Result Solver::checkSatAssuming(Term assumption) const;
// Result Solver::checkSatAssuming(const std::vector<Term>& assumptions) const;
// Result Solver::checkValid() const;
// Result Solver::checkValidAssuming(Term assumption) const;
// Result Solver::checkValidAssuming(const std::vector<Term>& assumptions) const;
// Term Solver::declareConst(const std::string& symbol, Sort sort) const;
// Sort Solver::declareDatatype( const std::string& symbol, const std::vector<DatatypeConstructorDecl>& ctors) const;
// Term Solver::declareFun(const std::string& symbol, Sort sort) const;
// Term Solver::declareFun(const std::string& symbol, const std::vector<Sort>& sorts, Sort sort) const;
// Sort Solver::declareSort(const std::string& symbol, uint32_t arity) const;
// Term Solver::defineFun(const std::string& symbol, const std::vector<Term>& bound_vars, Sort sort, Term term) const;
// Term Solver::defineFun(Term fun, const std::vector<Term>& bound_vars, Term term) const;
// Term Solver::defineFunRec(const std::string& symbol, const std::vector<Term>& bound_vars, Sort sort, Term term) const;
// Term Solver::defineFunRec(Term fun, const std::vector<Term>& bound_vars, Term term) const;
// void Solver::defineFunsRec(const std::vector<Term>& funs, const std::vector<std::vector<Term>>& bound_vars, const std::vector<Term>& terms) const;
// void Solver::echo(std::ostream& out, const std::string& str) const;
// std::vector<Term> Solver::getAssertions() const;
// std::vector<std::pair<Term, Term>> Solver::getAssignment() const;
// std::string Solver::getInfo(const std::string& flag) const;
// std::string Solver::getOption(const std::string& option) const;
// std::vector<Term> Solver::getUnsatAssumptions() const;
// std::vector<Term> Solver::getUnsatCore() const;
// Term Solver::getValue(Term term) const;
// std::vector<Term> Solver::getValue(const std::vector<Term>& terms) const;
// void Solver::pop(uint32_t nscopes = 1) const;
// void Solver::printModel(std::ostream& out) const;
// void Solver::push(uint32_t nscopes = 1) const;
// void Solver::reset() const;
// void Solver::resetAssertions() const;
// void Solver::setInfo(const std::string& keyword, const std::string& value) const;
// void Solver::setLogic(const std::string& logic) const;
// void Solver::setOption(const std::string& option, const std::string& value) const;
// Term Solver::ensureTermSort(const Term& t, const Sort& s) const;

/* -------------------------------------------------------------------------- */

void
CVC4SolverManager::clear()
{
  d_terms.clear();
  d_sorts2theory.clear();
  d_theory2sorts.clear();
}

CVC4SolverManager::~CVC4SolverManager()
{
  clear();
  delete d_solver;
}

Sort
CVC4SolverManager::get_sort(Term term)
{
  return term.getSort();
}

void
CVC4SolverManager::ensure_sort(TheoryId theory)
{
  // TODO
}

#define SMTMBT_CVC4_ADD_KIND(                            \
    kind, arity, parameterized, theory_term, theory_arg) \
  d_all_kinds.emplace(                                   \
      kind, KindData(kind, arity, parameterized, theory_term, theory_arg));

void
CVC4SolverManager::configure_kinds()
{
  SMTMBT_CVC4_ADD_KIND(DISTINCT, -1, false, THEORY_BOOL, THEORY_ALL);
  SMTMBT_CVC4_ADD_KIND(EQUAL, 2, false, THEORY_BOOL, THEORY_ALL);
  SMTMBT_CVC4_ADD_KIND(ITE, 3, false, THEORY_ALL, THEORY_ALL);

  SMTMBT_CVC4_ADD_KIND(AND, -1, false, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND(OR, -1, false, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND(NOT, 1, false, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND(XOR, 2, false, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND(IMPLIES, 2, false, THEORY_BOOL, THEORY_BOOL);

  SMTMBT_CVC4_ADD_KIND(BITVECTOR_CONCAT, -1, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_AND, -1, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_OR, -1, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_XOR, -1, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_MULT, -1, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_PLUS, -1, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_NOT, 1, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_NEG, 1, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_REDOR, 1, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_REDAND, 1, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_NAND, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_NOR, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_XNOR, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_COMP, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_SUB, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_UDIV, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_UREM, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_SDIV, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_SREM, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_SMOD, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_UDIV_TOTAL, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_UREM_TOTAL, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_SHL, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_LSHR, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_ASHR, 2, false, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_ULT, 2, false, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_ULE, 2, false, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_UGT, 2, false, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_UGE, 2, false, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_SLT, 2, false, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_SLE, 2, false, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_SGT, 2, false, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(BITVECTOR_SGE, 2, false, THEORY_BOOL, THEORY_BV);
  // SMTMBT_CVC4_ADD_KIND(BITVECTOR_ULTBV, 2, false, THEORY_BV, THEORY_BV);
  // SMTMBT_CVC4_ADD_KIND(BITVECTOR_SLTBV, 2, false, THEORY_BV, THEORY_BV);
  std::cout << "all kinds " << get_all_kinds().size() << std::endl;
}

void
CVC4SolverManager::configure()
{
  configure_kinds();

  /* Actions ................................................................ */
  /* create/delete solver */
  auto anew    = new_action<CVC4ActionNew>();
  auto adelete = new_action<CVC4ActionDelete>();
  /* make consts */
  auto amkfalse = new_action<CVC4ActionMkFalse>();
  auto amktrue  = new_action<CVC4ActionMkTrue>();
  /* get sort */
  auto amgetboolsort   = new_action<CVC4ActionGetBooleanSort>();
  auto amgetintsort    = new_action<CVC4ActionGetIntegerSort>();
  auto amgetnullsort   = new_action<CVC4ActionGetNullSort>();
  auto amgetrealsort   = new_action<CVC4ActionGetRealSort>();
  auto amgetregexpsort = new_action<CVC4ActionGetRegExpSort>();
  auto amgetrmsort     = new_action<CVC4ActionGetRoundingmodeSort>();
  auto amgetstringsort = new_action<CVC4ActionGetStringSort>();
  /* make sort */
  auto amkbvsort = new_action<CVC4ActionMkBitVectorSort>();
  /* make terms */
  auto amkterm0 = new_action<CVC4ActionMkTerm0>();
  auto amkterm1 = new_action<CVC4ActionMkTerm1>();
  auto amkterm2 = new_action<CVC4ActionMkTerm2>();
  auto amkterm3 = new_action<CVC4ActionMkTerm3>();
  auto amktermn = new_action<CVC4ActionMkTermN>();
  /* commands */
  auto achecksat = new_action<CVC4ActionCheckSat>();
  /* transitions */
  auto tinputs = new_action<CVC4ActionNoneCreateInputs>();
  auto tnone   = new_action<CVC4ActionNone>();

  /* States ................................................................. */
  auto sdelete = d_fsm.new_state("delete");
  auto sinputs = d_fsm.new_state("create inputs");
  auto snew    = d_fsm.new_state("new");
  auto ssat    = d_fsm.new_state("sat");
  auto sterms  = d_fsm.new_state("create terms");
  auto sfinal  = d_fsm.new_state("final", true);

  /* Transitions ............................................................ */
  snew->add_action(anew, 10, sinputs);

  sinputs->add_action(amgetboolsort, 2);
  sinputs->add_action(amgetintsort, 2);
  sinputs->add_action(amgetnullsort, 2);
  sinputs->add_action(amgetrealsort, 2);
  sinputs->add_action(amgetregexpsort, 2);
  sinputs->add_action(amgetrmsort, 2);
  sinputs->add_action(amgetstringsort, 2);
  sinputs->add_action(amkbvsort, 20);
  sinputs->add_action(amktrue, 10);
  sinputs->add_action(amkfalse, 10);
  sinputs->add_action(tinputs, 10, sterms);

  sterms->add_action(amgetboolsort, 2);
  sterms->add_action(amgetintsort, 2);
  sterms->add_action(amgetnullsort, 2);
  sterms->add_action(amgetrealsort, 2);
  sterms->add_action(amgetregexpsort, 2);
  sterms->add_action(amgetrmsort, 2);
  sterms->add_action(amgetstringsort, 2);
  sterms->add_action(amkterm0, 10);
  sterms->add_action(amkterm1, 10);
  sterms->add_action(amkterm2, 20);
  sterms->add_action(amkterm3, 20);
  sterms->add_action(amktermn, 20);
  sterms->add_action(tnone, 5, ssat);

  ssat->add_action(achecksat, 10, sdelete);
  sdelete->add_action(adelete, 10, sfinal);

  /* Initial State .......................................................... */
  d_fsm.set_init_state(snew);
}

KindData&
CVC4SolverManager::pick_kind(std::vector<Kind>& kinds)
{
  assert(kinds.size());
  auto it = kinds.begin();
  std::advance(it, d_rng.pick_uint32() % kinds.size());
  Kind kind = *it;
  assert(d_all_kinds.find(kind) != d_all_kinds.end());
  return d_all_kinds[kind];
}

KindData&
CVC4SolverManager::pick_kind(std::vector<Kind>& kinds1,
                             std::vector<Kind>& kinds2)
{
  assert(kinds1.size() || kinds2.size());
  size_t sz1 = kinds1.size();
  size_t sz2 = kinds2.size();
  uint32_t n = d_rng.pick_uint32() % (sz1 + sz2);
  std::vector<Kind>::iterator it;
  if (sz2 == 0 || n < sz1)
  {
    it = kinds1.begin();
  }
  else
  {
    n -= sz1;
    it = kinds2.begin();
  }
  std::advance(it, n);
  Kind kind = *it;
  assert(d_all_kinds.find(kind) != d_all_kinds.end());
  return d_all_kinds[kind];
}

/* -------------------------------------------------------------------------- */

}  // namespace cvc4
}  // namespace smtmbt
