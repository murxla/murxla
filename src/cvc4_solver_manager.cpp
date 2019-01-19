#include "cvc4_solver_manager.hpp"

#include <cassert>
#include <iostream>

#include "util.hpp"

using namespace CVC4::api;

namespace smtmbt {
namespace cvc4 {

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
// Sort Solver::getBooleanSort() const;
// Sort Solver::getIntegerSort() const;
// Sort Solver::getRealSort() const;
// Sort Solver::getRegExpSort() const;
// Sort Solver::getRoundingmodeSort() const;
// Sort Solver::getStringSort() const;
// Sort Solver::mkArraySort(Sort indexSort, Sort elemSort) const;
// Sort Solver::mkBitVectorSort(uint32_t size) const;
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

class CVC4ActionMkTerm : public CVC4Action
{
 public:
  CVC4ActionMkTerm(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTerm") {}

 protected:
};

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
    TheoryId theory_args = d_smgr->pick_theory();
    /* Nothing to do if no kind with term arguments of picked theory exists. */
    if (d_kinds.find(theory_args) == d_kinds.end()
        && d_kinds.find(THEORY_ALL) == d_kinds.end())
    {
      return true;
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

// Term Solver::mkTerm(Kind kind, Sort sort) const;
class CVC4ActionMkTerm0Sort : public CVC4Action
{
 public:
  CVC4ActionMkTerm0Sort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "mkTerm0Sort")
  {
    /* Note that this function is a special case since it does not expect term
     * arguments. We treat this as if the theory of the arguments is the same
     * as the theory of the created term.*/
    // TODO (no BV and BOOL kinds match this, thus empty for now)
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick theory of term argument(s). Note that this function is a special
     * case since it does not expect term arguments. We treat this as if the
     * theory of the arguments is the same as the theory of the created term. */
    TheoryId theory_args = d_smgr->pick_theory();
    /* Nothing to do if no kind with term arguments of picked theory exists. */
    if (d_kinds.find(theory_args) == d_kinds.end()
        && d_kinds.find(THEORY_ALL) == d_kinds.end())
    {
      return true;
    }
    Solver* cvc4 = d_smgr->get_solver();
    /* Pick kind that expects arguments of picked theory. (See note above.) */
    KindData& kd = d_smgr->pick_kind(d_kinds[theory_args]);
    d_smgr->add_term(cvc4->mkTerm(kd.d_kind, d_smgr->pick_sort(theory_args)),
                     kd.d_theory_term);
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
    auto all_kinds = d_smgr->get_all_kinds();

    d_kinds[THEORY_BOOL].push_back(Kind::NOT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_NOT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_NEG);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_REDAND);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_REDOR);
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick theory of term argument(s).*/
    TheoryId theory_args = d_smgr->pick_theory();
    /* Nothing to do if no kind with term arguments of picked theory exists. */
    if (d_kinds.find(theory_args) == d_kinds.end()
        && d_kinds.find(THEORY_ALL) == d_kinds.end())
    {
      return true;
    }
    Solver* cvc4 = d_smgr->get_solver();
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd = d_smgr->pick_kind(d_kinds[theory_args]);
    /* Pick child term. */
    Term child = d_smgr->pick_term(theory_args);
    /* Create term. */
    Term res = cvc4->mkTerm(kd.d_kind, child);
    std::cout << "res " << res << std::endl;
    d_smgr->add_term(res, kd.d_theory_term);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Mapping from TheoryId of the term arguments to this function to Kind and
   * TheoryId of the created term. */
  std::unordered_map<TheoryId, std::vector<Kind>> d_kinds;
};

// Term Solver::mkTerm(Kind kind, Term child1, Term child2) const;
class CVC4ActionMkTerm2 : public CVC4Action
{
 public:
  CVC4ActionMkTerm2(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTerm2")
  {
    d_kinds[THEORY_ALL].push_back(Kind::EQUAL);
    d_kinds[THEORY_ALL].push_back(Kind::DISTINCT);

    d_kinds[THEORY_BOOL].push_back(Kind::AND);
    d_kinds[THEORY_BOOL].push_back(Kind::OR);
    d_kinds[THEORY_BOOL].push_back(Kind::XOR);
    d_kinds[THEORY_BOOL].push_back(Kind::IMPLIES);

    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_CONCAT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_AND);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_OR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_XOR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_NAND);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_NOR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_XNOR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_COMP);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_MULT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_PLUS);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SUB);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UDIV);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UREM);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SDIV);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SREM);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SMOD);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UDIV_TOTAL);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UREM_TOTAL);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SHL);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_LSHR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_ASHR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_ULT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_ULE);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UGT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UGE);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SLT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SLE);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SGT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SGE);
    // d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_ULTBV);
    // d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SLTBV);
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick theory of term argument(s).*/
    TheoryId theory_args = d_smgr->pick_theory();
    /* Nothing to do if no kind with term arguments of picked theory exists. */
    if (d_kinds.find(theory_args) == d_kinds.end()
        && d_kinds.find(THEORY_ALL) == d_kinds.end())
    {
      return true;
    }
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd = d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);
    Solver* cvc4 = d_smgr->get_solver();
    /* Pick child terms. */
    Term child1 = d_smgr->pick_term(theory_args);
    Term child2;
    switch (kd.d_kind)
    {
      case Kind::BITVECTOR_CONCAT:
        child2 = d_smgr->pick_term(theory_args);
        break;
      default: child2 = d_smgr->pick_term(d_smgr->get_sort(child1));
    }
    /* Create term. */
    Term res = cvc4->mkTerm(kd.d_kind, child1, child2);
    std::cout << "res " << res << std::endl;
    d_smgr->add_term(res, kd.d_theory_term);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  std::unordered_map<TheoryId, std::vector<Kind>> d_kinds;
};

// Term Solver::mkTerm(Kind kind, Term child1, Term child2, Term child3) const;
class CVC4ActionMkTerm3 : public CVC4Action
{
 public:
  CVC4ActionMkTerm3(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTerm3")
  {
    d_kinds[THEORY_ALL].push_back(Kind::DISTINCT);
    d_kinds[THEORY_ALL].push_back(Kind::ITE);

    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_AND);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_OR);

    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_CONCAT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_AND);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_OR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_XOR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_MULT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_PLUS);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_ITE);
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    /* Pick theory of term argument(s).*/
    TheoryId theory_args = d_smgr->pick_theory();
    /* Nothing to do if no kind with term arguments of picked theory exists. */
    if (d_kinds.find(theory_args) == d_kinds.end()
        && d_kinds.find(THEORY_ALL) == d_kinds.end())
    {
      return true;
    }
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd = d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);
    Solver* cvc4 = d_smgr->get_solver();
    /* Pick child terms. */
    Term child1 = d_smgr->pick_term(theory_args);
    Term child2, child3;
    TheoryId theory_term =
        kd.d_theory_term == THEORY_ALL ? theory_args : kd.d_theory_term;

    switch (kd.d_kind)
    {
      case Kind::BITVECTOR_CONCAT:
        child2 = d_smgr->pick_term(theory_args);
        child3 = d_smgr->pick_term(theory_args);
        break;
      case Kind::ITE:
        child1 = d_smgr->pick_term(THEORY_BOOL);
        child2 = d_smgr->pick_term(theory_args);
        child3 = d_smgr->pick_term(d_smgr->get_sort(child2));
      default:
        auto sort = d_smgr->get_sort(child1);
        child2    = d_smgr->pick_term(sort);
        child3    = d_smgr->pick_term(sort);
    }
    /* Create term. */
    Term res = cvc4->mkTerm(kd.d_kind, child1, child2, child3);
    std::cout << "res " << res << std::endl;
    d_smgr->add_term(res, theory_term);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Mapping from TheoryId of the term arguments to this function to Kind and
   * TheoryId of the created term. */
  std::unordered_map<TheoryId, std::vector<Kind>> d_kinds;
};

#if 0
// Term Solver::mkTerm(Kind kind, const std::vector<Term>& children) const;
class CVC4ActionMkTermN : public CVC4Action
{
 public:
  CVC4ActionMkTermN(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTermN")
  {
    TODO, ARITY!
    d_kinds[THEORY_BOOL].push_back(Kind::EQUAL);
    d_kinds[THEORY_BOOL].push_back(Kind::DISTINCT);
    d_kinds[THEORY_BOOL].push_back(Kind::AND);
    d_kinds[THEORY_BOOL].push_back(Kind::IMPLIES);
    d_kinds[THEORY_BOOL].push_back(Kind::OR);
    d_kinds[THEORY_BOOL].push_back(Kind::XOR);
    d_kinds[THEORY_BOOL].push_back(Kind::IMPLIES);
    d_kinds[THEORY_BOOL].push_back(Kind::ITE);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_CONCAT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_AND);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_OR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_XOR);

    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_NAND);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_NOR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_XNOR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_COMP);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_MULT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_PLUS);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SUB);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UDIV);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UREM);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SDIV);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SREM);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SMOD);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UDIV_TOTAL);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UREM_TOTAL);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SHL);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_LSHR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_ASHR);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_ULT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_ULE);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UGT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_UGE);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SLT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SLE);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SGT);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SGE);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_ULTBV);
    d_kinds[THEORY_BV].push_back(Kind::BITVECTOR_SLTBV);
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    TODO
  }
  // void untrace(const char* s) override;

 private:
  /* Mapping from TheoryId of the term arguments to this function to Kind and
   * TheoryId of the created term. */
  std::unordered_map<KindData> d_kinds;
};
#endif

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
  d_sorts.clear();
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

#define SMTMBT_CVC4_ADD_KIND(kind, arity, theory_term, theory_arg) \
  d_all_kinds.emplace(kind, KindData(kind, arity, theory_term, theory_arg));

void
CVC4SolverManager::configure_kinds()
{
  SMTMBT_CVC4_ADD_KIND(Kind::DISTINCT, -1, THEORY_BOOL, THEORY_ALL);
  SMTMBT_CVC4_ADD_KIND(Kind::EQUAL, 2, THEORY_BOOL, THEORY_ALL);
  SMTMBT_CVC4_ADD_KIND(Kind::ITE, 3, THEORY_ALL, THEORY_ALL);

  SMTMBT_CVC4_ADD_KIND(Kind::AND, -1, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND(Kind::OR, -1, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND(Kind::NOT, 1, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND(Kind::XOR, 2, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND(Kind::IMPLIES, 2, THEORY_BOOL, THEORY_BOOL);

  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_CONCAT, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_AND, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_OR, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_XOR, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_MULT, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_PLUS, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_NOT, 1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_NEG, 1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_REDOR, 1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_REDAND, 1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_NAND, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_NOR, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_XNOR, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_COMP, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_SUB, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_UDIV, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_UREM, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_SDIV, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_SREM, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_SMOD, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_UDIV_TOTAL, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_UREM_TOTAL, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_SHL, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_LSHR, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_ASHR, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_ULT, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_ULE, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_UGT, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_UGE, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_SLT, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_SLE, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_SGT, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_SGE, 2, THEORY_BOOL, THEORY_BV);
  // SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_ULTBV, 2, THEORY_BV, THEORY_BV);
  // SMTMBT_CVC4_ADD_KIND(Kind::BITVECTOR_SLTBV, 2, THEORY_BV, THEORY_BV);
}

void
CVC4SolverManager::configure()
{
  configure_kinds();

  /* Actions ................................................................ */
  /* create/delete solver */
  auto anew      = new_action<CVC4ActionNew>();
  auto adelete   = new_action<CVC4ActionDelete>();
  /* make consts */
  auto amkfalse  = new_action<CVC4ActionMkFalse>();
  auto amktrue   = new_action<CVC4ActionMkTrue>();
  /* make terms */
  auto amkterm0 = new_action<CVC4ActionMkTerm0>();
  auto amkterm0sort = new_action<CVC4ActionMkTerm0Sort>();
  auto amkterm1 = new_action<CVC4ActionMkTerm1>();
  auto amkterm2 = new_action<CVC4ActionMkTerm2>();
  auto amkterm3     = new_action<CVC4ActionMkTerm3>();
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

  sinputs->add_action(amktrue, 10);
  sinputs->add_action(amkfalse, 10);
  sinputs->add_action(tinputs, 10, sterms);

  sterms->add_action(amkterm0, 10);
  sterms->add_action(amkterm0sort, 10);
  sterms->add_action(amkterm1, 10);
  sterms->add_action(amkterm2, 20);
  sterms->add_action(amkterm3, 20);
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
  std::advance(it, d_rng.next_uint32() % kinds.size());
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
  uint32_t n = d_rng.next_uint32() % (sz1 + sz2);
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
