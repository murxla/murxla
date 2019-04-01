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
#define SMTMBT_CVC4_NTERMS_MIN 20

#define SMTMBT_CVC4_BV_REPEAT_N_MIN 1
#define SMTMBT_CVC4_BV_REPEAT_N_MAX 5
#define SMTMBT_CVC4_BV_EXTEND_N_MIN 0
#define SMTMBT_CVC4_BV_EXTEND_N_MAX 32
#define SMTMBT_CVC4_BV_ROTATE_N_MIN 0
#define SMTMBT_CVC4_BV_ROTATE_N_MAX 32

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
// TODO bool Result::isSat() const;
// TODO bool Result::isUnsat() const;
// TODO bool Result::isSatUnknown() const;
// TODO bool Result::isValid() const;
// TODO bool Result::isInvalid() const;
// TODO bool Result::isValidUnknown() const;
// TODO bool Result::operator==(const Result& r) const;
// TODO bool Result::operator!=(const Result& r) const;
// TODO std::string Result::getUnknownExplanation() const;
// TODO std::string Result::toString() const;
// TODO std::ostream& operator<<(std::ostream& out, const Result& r);

////// Sort
// TODO bool Sort::operator==(const Sort& s) const;
// TODO bool Sort::operator!=(const Sort& s) const;
// TODO bool Sort::isNull() const;
// TODO bool Sort::isBoolean() const;
// TODO bool Sort::isInteger() const;
// TODO bool Sort::isReal() const;
// TODO bool Sort::isString() const;
// TODO bool Sort::isRegExp() const;
// TODO bool Sort::isRoundingMode() const;
// TODO bool Sort::isBitVector() const;
// TODO bool Sort::isFloatingPoint() const;
// TODO bool Sort::isDatatype() const;
// TODO bool Sort::isParametricDatatype() const;
// TODO bool Sort::isFunction() const;
// TODO bool Sort::isPredicate() const;
// TODO bool Sort::isTuple() const;
// TODO bool Sort::isRecord() const;
// TODO bool Sort::isArray() const;
// TODO bool Sort::isSet() const;
// TODO bool Sort::isUninterpretedSort() const;
// TODO bool Sort::isSortConstructor() const;
// TODO bool Sort::isFirstClass() const;
// TODO bool Sort::isFunctionLike() const;
// TODO Datatype Sort::getDatatype() const;
// TODO Sort Sort::instantiate(const std::vector<Sort>& params) const;
// TODO void Sort::toStream(std::ostream& out) const;
// TODO std::string Sort:: toString() const;

//// Function sort
// TODO size_t Sort:: getFunctionArity() const;
// TODO std::vector<Sort> Sort::getFunctionDomainSorts() const;
// TODO Sort Sort::getFunctionCodomainSort() const;

//// Array sort
// TODO Sort Sort::getArrayIndexSort() const;
// TODO Sort Sort::getArrayElementSort() const;

// Set sort
// TODO Sort Sort::getSetElementSort() const;

//// Uninterpreted sort
// TODO std::string Sort::getUninterpretedSortName() const;
// TODO bool Sort::isUninterpretedSortParameterized() const;
// TODO std::vector<Sort> Sort::getUninterpretedSortParamSorts() const;

// Sort constructor sort
// TODO std::string Sort::getSortConstructorName() const;
// TODO size_t Sort::getSortConstructorArity() const;

//// Bit-vector sort
// TODO uint32_t Sort::getBVSize() const;

//// Floating-point sort
// TODO uint32_t Sort::getFPExponentSize() const;
// TODO uint32_t Sort::getFPSignificandSize() const;

//// Datatype sort
// TODO std::vector<Sort> Sort::getDatatypeParamSorts() const;
// TODO size_t Sort::getDatatypeArity() const;

//// Tuple sort
// TODO size_t Sort::getTupleLength() const;
// TODO std::vector<Sort> Sort::getTupleSorts() const;
// TODO std::ostream& operator<<(std::ostream& out, const Sort& s);

////// Term
// TODO bool Term::operator==(const Term& t) const;
// TODO bool Term::operator!=(const Term& t) const;
// TODO Kind Term::getKind() const;
// TODO Sort Term::getSort() const;
// TODO bool Term::isNull() const;
// TODO Term Term::notTerm() const;
// TODO Term Term::andTerm(const Term& t) const;
// TODO Term Term::orTerm(const Term& t) const;
// TODO Term Term::xorTerm(const Term& t) const;
// TODO Term Term::eqTerm(const Term& t) const;
// TODO Term Term::impTerm(const Term& t) const;
// TODO Term Term::iteTerm(const Term& then_t, const Term& else_t) const;
// TODO std::string Term::toString() const;

//// Term::const_iterator
// TODO const_iterator& Term::const_iterator::operator=(const const_iterator& it);
// TODO bool Term::const_iterator::operator==(const const_iterator& it) const;
// TODO bool Term::const_iterator::operator!=(const const_iterator& it) const;
// TODO const_iterator& Term::const_iterator::operator++();
// TODO const_iterator Term::const_iterator::operator++(int);
// TODO Term Term::const_iterator::operator*() const;

// TODO const_iterator Term::begin() const;
// TODO const_iterator Term::end() const;

// TODO std::ostream& operator<<(std::ostream& out, const Term& t);
// TODO std::ostream& operator<<(std::ostream& out, const std::vector<Term>& vector);
// TODO std::ostream& operator<<(std::ostream& out, const std::set<Term>& set) ;
// TODO std::ostream& operator<<(std::ostream& out, const std::unordered_set<Term, TermHashFunction>& unordered_set);
// TODO template <typename V> std::ostream& operator<<(std::ostream& out, const std::map<Term, V>& map);
// TODO template <typename V> std::ostream& operator<<(std::ostream& out, const std::unordered_map<Term, V, TermHashFunction>& unordered_map);


//// OpTerm
// TODO bool OpTerm::operator==(const OpTerm& t) const;
// TODO bool OpTerm::operator!=(const OpTerm& t) const;
// TODO Kind OpTerm::getKind() const;
// TODO Sort OpTerm::getSort() const;
// TODO bool OpTerm::isNull() const;
// TODO std::string OpTerm::toString() const;
// TODO std::ostream& OpTerm::operator<<(std::ostream& out, const OpTerm& t);

////// DatatypeSelectorDecl
// TODO std::string DatatypeSelectorDecl::toString() const;

////// DatatypeConstructorDecl
// TODO void DatatypeConstructorDecl::addSelector(const DatatypeSelectorDecl& stor);
// TODO std::string DatatypeConstructorDecl::toString() const;

////// DatatypeDecl
// TODO void DatatypeDecl::addConstructor(const DatatypeConstructorDecl& ctor);
// TODO size_t DatatyepDecl::getNumConstructors() const;
// TODO bool DatatypeDecl::isParametric() const;
// TODO std::string DatatypeDecl::toString() const;

////// DatatypeSelector
// TODO std::string DatatypeSelector::toString() const;

////// DatatypeConstructor
// TODO bool DatatypeConstructor::isResolved() const;
// TODO Term DatatypeConstructor::getConstructorTerm() const;
// TODO DatatypeSelector DatatypeConstructor::operator[](const std::string& name) const;
// TODO DatatypeSelector DatatypeConstructor::getSelector(const std::string& name) const;
// TODO Term DatatypeConstructor::getSelectorTerm(const std::string& name) const;
// TODO std::string DatatypeConstructor::toString() const;

////// DatatypeConstructor::const_iterator
// TODO const_iterator& DatatypeConstructor::const_iterator::operator=(const const_iterator& it);
// TODO bool DatatypeConstructor::const_iterator::operator==(const const_iterator& it) const;
// TODO bool DatatypeConstructor::const_iterator::operator!=(const const_iterator& it) const;
// TODO const_iterator& DatatypeConstructor::const_iterator::operator++();
// TODO const_iterator DatatypeConstructor::const_iterator::operator++(int);
// TODO const DatatypeSelector& DatatypeConstructor::const_iterator::operator*() const;
// TODO const DatatypeSelector* DatatypeConstructor::const_iterator::operator->() const;
// TODO const_iterator DatatypeConstructor::begin() const;
// TODO const_iterator DatatypeConstructor::end() const;

////// Datatype
// TODO DatatypeConstructor Datatype::operator[](size_t idx) const;
// TODO DatatypeConstructor Datatype::operator[](const std::string& name) const;
// TODO DatatypeConstructor Datatype::getConstructor(const std::string& name) const;
// TODO Term Datatype::getConstructorTerm(const std::string& name) const;
// TODO size_t Datatype::getNumConstructors() const;
// TODO bool Datatype::isParametric() const;
// TODO std::string Datatype::toString() const;

////// Datatype::const_iterator
// TODO const_iterator& Datatype::const_iterator::operator=(const const_iterator& it);
// TODO bool Datatype::const_iterator::operator==(const const_iterator& it) const;
// TODO bool Datatype::const_iterator::operator!=(const const_iterator& it) const;
// TODO const_iterator& Datatype::const_iterator::operator++();
// TODO const_iterator Datatype::const_iterator::operator++(int);
// TODO const DatatypeConstructor& Datatype::const_iterator::operator*() const;
// TODO const DatatypeConstructor* Datatype::const_iterator::operator->() const;

// TODO const_iterator Datatype::begin() const;
// TODO const_iterator Datatype::end() const;
// TODO std::ostream& operator<<(std::ostream& out, const DatatypeDecl& dtdecl);
// TODO std::ostream& operator<<(std::ostream& out, const DatatypeConstructorDecl& ctordecl);
// TODO std::ostream& operator<<(std::ostream& out, const DatatypeSelectorDecl& stordecl);
// TODO std::ostream& operator<<(std::ostream& out, const Datatype& dtype);
// TODO std::ostream& operator<<(std::ostream& out, const DatatypeConstructor& ctor);
// TODO std::ostream& operator<<(std::ostream& out, const DatatypeSelector& stor);


////// Solver

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
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    (void) cvc4->getNullSort();
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
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    (void) cvc4->getBooleanSort();
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
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    (void) cvc4->getIntegerSort();
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
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    (void) cvc4->getRealSort();
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
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    (void) cvc4->getRegExpSort();
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
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    (void) cvc4->getRoundingmodeSort();
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
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    (void) cvc4->getStringSort();
    return true;
  }
  // void untrace(const char* s) override;
};

// TODO Sort Solver::mkArraySort(Sort indexSort, Sort elemSort) const;

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

// TODO Sort Solver::mkFloatingPointSort(uint32_t exp, uint32_t sig) const;
// TODO Sort Solver::mkDatatypeSort(DatatypeDecl dtypedecl) const;
// TODO Sort Solver::mkFunctionSort(Sort domain, Sort codomain) const;
// TODO Sort Solver::mkFunctionSort(const std::vector<Sort>& sorts, Sort codomain) const;
// TODO Sort Solver::mkParamSort(const std::string& symbol) const;
// TODO Sort Solver::mkPredicateSort(const std::vector<Sort>& sorts) const;
// TODO Sort Solver::mkRecordSort(const std::vector<std::pair<std::string, Sort>>& fields) const;
// TODO Sort Solver::mkSetSort(Sort elemSort) const;
// TODO Sort Solver::mkUninterpretedSort(const std::string& symbol) const;
// TODO Sort Solver::mkSortConstructorSort(const std::string& symbol, size_t arity) const;
// TODO Sort Solver::mkTupleSort(const std::vector<Sort>& sorts) const;

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
    assert(d_kinds.find(theory_args) == d_kinds.end()
           || d_kinds[theory_args].size() > 0);
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    /* Pick kind that expects arguments of picked theory. (See note above.) */
    KindData& kd =
        d_kinds.find(THEORY_ALL) == d_kinds.end()
            ? d_smgr->pick_kind(d_kinds[theory_args])
            : d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);
    Term res = cvc4->mkTerm(kd.d_kind);
    d_smgr->add_term(
        res, kd.d_theory_term == THEORY_ALL ? theory_args : kd.d_theory_term);
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
  std::unordered_map<TheoryId, CVC4KindVector> d_kinds;
};

// Term Solver::mkTerm(Kind kind, Term child) const;
class CVC4ActionMkTerm1 : public CVC4Action
{
 public:
  CVC4ActionMkTerm1(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTerm1")
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if (k.second.d_arity == 1 && k.second.d_nparams == 0)
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
    assert(d_kinds.find(theory_args) == d_kinds.end()
           || d_kinds[theory_args].size() > 0);
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd =
        d_kinds.find(THEORY_ALL) == d_kinds.end()
            ? d_smgr->pick_kind(d_kinds[theory_args])
            : d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);
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
  std::unordered_map<TheoryId, CVC4KindVector> d_kinds;
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
          && k.second.d_nparams == 0)
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
    assert(d_kinds.find(theory_args) == d_kinds.end()
           || d_kinds[theory_args].size() > 0);
    assert(d_kinds.find(THEORY_ALL) == d_kinds.end()
           || d_kinds[THEORY_ALL].size() > 0);
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd =
        d_kinds.find(THEORY_ALL) == d_kinds.end()
            ? d_smgr->pick_kind(d_kinds[theory_args])
            : d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
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
  std::unordered_map<TheoryId, CVC4KindVector> d_kinds;
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
          && k.second.d_nparams == 0)
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
    assert(d_kinds.find(theory_args) == d_kinds.end()
           || d_kinds[theory_args].size() > 0);
    assert(d_kinds.find(THEORY_ALL) == d_kinds.end()
           || d_kinds[THEORY_ALL].size() > 0);
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd =
        d_kinds.find(THEORY_ALL) == d_kinds.end()
            ? d_smgr->pick_kind(d_kinds[theory_args])
            : d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
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
        if (!d_smgr->has_term(THEORY_BOOL)) return false;
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
  std::unordered_map<TheoryId, CVC4KindVector> d_kinds;
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
          && k.second.d_nparams == 0)
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
    assert(d_kinds.find(theory_args) == d_kinds.end()
           || d_kinds[theory_args].size() > 0);
    assert(d_kinds.find(THEORY_ALL) == d_kinds.end()
           || d_kinds[THEORY_ALL].size() > 0);
    /* Pick kind that expects arguments of picked theory. */
    KindData& kd =
        d_kinds.find(THEORY_ALL) == d_kinds.end()
            ? d_smgr->pick_kind(d_kinds[theory_args])
            : d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
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
          {
            if (!d_smgr->has_term(THEORY_BOOL)) return false;
            children.push_back(d_smgr->pick_term(THEORY_BOOL));
          }
          else if (children.size() == 1)
          {
            children.push_back(d_smgr->pick_term(theory_args));
          }
          else
          {
            children.push_back(
                d_smgr->pick_term(d_smgr->get_sort(children.back())));
          }
          break;
        default:
          if (children.empty())
          {
            children.push_back(d_smgr->pick_term(theory_args));
          }
          else
          {
            children.push_back(
                d_smgr->pick_term(d_smgr->get_sort(children.back())));
          }
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
  std::unordered_map<TheoryId, CVC4KindVector> d_kinds;
  uint32_t d_max_arity;
};

// Term Solver::mkTerm(Kind kind, OpTerm opTerm, Term child) const;
class CVC4ActionMkTermOp1 : public CVC4Action
{
 public:
  CVC4ActionMkTermOp1(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "mkTermOp1")
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if (k.second.d_arity == 1 && k.second.d_nparams > 0)
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
    assert(d_kinds.find(theory_args) == d_kinds.end()
           || d_kinds[theory_args].size() > 0);

    /* Pick kind that expects arguments of picked theory. */
    KindData& kd =
        d_kinds.find(THEORY_ALL) == d_kinds.end()
            ? d_smgr->pick_kind(d_kinds[theory_args])
            : d_smgr->pick_kind(d_kinds[theory_args], d_kinds[THEORY_ALL]);

    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);

    /* Pick child term. */
    Term child = d_smgr->pick_term(theory_args);
    /* Create operator term. */
    OpTerm opTerm = d_smgr->mkOpTerm(kd.d_kind, child);
    /* Create term. */
    Term res = cvc4->mkTerm(kd.d_kind, opTerm, child);
    std::cout << "res " << res << std::endl;
    d_smgr->add_term(
        res, kd.d_theory_term == THEORY_ALL ? theory_args : kd.d_theory_term);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Mapping from TheoryId of the term arguments to this function to Kinds
   * of the created term that expect arguments of this theory. */
  std::unordered_map<TheoryId, CVC4KindVector> d_kinds;
};

// TODO Term Solver::mkTerm(Kind kind, OpTerm opTerm, Term child1, Term child2) const;
// TODO Term Solver::mkTerm(Kind kind, OpTerm opTerm, Term child1, Term child2, Term child3) const;
// TODO Term Solver::mkTerm(Kind kind, OpTerm opTerm, const std::vector<Term>& children) const;
// TODO Term Solver::mkTuple(const std::vector<Sort>& sorts, const std::vector<Term>& terms) const;

// Term Solver::mkTrue() const;
class CVC4ActionMkTrue : public CVC4Action
{
 public:
  CVC4ActionMkTrue(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkTrue") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    Term res = cvc4->mkTrue();
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
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    Term res = cvc4->mkFalse();
    d_smgr->add_input(res, THEORY_BOOL);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Solver::mkBoolean(bool val) const;
class CVC4ActionMkBoolean : public CVC4Action
{
 public:
  CVC4ActionMkBoolean(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "mkBoolean")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    RNGenerator& rng = d_smgr->get_rng();
    Solver* cvc4     = d_smgr->get_solver();
    assert(cvc4);
    Term res = cvc4->mkBoolean(rng.pick_with_prob(500) ? true : false);
    d_smgr->add_input(res, THEORY_BOOL);
    return true;
  }
  // void untrace(const char* s) override;
};

// TODO Term Solver::mkPi() const;
// TODO Term Solver::mkReal(const char* s) const;
// TODO Term Solver::mkReal(const std::string& s) const;
// TODO Term Solver::mkReal(int32_t val) const;
// TODO Term Solver::mkReal(int64_t val) const;
// TODO Term Solver::mkReal(uint32_t val) const;
// TODO Term Solver::mkReal(uint64_t val) const;
// TODO Term Solver::mkReal(int32_t num, int32_t den) const;
// TODO Term Solver::mkReal(int64_t num, int64_t den) const;
// TODO Term Solver::mkReal(uint32_t num, uint32_t den) const;
// TODO Term Solver::mkReal(uint64_t num, uint64_t den) const;
// TODO Term Solver::mkRegexpEmpty() const;
// TODO Term Solver::mkRegexpSigma() const;
// TODO Term Solver::mkEmptySet(Sort s) const;
// TODO Term Solver::mkSepNil(Sort sort) const;
// TODO Term Solver::mkString(const char* s, bool useEscSequences = false) const;
// TODO Term Solver::mkString(const std::string& s, bool useEscSequences = false) const;
// TODO Term Solver::mkString(const unsigned char c) const;
// TODO Term Solver::mkString(const std::vector<unsigned>& s) const;
// TODO Term Solver::mkUniverseSet(Sort sort) const;

// Term Solver::mkBitVector(uint32_t size, uint64_t val = 0) const;
class CVC4ActionMkBitVector0 : public CVC4Action
{
 public:
  CVC4ActionMkBitVector0(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "mkBitVector0")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    RNGenerator& rng = d_smgr->get_rng();
    Solver* cvc4     = d_smgr->get_solver();
    assert(cvc4);
    uint32_t bw = rng.pick_uint32(SMTMBT_CVC4_BW_MIN, SMTMBT_CVC4_BW_MAX);
    Term res;
    if (rng.pick_with_prob(1))
    {
      res = cvc4->mkBitVector(bw);
    }
    else
    {
      uint64_t val = rng.pick_uint64();
      res          = cvc4->mkBitVector(bw, val);
    }
    d_smgr->add_input(res, THEORY_BV);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Solver::mkBitVector(const char* s, uint32_t base = 2) const;
class CVC4ActionMkBitVector1 : public CVC4Action
{
 public:
  CVC4ActionMkBitVector1(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "mkBitVector1")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    RNGenerator& rng = d_smgr->get_rng();
    Solver* cvc4     = d_smgr->get_solver();
    assert(cvc4);
    /* Functions RNGenerator::pick_XX_str allow max. size of 64 bit. */
    uint32_t bw = rng.pick_uint32(
        SMTMBT_CVC4_BW_MIN, SMTMBT_CVC4_BW_MAX > 64 ? 64 : SMTMBT_CVC4_BW_MAX);
    uint32_t r = rng.pick_uint32(0, 2);
    Term res;
    switch (r)
    {
      case 0:
      {
        std::string s = rng.pick_bin_str(bw);
        const char* c = s.c_str();
        res           = rng.pick_with_prob(500) ? cvc4->mkBitVector(c)
                                      : cvc4->mkBitVector(c, 2);
      }
      break;

      case 1:
      {
        std::string s = rng.pick_dec_str(bw);
        const char* c = s.c_str();
        res           = cvc4->mkBitVector(c, 10);
      }
      break;

      default:
      {
        assert(r == 2);
        std::string s = rng.pick_hex_str(bw);
        const char* c = s.c_str();
        res           = cvc4->mkBitVector(c, 16);
      }
    }
    d_smgr->add_input(res, THEORY_BV);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Solver::mkBitVector(const std::string& s, uint32_t base = 2) const;
class CVC4ActionMkBitVector2 : public CVC4Action
{
 public:
  CVC4ActionMkBitVector2(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "mkBitVector2")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    RNGenerator& rng = d_smgr->get_rng();
    Solver* cvc4     = d_smgr->get_solver();
    assert(cvc4);
    /* Functions RNGenerator::pick_XX_str allow max. size of 64 bit. */
    uint32_t bw = rng.pick_uint32(
        SMTMBT_CVC4_BW_MIN, SMTMBT_CVC4_BW_MAX > 64 ? 64 : SMTMBT_CVC4_BW_MAX);
    uint32_t r  = rng.pick_uint32(0, 2);
    Term res;
    switch (r)
    {
      case 0:
      {
        std::string s = rng.pick_bin_str(bw);
        res = rng.pick_with_prob(500) ? res = cvc4->mkBitVector(s)
                                      : cvc4->mkBitVector(s, 2);
      }
      break;

      case 1:
      {
        std::string s = rng.pick_dec_str(bw);
        res           = cvc4->mkBitVector(s, 10);
      }
      break;

      default:
      {
        assert(r == 2);
        std::string s = rng.pick_hex_str(bw);
        res           = cvc4->mkBitVector(s, 16);
      }
    }
    d_smgr->add_input(res, THEORY_BV);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Solver::mkBitVector(uint32_t size, const char* s, uint32_t base) const;
class CVC4ActionMkBitVector3 : public CVC4Action
{
 public:
  CVC4ActionMkBitVector3(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "mkBitVector3")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    RNGenerator& rng = d_smgr->get_rng();
    Solver* cvc4     = d_smgr->get_solver();
    assert(cvc4);
    /* Functions RNGenerator::pick_XX_str allow max. size of 64 bit. */
    uint32_t bw = rng.pick_uint32(
        SMTMBT_CVC4_BW_MIN, SMTMBT_CVC4_BW_MAX > 64 ? 64 : SMTMBT_CVC4_BW_MAX);
    uint32_t r = rng.pick_uint32(0, 2);
    Term res;
    switch (r)
    {
      case 0:
      {
        std::string s = rng.pick_bin_str(bw);
        const char* c = s.c_str();
        res           = cvc4->mkBitVector(bw, c, 2);
      }
      break;

      case 1:
      {
        std::string s = rng.pick_dec_str(bw);
        const char* c = s.c_str();
        res           = cvc4->mkBitVector(bw, c, 10);
      }
      break;

      default:
      {
        assert(r == 2);
        std::string s = rng.pick_hex_str(bw);
        const char* c = s.c_str();
        res           = cvc4->mkBitVector(bw, c, 16);
      }
    }
    d_smgr->add_input(res, THEORY_BV);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Solver::mkBitVector(uint32_t size, std::string& s, uint32_t base) const;
class CVC4ActionMkBitVector4 : public CVC4Action
{
 public:
  CVC4ActionMkBitVector4(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "mkBitVector4")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    RNGenerator& rng = d_smgr->get_rng();
    Solver* cvc4     = d_smgr->get_solver();
    assert(cvc4);
    /* Functions RNGenerator::pick_XX_str allow max. size of 64 bit. */
    uint32_t bw = rng.pick_uint32(
        SMTMBT_CVC4_BW_MIN, SMTMBT_CVC4_BW_MAX > 64 ? 64 : SMTMBT_CVC4_BW_MAX);
    uint32_t r = rng.pick_uint32(0, 2);
    Term res;
    switch (r)
    {
      case 0:
      {
        std::string s = rng.pick_bin_str(bw);
        res           = cvc4->mkBitVector(bw, s, 2);
      }
      break;

      case 1:
      {
        std::string s = rng.pick_dec_str(bw);
        res           = cvc4->mkBitVector(bw, s, 10);
      }
      break;

      default:
      {
        assert(r == 2);
        std::string s = rng.pick_hex_str(bw);
        res           = cvc4->mkBitVector(bw, s, 16);
      }
    }
    d_smgr->add_input(res, THEORY_BV);
    return true;
  }
  // void untrace(const char* s) override;
};

// TODO Term Solver::mkPosInf(uint32_t exp, uint32_t sig) const;
// TODO Term Solver::mkNegInf(uint32_t exp, uint32_t sig) const;
// TODO Term Solver::mkNaN(uint32_t exp, uint32_t sig) const;
// TODO Term Solver::mkPosZero(uint32_t exp, uint32_t sig) const;
// TODO Term Solver::mkNegZero(uint32_t exp, uint32_t sig) const;
// TODO Term Solver::mkRoundingMode(RoundingMode rm) const;
// TODO Term Solver::mkUninterpretedConst(Sort sort, int32_t index) const;
// TODO Term Solver::mkAbstractValue(const std::string& index) const;
// TODO Term Solver::mkAbstractValue(uint64_t index) const;
// TODO Term Solver::mkFloatingPoint(uint32_t exp, uint32_t sig, Term val) const;

// Term Solver::mkVar(const std::string& symbol, Sort sort) const;
class CVC4ActionMkVar : public CVC4Action
{
 public:
  CVC4ActionMkVar(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "mkVar") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    // TODO generate random symbol string
    if (!d_smgr->has_sort()) return false;
    TheoryId theory = d_smgr->pick_theory();
    Sort sort       = d_smgr->pick_sort(theory);
    Term res        = cvc4->mkVar(sort, "");
    d_smgr->add_input(res, theory);
    return true;
  }
  // void untrace(const char* s) override;
};

// TODO Term Solver::mkBoundVar(Sort sort, const std::string& symbol) const;

// Term Solver::simplify(const Term& t);
class CVC4ActionSimplify : public CVC4Action
{
 public:
  CVC4ActionSimplify(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "simplify")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    TheoryId theory = d_smgr->pick_theory_with_terms();
    Term term       = d_smgr->pick_term(theory);
    Term res        = cvc4->simplify(term);
    d_smgr->add_input(res, theory);
    return true;
  }
  // void untrace(const char* s) override;
};

// void Solver::assertFormula(Term term) const;
class CVC4ActionAssertFormula : public CVC4Action
{
 public:
  CVC4ActionAssertFormula(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "assertFormula")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term(THEORY_BOOL)) return false;
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    Term f = d_smgr->pick_term(THEORY_BOOL);
    cvc4->assertFormula(f);
    return true;
  }
  // void untrace(const char* s) override;
};

// Result Solver::checkSat() const;
class CVC4ActionCheckSat : public CVC4Action
{
 public:
  CVC4ActionCheckSat(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "checkSat") {}

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    // TODO query result
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    (void) cvc4->checkSat();
    return true;
  }
  // void untrace(const char* s) override;
};

// TODO Result Solver::checkSatAssuming(Term assumption) const;
// TODO Result Solver::checkSatAssuming(const std::vector<Term>& assumptions) const;

// Result Solver::checkValid() const;
class CVC4ActionCheckValid : public CVC4Action
{
 public:
  CVC4ActionCheckValid(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "checkValid")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    // TODO query result
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    (void) cvc4->checkValid();
    return true;
  }
  // void untrace(const char* s) override;
};

// TODO Result Solver::checkValidAssuming(Term assumption) const;
// TODO Result Solver::checkValidAssuming(const std::vector<Term>& assumptions) const;
// TODO Term Solver::declareConst(const std::string& symbol, Sort sort) const;
// TODO Sort Solver::declareDatatype( const std::string& symbol, const std::vector<DatatypeConstructorDecl>& ctors) const;
// TODO Term Solver::declareFun(const std::string& symbol, Sort sort) const;
// TODO Term Solver::declareFun(const std::string& symbol, const std::vector<Sort>& sorts, Sort sort) const;
// TODO Sort Solver::declareSort(const std::string& symbol, uint32_t arity) const;
// TODO Term Solver::defineFun(const std::string& symbol, const std::vector<Term>& bound_vars, Sort sort, Term term) const;
// TODO Term Solver::defineFun(Term fun, const std::vector<Term>& bound_vars, Term term) const;
// TODO Term Solver::defineFunRec(const std::string& symbol, const std::vector<Term>& bound_vars, Sort sort, Term term) const;
// TODO Term Solver::defineFunRec(Term fun, const std::vector<Term>& bound_vars, Term term) const;
// TODO void Solver::defineFunsRec(const std::vector<Term>& funs, const std::vector<std::vector<Term>>& bound_vars, const std::vector<Term>& terms) const;
// TODO void Solver::echo(std::ostream& out, const std::string& str) const;
// TODO std::vector<Term> Solver::getAssertions() const;
// TODO std::vector<std::pair<Term, Term>> Solver::getAssignment() const;
// TODO std::string Solver::getInfo(const std::string& flag) const;
// TODO std::string Solver::getOption(const std::string& option) const;
// TODO std::vector<Term> Solver::getUnsatAssumptions() const;
// TODO std::vector<Term> Solver::getUnsatCore() const;
// TODO Term Solver::getValue(Term term) const;
// TODO std::vector<Term> Solver::getValue(const std::vector<Term>& terms) const;
// TODO void Solver::pop(uint32_t nscopes = 1) const;
// TODO void Solver::printModel(std::ostream& out) const;
// TODO void Solver::push(uint32_t nscopes = 1) const;
// TODO void Solver::reset() const;
// TODO void Solver::resetAssertions() const;
// TODO void Solver::setInfo(const std::string& keyword, const std::string& value) const;
// TODO void Solver::setLogic(const std::string& logic) const;
// TODO void Solver::setOption(const std::string& option, const std::string& value) const;
// TODO Term Solver::ensureTermSort(const Term& t, const Sort& s) const;

/* -------------------------------------------------------------------------- */

KindData&
CVC4SolverManager::pick_kind(CVC4KindMap& map, CVC4KindVector& kinds)
{
  assert(kinds.size());
  auto it = kinds.begin();
  std::advance(it, d_rng.pick_uint32() % kinds.size());
  Kind kind = *it;
  assert(map.find(kind) != map.end());
  return map[kind];
}

KindData&
CVC4SolverManager::pick_kind(CVC4KindMap& map,
                             CVC4KindVector& kinds1,
                             CVC4KindVector& kinds2)
{
  assert(kinds1.size() || kinds2.size());
  size_t sz1 = kinds1.size();
  size_t sz2 = kinds2.size();
  uint32_t n = d_rng.pick_uint32() % (sz1 + sz2);
  CVC4KindVector::iterator it;
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
  assert(map.find(kind) != map.end());
  return map[kind];
}

KindData&
CVC4SolverManager::pick_kind(CVC4KindVector& kinds)
{
  return pick_kind(d_all_kinds, kinds);
}

KindData&
CVC4SolverManager::pick_kind(CVC4KindVector& kinds1, CVC4KindVector& kinds2)
{
  return pick_kind(d_all_kinds, kinds1, kinds2);
}

/* -------------------------------------------------------------------------- */

// TODO OpTerm Solver::mkOpTerm(Kind kind, Kind k);
// TODO OpTerm Solver::mkOpTerm(Kind kind, const std::string& arg);

// OpTerm Solver::mkOpTerm(Kind kind, uint32_t arg);
// OpTerm Solver::mkOpTerm(Kind kind, uint32_t arg1, uint32_t arg2);
OpTerm
CVC4SolverManager::mkOpTerm(Kind kind, Term term)
{
  assert(!term.isNull());

  uint32_t n0, n1, max;
  Solver* cvc4 = get_solver();
  assert(cvc4);
  RNGenerator& rng = get_rng();
  Sort sort        = term.getSort();
  OpTerm res;

  assert(d_all_kinds.find(kind) != d_all_kinds.end());
  assert(d_all_kinds[kind].d_op_kind != UNDEFINED_KIND);
  /* Pick parameter value. */
  switch (kind)
  {
    case BITVECTOR_REPEAT:
    {
      assert(sort.isBitVector());
      max = std::max<uint32_t>(1, SMTMBT_CVC4_BW_MAX / sort.getBVSize());
      n0  = rng.pick_uint32(1, max);
      res = cvc4->mkOpTerm(d_all_kinds[kind].d_op_kind, n0);
    }
    break;

    case BITVECTOR_ZERO_EXTEND:
    case BITVECTOR_SIGN_EXTEND:
      assert(sort.isBitVector());
      n0  = rng.pick_uint32(0, SMTMBT_CVC4_BW_MAX - sort.getBVSize());
      res = cvc4->mkOpTerm(d_all_kinds[kind].d_op_kind, n0);
      break;

    case BITVECTOR_ROTATE_LEFT:
    case BITVECTOR_ROTATE_RIGHT:
      assert(sort.isBitVector());
      n0  = rng.pick_uint32(0, sort.getBVSize());
      res = cvc4->mkOpTerm(d_all_kinds[kind].d_op_kind, n0);
      break;

    default:
      assert(kind == BITVECTOR_EXTRACT);
      n0  = rng.pick_uint32(0, sort.getBVSize() - 1);  // high
      n1  = rng.pick_uint32(0, n0);                    // low
      res = cvc4->mkOpTerm(d_all_kinds[kind].d_op_kind, n0, n1);
  }
  std::cout << "res " << res << std::endl;
  return res;
}

/* -------------------------------------------------------------------------- */

void
CVC4SolverManager::clear()
{
  d_terms.clear();
  d_sorts2theory.clear();
  d_theory2sorts.clear();
  d_all_kinds.clear();
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

#define SMTMBT_CVC4_ADD_KIND(                               \
    kind, op_kind, arity, nparams, theory_term, theory_arg) \
  d_all_kinds.emplace(                                      \
      kind, KindData(kind, op_kind, arity, nparams, theory_term, theory_arg));

#define SMTMBT_CVC4_ADD_KIND_NONPARAM(kind, arity, theory_term, theory_arg) \
  d_all_kinds.emplace(                                                      \
      kind,                                                                 \
      KindData(kind, UNDEFINED_KIND, arity, 0, theory_term, theory_arg));

#define SMTMBT_CVC4_ADD_KIND_PARAM(                         \
    kind, op_kind, arity, nparams, theory_term, theory_arg) \
  d_all_kinds.emplace(                                      \
      kind, KindData(kind, op_kind, arity, nparams, theory_term, theory_arg));

void
CVC4SolverManager::configure_kinds()
{
  /* Non-operator kinds ----------------------------------------------------- */

  SMTMBT_CVC4_ADD_KIND_NONPARAM(DISTINCT, -1, THEORY_BOOL, THEORY_ALL);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(EQUAL, 2, THEORY_BOOL, THEORY_ALL);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(ITE, 3, THEORY_ALL, THEORY_ALL);

  SMTMBT_CVC4_ADD_KIND_NONPARAM(AND, -1, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(OR, -1, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(NOT, 1, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(XOR, 2, THEORY_BOOL, THEORY_BOOL);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(IMPLIES, 2, THEORY_BOOL, THEORY_BOOL);

  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_CONCAT, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_AND, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_OR, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_XOR, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_MULT, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_PLUS, -1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_NOT, 1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_NEG, 1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_REDOR, 1, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_REDAND, 1, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_NAND, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_NOR, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_XNOR, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_COMP, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SUB, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_UDIV, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_UREM, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SDIV, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SREM, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SMOD, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_UDIV_TOTAL, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_UREM_TOTAL, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SHL, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_LSHR, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_ASHR, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_ULT, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_ULE, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_UGT, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_UGE, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SLT, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SLE, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SGT, 2, THEORY_BOOL, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SGE, 2, THEORY_BOOL, THEORY_BV);
  // SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_ULTBV, 2, THEORY_BV, THEORY_BV);
  // SMTMBT_CVC4_ADD_KIND_NONPARAM(BITVECTOR_SLTBV, 2, THEORY_BV, THEORY_BV);

  /* Non-operator parameterized kinds --------------------------------------- */

  SMTMBT_CVC4_ADD_KIND_PARAM(
      BITVECTOR_EXTRACT, BITVECTOR_EXTRACT_OP, 1, 2, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_PARAM(
      BITVECTOR_REPEAT, BITVECTOR_REPEAT_OP, 1, 1, THEORY_BV, THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_PARAM(BITVECTOR_ROTATE_LEFT,
                             BITVECTOR_ROTATE_LEFT_OP,
                             1,
                             1,
                             THEORY_BV,
                             THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_PARAM(BITVECTOR_ROTATE_RIGHT,
                             BITVECTOR_ROTATE_RIGHT_OP,
                             1,
                             1,
                             THEORY_BV,
                             THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_PARAM(BITVECTOR_SIGN_EXTEND,
                             BITVECTOR_SIGN_EXTEND_OP,
                             1,
                             1,
                             THEORY_BV,
                             THEORY_BV);
  SMTMBT_CVC4_ADD_KIND_PARAM(BITVECTOR_ZERO_EXTEND,
                             BITVECTOR_ZERO_EXTEND_OP,
                             1,
                             1,
                             THEORY_BV,
                             THEORY_BV);
  // INT_TO_BITVECTOR
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
  auto amkbool  = new_action<CVC4ActionMkBoolean>();
  auto amkbv0   = new_action<CVC4ActionMkBitVector0>();
  auto amkbv1   = new_action<CVC4ActionMkBitVector1>();
  auto amkbv2   = new_action<CVC4ActionMkBitVector2>();
  auto amkbv3   = new_action<CVC4ActionMkBitVector3>();
  auto amkbv4   = new_action<CVC4ActionMkBitVector4>();
  auto amkfalse = new_action<CVC4ActionMkFalse>();
  auto amktrue  = new_action<CVC4ActionMkTrue>();
  auto amkvar   = new_action<CVC4ActionMkVar>();
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
  auto amkterm0   = new_action<CVC4ActionMkTerm0>();
  auto amkterm1   = new_action<CVC4ActionMkTerm1>();
  auto amkterm2   = new_action<CVC4ActionMkTerm2>();
  auto amkterm3   = new_action<CVC4ActionMkTerm3>();
  auto amktermn   = new_action<CVC4ActionMkTermN>();
  auto amktermop1 = new_action<CVC4ActionMkTermOp1>();
  /* commands */
  auto aassert   = new_action<CVC4ActionAssertFormula>();
  auto asimp     = new_action<CVC4ActionSimplify>();
  auto achecksat = new_action<CVC4ActionCheckSat>();
  auto acheckval = new_action<CVC4ActionCheckValid>();
  /* transitions */
  auto tinputs = new_action<CVC4ActionNoneCreateInputs>();
  auto tnone   = new_action<CVC4ActionNone>();
  /* States ................................................................. */
  auto sassert = d_fsm.new_state(
      "assert", [this]() { return this->has_term(THEORY_BOOL); });
  auto sdelete = d_fsm.new_state("delete");
  auto sinputs = d_fsm.new_state("create inputs");
  auto snew    = d_fsm.new_state("new");
  auto ssat    = d_fsm.new_state("sat");
  auto sterms  = d_fsm.new_state("create terms");
  auto sfinal  = d_fsm.new_state("final", nullptr, true);

  /* Transitions ............................................................ */
  snew->add_action(anew, 10, sinputs);

  sinputs->add_action(amgetboolsort, 1);
  sinputs->add_action(amgetintsort, 1);
  sinputs->add_action(amgetnullsort, 1);
  sinputs->add_action(amgetrealsort, 1);
  sinputs->add_action(amgetregexpsort, 1);
  sinputs->add_action(amgetrmsort, 1);
  sinputs->add_action(amgetstringsort, 1);
  sinputs->add_action(amkbv0, 10);
  sinputs->add_action(amkbv1, 10);
  sinputs->add_action(amkbv2, 10);
  sinputs->add_action(amkbv3, 10);
  sinputs->add_action(amkbv4, 10);
  sinputs->add_action(amkbvsort, 2);
  sinputs->add_action(amktrue, 2);
  sinputs->add_action(amkfalse, 2);
  sinputs->add_action(amkbool, 2);
  sinputs->add_action(amkvar, 10);
  sinputs->add_action(tinputs, 10, sterms);
  sinputs->add_action(tinputs, 10, sassert);

  sassert->add_action(aassert, 2);
  sassert->add_action(aassert, 5, sinputs);
  sassert->add_action(aassert, 20, sterms);
  sassert->add_action(aassert, 2, ssat);

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
  sterms->add_action(amktermop1, 20);
  sterms->add_action(asimp, 2);
  sterms->add_action(tnone, 5, sassert);
  sterms->add_action(tnone, 2, ssat);

  ssat->add_action(achecksat, 10, sdelete);
  ssat->add_action(acheckval, 2, sdelete);
  sdelete->add_action(adelete, 10, sfinal);

  /* Initial State .......................................................... */
  d_fsm.set_init_state(snew);
}

/* -------------------------------------------------------------------------- */

}  // namespace cvc4
}  // namespace smtmbt
