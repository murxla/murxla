#include "cvc4_solver_manager.hpp"

#include <cassert>
#include <iostream>

#include "util.hpp"

using namespace CVC4::api;

namespace smtmbt {
namespace cvc4 {

#if 0

/* -------------------------------------------------------------------------- */

#define SMTMBT_CVC4_MKTERM_N_ARGS -1

#define SMTMBT_CVC4_BW_MIN 1
#define SMTMBT_CVC4_BW_MAX 128

#define SMTMBT_CVC4_NTERMS_MIN 20

#define SMTMBT_CVC4_NPUSH_MIN 1
#define SMTMBT_CVC4_NPUSH_MAX 5

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

////// Result
// TODO bool Result::is_sat() const;
// TODO bool Result::isUnsat() const;
// TODO bool Result::is_satUnknown() const;
// TODO bool Result::isValid() const;
// TODO bool Result::isInvalid() const;
// TODO bool Result::isValidUnknown() const;
// TODO bool Result::operator==(const Result& r) const;
// TODO bool Result::operator!=(const Result& r) const;
// TODO std::string Result::getUnknownExplanation() const;
// TODO std::string Result::toString() const;
// TODO std::ostream& operator<<(std::ostream& out, const Result& r);

////// Sort
// bool Sort::operator==(const Sort& s) const;
class CVC4ActionSortOpEq : public CVC4Action
{
 public:
  CVC4ActionSortOpEq(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "SortOpEq")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_sort()) return false;
    Sort s0 = d_smgr->pick_sort();
    assert(!s0.isNull());
    Sort s1 = d_smgr->pick_sort();
    assert(!s1.isNull());
    (void) (s0 == s1);
    return true;
  }
  // void untrace(const char* s) override;
};

// bool Sort::operator!=(const Sort& s) const;
class CVC4ActionSortOpNe : public CVC4Action
{
 public:
  CVC4ActionSortOpNe(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "SortOpNe")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_sort()) return false;
    Sort s0 = d_smgr->pick_sort();
    assert(!s0.isNull());
    Sort s1 = d_smgr->pick_sort();
    assert(!s1.isNull());
    (void) (s0 != s1);
    return true;
  }
  // void untrace(const char* s) override;
};

// bool Sort::isNull() const;
class CVC4ActionSortIsNull : public CVC4Action
{
 public:
  CVC4ActionSortIsNull(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "sortIsNull")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_sort()) return false;
    TheoryId theory = d_smgr->pick_theory_with_sorts();
    Sort sort       = d_smgr->pick_sort(theory);
    assert(sort.isNull() == (sort == Sort()));
    return true;
  }
  // void untrace(const char* s) override;
};

// bool Sort::isBoolean() const;
class CVC4ActionSortIsBoolean : public CVC4Action
{
 public:
  CVC4ActionSortIsBoolean(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "sortIsBoolean")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_sort()) return false;
    TheoryId theory = d_smgr->pick_theory_with_sorts();
    Sort sort       = d_smgr->pick_sort(theory);
    bool expected   = theory == THEORY_BOOL ? true : false;
    assert(sort.isBoolean() == expected);
    return true;
  }
  // void untrace(const char* s) override;
};

// TODO bool Sort::isInteger() const;
// TODO bool Sort::isReal() const;
// TODO bool Sort::isString() const;
// TODO bool Sort::isRegExp() const;
// TODO bool Sort::isRoundingMode() const;

// bool Sort::isBitVector() const;
class CVC4ActionSortIsBitVector : public CVC4Action
{
 public:
  CVC4ActionSortIsBitVector(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "sortIsBitVector")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_sort()) return false;
    TheoryId theory = d_smgr->pick_theory_with_sorts();
    Sort sort       = d_smgr->pick_sort(theory);
    bool expected   = theory == THEORY_BV ? true : false;
    assert(sort.isBitVector() == expected);
    return true;
  }
  // void untrace(const char* s) override;
};

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
// uint32_t Sort::getBVSize() const;
class CVC4ActionSortGetBVSize : public CVC4Action
{
 public:
  CVC4ActionSortGetBVSize(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "sortGetBVSize")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_sort(THEORY_BV)) return false;
    Sort sort = d_smgr->pick_sort(THEORY_BV);
    assert(sort.getBVSize() > 0);
    return true;
  }
  // void untrace(const char* s) override;
};

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
// bool Term::operator==(const Term& t) const;
class CVC4ActionTermOpEq : public CVC4Action
{
 public:
  CVC4ActionTermOpEq(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "TermOpEq")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term()) return false;
    Term t0 = d_smgr->pick_term();
    assert(!t0.isNull());
    Term t1 = d_smgr->pick_term();
    assert(!t1.isNull());
    (void) (t0 == t1);
    return true;
  }
  // void untrace(const char* s) override;
};

// bool Term::operator!=(const Term& t) const;
class CVC4ActionTermOpNe : public CVC4Action
{
 public:
  CVC4ActionTermOpNe(CVC4SolverManagerBase* smgr) : CVC4Action(smgr, "TermOpNe")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term()) return false;
    Term t0 = d_smgr->pick_term();
    assert(!t0.isNull());
    Term t1 = d_smgr->pick_term();
    assert(!t1.isNull());
    (void) (t0 != t1);
    return true;
  }
  // void untrace(const char* s) override;
};

// Kind Term::getKind() const;
class CVC4ActionTermGetKind : public CVC4Action
{
 public:
  CVC4ActionTermGetKind(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "TermGetKind")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term()) return false;
    Term term = d_smgr->pick_term();
    assert(!term.isNull());
    assert(term.getKind() != UNDEFINED_KIND);
    assert(term.getKind() != INTERNAL_KIND);
    return true;
  }
  // void untrace(const char* s) override;
};

// Sort Term::getSort() const;
class CVC4ActionTermGetSort : public CVC4Action
{
 public:
  CVC4ActionTermGetSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "TermGetSort")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term()) return false;
    Sort sort = d_smgr->pick_sort_with_terms();
    Term term = d_smgr->pick_term(sort);
    assert(!term.isNull());
    assert(term.getSort() == sort);
    return true;
  }
  // void untrace(const char* s) override;
};

// bool Term::isNull() const;
class CVC4ActionTermIsNull : public CVC4Action
{
 public:
  CVC4ActionTermIsNull(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "TermIsNull")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term()) return false;
    Term term = d_smgr->pick_term();
    assert(!term.isNull());
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Term::notTerm() const;
class CVC4ActionTermNotTerm : public CVC4Action
{
 public:
  CVC4ActionTermNotTerm(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "TermNotTerm")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term(THEORY_BOOL)) return false;
    Term res = d_smgr->pick_term(THEORY_BOOL).notTerm();
    assert(d_smgr->get_sort(res)
           == (static_cast<Solver*>(d_smgr->get_solver())->getBooleanSort()));
    assert(d_smgr->has_sort(d_smgr->get_sort(res)));
    d_smgr->add_term(res, THEORY_BOOL);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Term::andTerm(const Term& t) const;
class CVC4ActionTermAndTerm : public CVC4Action
{
 public:
  CVC4ActionTermAndTerm(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "TermAndTerm")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term(THEORY_BOOL)) return false;
    Term t   = d_smgr->pick_term(THEORY_BOOL);
    Term res = d_smgr->pick_term(THEORY_BOOL).andTerm(t);
    assert(d_smgr->get_sort(res)
           == (static_cast<Solver*>(d_smgr->get_solver())->getBooleanSort()));
    assert(d_smgr->has_sort(d_smgr->get_sort(res)));
    d_smgr->add_term(res, THEORY_BOOL);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Term::orTerm(const Term& t) const;
class CVC4ActionTermOrTerm : public CVC4Action
{
 public:
  CVC4ActionTermOrTerm(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "TermOrTerm")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term(THEORY_BOOL)) return false;
    Term t   = d_smgr->pick_term(THEORY_BOOL);
    Term res = d_smgr->pick_term(THEORY_BOOL).orTerm(t);
    assert(d_smgr->get_sort(res)
           == (static_cast<Solver*>(d_smgr->get_solver())->getBooleanSort()));
    assert(d_smgr->has_sort(d_smgr->get_sort(res)));
    d_smgr->add_term(res, THEORY_BOOL);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Term::xorTerm(const Term& t) const;
class CVC4ActionTermXorTerm : public CVC4Action
{
 public:
  CVC4ActionTermXorTerm(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "TermXorTerm")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term(THEORY_BOOL)) return false;
    Term t   = d_smgr->pick_term(THEORY_BOOL);
    Term res = d_smgr->pick_term(THEORY_BOOL).xorTerm(t);
    assert(d_smgr->get_sort(res)
           == (static_cast<Solver*>(d_smgr->get_solver())->getBooleanSort()));
    assert(d_smgr->has_sort(d_smgr->get_sort(res)));
    d_smgr->add_term(res, THEORY_BOOL);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Term::eqTerm(const Term& t) const;
class CVC4ActionTermEqTerm : public CVC4Action
{
 public:
  CVC4ActionTermEqTerm(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "TermEqTerm")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term(THEORY_BOOL)) return false;
    Term t   = d_smgr->pick_term(THEORY_BOOL);
    Term res = d_smgr->pick_term(THEORY_BOOL).eqTerm(t);
    assert(d_smgr->get_sort(res)
           == (static_cast<Solver*>(d_smgr->get_solver())->getBooleanSort()));
    assert(d_smgr->has_sort(d_smgr->get_sort(res)));
    d_smgr->add_term(res, THEORY_BOOL);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Term::impTerm(const Term& t) const;
class CVC4ActionTermImpTerm : public CVC4Action
{
 public:
  CVC4ActionTermImpTerm(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "TermImpTerm")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term(THEORY_BOOL)) return false;
    Term t   = d_smgr->pick_term(THEORY_BOOL);
    Term res = d_smgr->pick_term(THEORY_BOOL).impTerm(t);
    assert(d_smgr->get_sort(res)
           == (static_cast<Solver*>(d_smgr->get_solver())->getBooleanSort()));
    assert(d_smgr->has_sort(d_smgr->get_sort(res)));
    d_smgr->add_term(res, THEORY_BOOL);
    return true;
  }
  // void untrace(const char* s) override;
};

// Term Term::iteTerm(const Term& then_t, const Term& else_t) const;
class CVC4ActionTermIteTerm : public CVC4Action
{
 public:
  CVC4ActionTermIteTerm(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "TermIteTerm")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_term(THEORY_BOOL)) return false;
    Term tcond      = d_smgr->pick_term(THEORY_BOOL);
    TheoryId theory = d_smgr->pick_theory_with_terms();
    Term tthen      = d_smgr->pick_term(theory);
    Term telse      = d_smgr->pick_term(tthen);
    Term res        = tcond.iteTerm(tthen, telse);
    assert(d_smgr->has_sort(d_smgr->get_sort(res)));
    d_smgr->add_term(res, theory);
    return true;
  }
  // void untrace(const char* s) override;
};

// TODO std::string Term::toString() const;

//// Term::const_iterator
// TODO const_iterator& Term::const_iterator::operator=(const const_iterator&
// it);
// TODO bool Term::const_iterator::operator==(const const_iterator& it) const;
// TODO bool Term::const_iterator::operator!=(const const_iterator& it) const;
// TODO const_iterator& Term::const_iterator::operator++();
// TODO const_iterator Term::const_iterator::operator++(int);
// TODO Term Term::const_iterator::operator*() const;

// TODO const_iterator Term::begin() const;
// TODO const_iterator Term::end() const;

// TODO std::ostream& operator<<(std::ostream& out, const Term& t);
// TODO std::ostream& operator<<(std::ostream& out, const std::vector<Term>&
// vector);
// TODO std::ostream& operator<<(std::ostream& out, const std::set<Term>& set) ;
// TODO std::ostream& operator<<(std::ostream& out, const
// std::unordered_set<Term, TermHashFunction>& unordered_set);
// TODO template <typename V> std::ostream& operator<<(std::ostream& out, const
// std::map<Term, V>& map);
// TODO template <typename V> std::ostream& operator<<(std::ostream& out, const
// std::unordered_map<Term, V, TermHashFunction>& unordered_map);

//// OpTerm
// bool OpTerm::operator==(const OpTerm& t) const;
class CVC4ActionOpTermOpEq : public CVC4Action
{
 public:
  CVC4ActionOpTermOpEq(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "OpTermOpEq")
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if (k.second.d_nparams > 0) d_kinds.push_back(k.first);
    }
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_op_term()) return false;
    OpTerm t0 = d_smgr->pick_op_term();
    assert(!t0.isNull());
    OpTerm t1 = d_smgr->pick_op_term();
    assert(!t1.isNull());
    (void) (t0 == t1);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Vector of parameterized Kinds. */
  CVC4KindVector d_kinds;
};

// bool OpTerm::operator!=(const OpTerm& t) const;
class CVC4ActionOpTermOpNe : public CVC4Action
{
 public:
  CVC4ActionOpTermOpNe(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "OpTermOpNe")
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if (k.second.d_nparams > 0) d_kinds.push_back(k.first);
    }
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_op_term()) return false;
    OpTerm t0 = d_smgr->pick_op_term();
    assert(!t0.isNull());
    OpTerm t1 = d_smgr->pick_op_term();
    assert(!t1.isNull());
    (void) (t0 != t1);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Vector of parameterized Kinds. */
  CVC4KindVector d_kinds;
};

// Kind OpTerm::getKind() const;
class CVC4ActionOpTermGetKind : public CVC4Action
{
 public:
  CVC4ActionOpTermGetKind(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "OpTermGetKind")
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if (k.second.d_nparams > 0) d_kinds.push_back(k.first);
    }
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_op_term()) return false;
    OpTerm t = d_smgr->pick_op_term();
    assert(!t.isNull());
    assert(t.getKind() != UNDEFINED_KIND);
    assert(t.getKind() != INTERNAL_KIND);
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Vector of parameterized Kinds. */
  CVC4KindVector d_kinds;
};

// Sort OpTerm::getSort() const;
class CVC4ActionOpTermGetSort : public CVC4Action
{
 public:
  CVC4ActionOpTermGetSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "OpTermGetSort")
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if (k.second.d_nparams > 0) d_kinds.push_back(k.first);
    }
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_op_term()) return false;
    OpTerm t = d_smgr->pick_op_term();
    assert(!t.isNull());
    assert(!t.getSort().isNull());
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Vector of parameterized Kinds. */
  CVC4KindVector d_kinds;
};

// bool OpTerm::isNull() const;
class CVC4ActionOpTermIsNull : public CVC4Action
{
 public:
  CVC4ActionOpTermIsNull(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "OpTermIsNull")
  {
    for (const auto& k : d_smgr->get_all_kinds())
    {
      if (k.second.d_nparams > 0) d_kinds.push_back(k.first);
    }
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    if (!d_smgr->has_op_term()) return false;
    OpTerm t = d_smgr->pick_op_term();
    assert(!t.isNull());
    return true;
  }
  // void untrace(const char* s) override;

 private:
  /* Vector of parameterized Kinds. */
  CVC4KindVector d_kinds;
};

// TODO std::string OpTerm::toString() const;
// TODO std::ostream& OpTerm::operator<<(std::ostream& out, const OpTerm& t);

////// DatatypeSelectorDecl
// TODO std::string DatatypeSelectorDecl::toString() const;

////// DatatypeConstructorDecl
// TODO void DatatypeConstructorDecl::addSelector(const DatatypeSelectorDecl&
// stor);
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
// TODO DatatypeSelector DatatypeConstructor::operator[](const std::string&
// name) const;
// TODO DatatypeSelector DatatypeConstructor::getSelector(const std::string&
// name) const;
// TODO Term DatatypeConstructor::getSelectorTerm(const std::string& name)
// const;
// TODO std::string DatatypeConstructor::toString() const;

////// DatatypeConstructor::const_iterator
// TODO const_iterator& DatatypeConstructor::const_iterator::operator=(const
// const_iterator& it);
// TODO bool DatatypeConstructor::const_iterator::operator==(const
// const_iterator& it) const;
// TODO bool DatatypeConstructor::const_iterator::operator!=(const
// const_iterator& it) const;
// TODO const_iterator& DatatypeConstructor::const_iterator::operator++();
// TODO const_iterator DatatypeConstructor::const_iterator::operator++(int);
// TODO const DatatypeSelector& DatatypeConstructor::const_iterator::operator*()
// const;
// TODO const DatatypeSelector*
// DatatypeConstructor::const_iterator::operator->() const;
// TODO const_iterator DatatypeConstructor::begin() const;
// TODO const_iterator DatatypeConstructor::end() const;

////// Datatype
// TODO DatatypeConstructor Datatype::operator[](size_t idx) const;
// TODO DatatypeConstructor Datatype::operator[](const std::string& name) const;
// TODO DatatypeConstructor Datatype::getConstructor(const std::string& name)
// const;
// TODO Term Datatype::getConstructorTerm(const std::string& name) const;
// TODO size_t Datatype::getNumConstructors() const;
// TODO bool Datatype::isParametric() const;
// TODO std::string Datatype::toString() const;

////// Datatype::const_iterator
// TODO const_iterator& Datatype::const_iterator::operator=(const
// const_iterator& it);
// TODO bool Datatype::const_iterator::operator==(const const_iterator& it)
// const;
// TODO bool Datatype::const_iterator::operator!=(const const_iterator& it)
// const;
// TODO const_iterator& Datatype::const_iterator::operator++();
// TODO const_iterator Datatype::const_iterator::operator++(int);
// TODO const DatatypeConstructor& Datatype::const_iterator::operator*() const;
// TODO const DatatypeConstructor* Datatype::const_iterator::operator->() const;

// TODO const_iterator Datatype::begin() const;
// TODO const_iterator Datatype::end() const;
// TODO std::ostream& operator<<(std::ostream& out, const DatatypeDecl& dtdecl);
// TODO std::ostream& operator<<(std::ostream& out, const
// DatatypeConstructorDecl& ctordecl);
// TODO std::ostream& operator<<(std::ostream& out, const DatatypeSelectorDecl&
// stordecl);
// TODO std::ostream& operator<<(std::ostream& out, const Datatype& dtype);
// TODO std::ostream& operator<<(std::ostream& out, const DatatypeConstructor&
// ctor);
// TODO std::ostream& operator<<(std::ostream& out, const DatatypeSelector&
// stor);

////// Solver

// Sort Solver::getNullSort() const;
class CVC4ActionSolverGetNullSort : public CVC4Action
{
 public:
  CVC4ActionSolverGetNullSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverGetNullSort")
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

// Sort Solver::getIntegerSort() const;
class CVC4ActionSolverGetIntegerSort : public CVC4Action
{
 public:
  CVC4ActionSolverGetIntegerSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverGetIntegerSort")
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
class CVC4ActionSolverGetRealSort : public CVC4Action
{
 public:
  CVC4ActionSolverGetRealSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverGetRealSort")
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
class CVC4ActionSolverGetRegExpSort : public CVC4Action
{
 public:
  CVC4ActionSolverGetRegExpSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverGetRegExpSort")
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
class CVC4ActionSolverGetRoundingmodeSort : public CVC4Action
{
 public:
  CVC4ActionSolverGetRoundingmodeSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverGetRoundingmodeSort")
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
class CVC4ActionSolverGetStringSort : public CVC4Action
{
 public:
  CVC4ActionSolverGetStringSort(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverGetStringSort")
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

// TODO Term Solver::mkTuple(const std::vector<Sort>& sorts, const std::vector<Term>& terms) const;

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

// TODO Term Solver::mkVar(Sort sort, const std::string& symbol) const;

// Term Solver::simplify(const Term& t);
class CVC4ActionSolverSimplify : public CVC4Action
{
 public:
  CVC4ActionSolverSimplify(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverSimplify")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    Solver* cvc4 = d_smgr->get_solver();
    assert(cvc4);
    if (!d_smgr->has_term()) return false;
    TheoryId theory = d_smgr->pick_theory_with_terms();
    Term term       = d_smgr->pick_term(theory);
    Term res        = cvc4->simplify(term);
    d_smgr->add_input(res, theory);
    return true;
  }
  // void untrace(const char* s) override;
};

// void Solver::assertFormula(Term term) const;
class CVC4ActionSolverAssertFormula : public CVC4Action
{
 public:
  CVC4ActionSolverAssertFormula(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverAssertFormula")
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
class CVC4ActionSolverCheckSat : public CVC4Action
{
 public:
  CVC4ActionSolverCheckSat(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverCheckSat")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    // TODO query result
    Solver* cvc4 = d_smgr->get_solver();
    if (cvc4->getOption("incremental") == "false") return false;
    assert(cvc4);
    (void) cvc4->checkSat();
    return true;
  }
  // void untrace(const char* s) override;
};

// TODO Result Solver::checkSatAssuming(Term assumption) const;
// TODO Result Solver::checkSatAssuming(const std::vector<Term>& assumptions) const;

// Result Solver::checkValid() const;
class CVC4ActionSolverCheckValid : public CVC4Action
{
 public:
  CVC4ActionSolverCheckValid(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverCheckValid")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    // TODO query result
    Solver* cvc4 = d_smgr->get_solver();
    if (cvc4->getOption("incremental") == "false") return false;
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

// void Solver::push(uint32_t nscopes = 1) const;
class CVC4ActionSolverPush : public CVC4Action
{
 public:
  CVC4ActionSolverPush(CVC4SolverManagerBase* smgr)
      : CVC4Action(smgr, "solverPush")
  {
  }

  bool run() override
  {
    SMTMBT_TRACE << get_id();
    RNGenerator& rng = d_smgr->get_rng();
    Solver* cvc4     = d_smgr->get_solver();
    if (cvc4->getOption("incremental") == "false") return false;
    assert(cvc4);
    uint32_t n = rng.pick_uint32(SMTMBT_CVC4_NPUSH_MIN, SMTMBT_CVC4_NPUSH_MAX);
    cvc4->push(n);
    d_smgr->push_nscopes(n);
    return true;
  }
  // void untrace(const char* s) override;
};

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

OpTerm&
CVC4SolverManager::pick_op_term()
{
  assert(d_op_terms.size());
  auto it = d_op_terms.begin();
  std::advance(it, d_rng.pick_uint32() % d_op_terms.size());
  return *it;
}

/* -------------------------------------------------------------------------- */

// TODO OpTerm Solver::mkOpTerm(Kind kind, Kind k);
// TODO OpTerm Solver::mkOpTerm(Kind kind, const std::string& arg);

/* -------------------------------------------------------------------------- */

void
CVC4SolverManager::clear()
{
  d_terms.clear();
  d_op_terms.clear();
  d_sorts_to_theory.clear();
  d_theory_to_sorts.clear();
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

  /* --------------------------------------------------------------------- */
  /* Actions                                                               */
  /* --------------------------------------------------------------------- */

  /* Sort Actions ........................................................ */
  auto a_sort_isbool    = new_action<CVC4ActionSortIsBoolean>();
  auto a_sort_isbv      = new_action<CVC4ActionSortIsBitVector>();
  auto a_sort_isnull    = new_action<CVC4ActionSortIsNull>();
  auto a_sort_getbvsize = new_action<CVC4ActionSortGetBVSize>();
  auto a_sort_opeq      = new_action<CVC4ActionSortOpEq>();
  auto a_sort_opne      = new_action<CVC4ActionSortOpNe>();

  /* Term Actions ....................................................... */
  auto a_term_andterm = new_action<CVC4ActionTermAndTerm>();
  auto a_term_eqterm  = new_action<CVC4ActionTermEqTerm>();
  auto a_term_getkind = new_action<CVC4ActionTermGetKind>();
  auto a_term_getsort = new_action<CVC4ActionTermGetSort>();
  auto a_term_impterm = new_action<CVC4ActionTermImpTerm>();
  auto a_term_isnull  = new_action<CVC4ActionTermIsNull>();
  auto a_term_iteterm = new_action<CVC4ActionTermIteTerm>();
  auto a_term_notterm = new_action<CVC4ActionTermNotTerm>();
  auto a_term_opeq    = new_action<CVC4ActionTermOpEq>();
  auto a_term_opne    = new_action<CVC4ActionTermOpNe>();
  auto a_term_orterm  = new_action<CVC4ActionTermOrTerm>();
  auto a_term_xorterm = new_action<CVC4ActionTermXorTerm>();

  /* OpTerm Actions ...................................................... */
  auto a_opterm_getkind = new_action<CVC4ActionOpTermGetKind>();
  auto a_opterm_getsort = new_action<CVC4ActionOpTermGetSort>();
  auto a_opterm_isnull  = new_action<CVC4ActionOpTermIsNull>();
  auto a_opterm_opeq    = new_action<CVC4ActionOpTermOpEq>();
  auto a_opterm_opne    = new_action<CVC4ActionOpTermOpNe>();

  /* Solver Actions ...................................................... */
  /* create/delete solver */
  auto a_solver_new    = new_action<CVC4ActionSolverNew>();
  auto a_solver_delete = new_action<CVC4ActionSolverDelete>();
  /* make consts */
  auto a_solver_mkbool  = new_action<CVC4ActionSolverMkBoolean>();
  auto a_solver_mkbv0   = new_action<CVC4ActionSolverMkBitVector0>();
  auto a_solver_mkbv1   = new_action<CVC4ActionSolverMkBitVector1>();
  auto a_solver_mkbv2   = new_action<CVC4ActionSolverMkBitVector2>();
  auto a_solver_mkbv3   = new_action<CVC4ActionSolverMkBitVector3>();
  auto a_solver_mkbv4   = new_action<CVC4ActionSolverMkBitVector4>();
  auto a_solver_mkfalse = new_action<CVC4ActionSolverMkFalse>();
  auto a_solver_mktrue  = new_action<CVC4ActionSolverMkTrue>();
  auto a_solver_mkConst   = new_action<CVC4ActionSolverMkConst>();
  /* get sort */
  auto a_solver_getboolsort   = new_action<CVC4ActionSolverGetBooleanSort>();
  auto a_solver_getintsort    = new_action<CVC4ActionSolverGetIntegerSort>();
  auto a_solver_getnullsort   = new_action<CVC4ActionSolverGetNullSort>();
  auto a_solver_getrealsort   = new_action<CVC4ActionSolverGetRealSort>();
  auto a_solver_getregexpsort = new_action<CVC4ActionSolverGetRegExpSort>();
  auto a_solver_getrmsort = new_action<CVC4ActionSolverGetRoundingmodeSort>();
  auto a_solver_getstringsort = new_action<CVC4ActionSolverGetStringSort>();
  /* make sort */
  auto a_solver_mkbvsort = new_action<CVC4ActionSolverMkBitVectorSort>();
  /* make terms */
  auto a_solver_mkterm0   = new_action<CVC4ActionSolverMkTerm0>();
  auto a_solver_mkterm1   = new_action<CVC4ActionSolverMkTerm1>();
  auto a_solver_mkterm2   = new_action<CVC4ActionSolverMkTerm2>();
  auto a_solver_mkterm3   = new_action<CVC4ActionSolverMkTerm3>();
  auto a_solver_mktermn   = new_action<CVC4ActionSolverMkTermN>();
  auto a_solver_mktermop1 = new_action<CVC4ActionSolverMkTermOp1>();
  /* commands */
  auto a_solver_assert   = new_action<CVC4ActionSolverAssertFormula>();
  auto a_solver_checksat = new_action<CVC4ActionSolverCheckSat>();
  auto a_solver_checkval = new_action<CVC4ActionSolverCheckValid>();
  auto a_solver_push     = new_action<CVC4ActionSolverPush>();
  auto a_solver_simp     = new_action<CVC4ActionSolverSimplify>();
  /* transitions */
  auto t_inputs = new_action<CVC4ActionNoneCreateInputs>();
  auto t_none   = new_action<CVC4ActionNone>();

  /* --------------------------------------------------------------------- */
  /* States                                                                */
  /* --------------------------------------------------------------------- */

  auto s_assert = d_fsm.new_state(
      "assert", [this]() { return this->has_term(THEORY_BOOL); });
  auto s_delete = d_fsm.new_state("delete");
  auto s_inputs = d_fsm.new_state("create inputs");
  auto s_new    = d_fsm.new_state("new");
  // auto s_pushpop =
  //    d_fsm.new_state("pushpop", [this]() { return this->d_incremental; });
  auto s_pushpop = d_fsm.new_state("pushpop");
  auto s_sat     = d_fsm.new_state("sat");
  auto s_terms   = d_fsm.new_state("create terms");
  auto s_final   = d_fsm.new_state("final", nullptr, true);

  /* --------------------------------------------------------------------- */
  /* Transitions                                                           */
  /* --------------------------------------------------------------------- */

  /* State: new .......................................................... */
  s_new->add_action(a_solver_new, 10, s_inputs);

  /* State: create inputs ................................................ */
  /* sort actions */
  s_inputs->add_action(a_sort_isbool, 1);
  s_inputs->add_action(a_sort_isbv, 1);
  s_inputs->add_action(a_sort_isnull, 1);
  s_inputs->add_action(a_sort_getbvsize, 1);
  s_inputs->add_action(a_sort_opeq, 1);
  s_inputs->add_action(a_sort_opne, 1);
  /* term actions */
  s_inputs->add_action(a_term_getkind, 1);
  s_inputs->add_action(a_term_getsort, 1);
  s_inputs->add_action(a_term_isnull, 1);
  s_inputs->add_action(a_term_opeq, 1);
  s_inputs->add_action(a_term_opne, 1);
  /* opterm actions */
  s_inputs->add_action(a_opterm_getkind, 1);
  s_inputs->add_action(a_opterm_getsort, 1);
  s_inputs->add_action(a_opterm_isnull, 1);
  s_inputs->add_action(a_opterm_opeq, 1);
  s_inputs->add_action(a_opterm_opne, 1);
  /* solver actions */
  s_inputs->add_action(a_solver_getboolsort, 1);
  s_inputs->add_action(a_solver_getintsort, 1);
  s_inputs->add_action(a_solver_getnullsort, 1);
  s_inputs->add_action(a_solver_getrealsort, 1);
  s_inputs->add_action(a_solver_getregexpsort, 1);
  s_inputs->add_action(a_solver_getrmsort, 1);
  s_inputs->add_action(a_solver_getstringsort, 1);
  s_inputs->add_action(a_solver_mkbv0, 10);
  s_inputs->add_action(a_solver_mkbv1, 10);
  s_inputs->add_action(a_solver_mkbv2, 10);
  s_inputs->add_action(a_solver_mkbv3, 10);
  s_inputs->add_action(a_solver_mkbv4, 10);
  s_inputs->add_action(a_solver_mkbvsort, 2);
  s_inputs->add_action(a_solver_mktrue, 2);
  s_inputs->add_action(a_solver_mkfalse, 2);
  s_inputs->add_action(a_solver_mkbool, 2);
  s_inputs->add_action(a_solver_mkConst, 10);
  s_inputs->add_action(a_solver_simp, 2);
  /* empty transitions */
  s_inputs->add_action(t_inputs, 10, s_assert);
  s_inputs->add_action(t_inputs, 10, s_pushpop);
  s_inputs->add_action(t_inputs, 10, s_terms);

  /* State: assert ....................................................... */
  /* solver actions */
  s_assert->add_action(a_solver_assert, 20);
  s_assert->add_action(t_none, 5, s_inputs);
  s_assert->add_action(t_none, 2, s_pushpop);
  s_assert->add_action(t_none, 2, s_sat);
  s_assert->add_action(t_none, 10, s_terms);

  /* State: create terms ................................................. */
  /* sort actions */
  s_terms->add_action(a_sort_isbool, 1);
  s_terms->add_action(a_sort_isbv, 1);
  s_terms->add_action(a_sort_isnull, 1);
  s_terms->add_action(a_sort_getbvsize, 1);
  s_terms->add_action(a_sort_opeq, 1);
  s_terms->add_action(a_sort_opne, 1);
  /* term actions */
  s_terms->add_action(a_term_andterm, 1);
  s_terms->add_action(a_term_eqterm, 1);
  s_terms->add_action(a_term_getkind, 1);
  s_terms->add_action(a_term_getsort, 1);
  s_terms->add_action(a_term_impterm, 1);
  s_terms->add_action(a_term_isnull, 1);
  s_terms->add_action(a_term_iteterm, 1);
  s_terms->add_action(a_term_notterm, 1);
  s_terms->add_action(a_term_opeq, 1);
  s_terms->add_action(a_term_opne, 1);
  s_terms->add_action(a_term_orterm, 1);
  s_terms->add_action(a_term_xorterm, 1);
  /* opterm actions */
  s_terms->add_action(a_opterm_getkind, 1);
  s_terms->add_action(a_opterm_getsort, 1);
  s_terms->add_action(a_opterm_isnull, 1);
  s_terms->add_action(a_opterm_opeq, 1);
  s_terms->add_action(a_opterm_opne, 1);
  /* solver actions */
  s_terms->add_action(a_solver_getboolsort, 2);
  s_terms->add_action(a_solver_getintsort, 2);
  s_terms->add_action(a_solver_getnullsort, 2);
  s_terms->add_action(a_solver_getrealsort, 2);
  s_terms->add_action(a_solver_getregexpsort, 2);
  s_terms->add_action(a_solver_getrmsort, 2);
  s_terms->add_action(a_solver_getstringsort, 2);
  s_terms->add_action(a_solver_mkterm0, 10);
  s_terms->add_action(a_solver_mkterm1, 10);
  s_terms->add_action(a_solver_mkterm2, 20);
  s_terms->add_action(a_solver_mkterm3, 20);
  s_terms->add_action(a_solver_mktermn, 20);
  s_terms->add_action(a_solver_mktermop1, 20);
  s_terms->add_action(a_solver_simp, 2);
  /* empty transitions */
  s_terms->add_action(t_none, 5, s_assert);
  s_terms->add_action(t_none, 2, s_pushpop);
  s_terms->add_action(t_none, 2, s_sat);

  /* State: push / pop ................................................... */
  /* sort actions */
  s_pushpop->add_action(a_solver_push, 5);
  /* empty transitions */
  s_pushpop->add_action(t_none, 1, s_assert);
  s_pushpop->add_action(t_none, 1, s_inputs);
  s_pushpop->add_action(t_none, 1, s_sat);
  s_pushpop->add_action(t_none, 1, s_terms);

  /* State: sat .......................................................... */
  /* solver actions */
  s_sat->add_action(a_solver_checksat, 5);
  s_sat->add_action(a_solver_checkval, 5);
  /* empty transitions */
  s_sat->add_action(t_none, 5, s_assert);
  s_sat->add_action(t_none, 5, s_delete);
  s_sat->add_action(t_none, 5, s_inputs);
  s_sat->add_action(t_none, 5, s_pushpop);
  s_sat->add_action(t_none, 5, s_terms);

  /* State: delete ....................................................... */
  /* solver actions */
  s_delete->add_action(a_solver_delete, 10, s_final);

  /* --------------------------------------------------------------------- */
  /* Initial State                                                         */
  /* --------------------------------------------------------------------- */

  d_fsm.set_init_state(s_new);
}

/* -------------------------------------------------------------------------- */

#endif

}  // namespace cvc4
}  // namespace smtmbt
