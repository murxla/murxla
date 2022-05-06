FSM: Actions
============

An action defines a **specific interaction** with the solver under test.
The actual interaction of the :ref:`the base set of actions
<advanced/fsm/action:The Base Set of Actions>`
with the solver happens via one or more calls to the
API of the :doc:`solver wrapper
<../../solver_integration/solver_wrapper/solver_wrapper>`.
Solver-specific actions directly interact with the API of the solver under
test.

Actions perform **three tasks**:

(1) randomly **generate** API call arguments (implemented in
    :cpp:func:`murxla::Action::generate()`)
(2) **execute** solver wrapper API calls with the generated set of arguments
    while tracing this execution (implemented in member function
    ``run(<args>)`` of an action)
(3) **replay** the trace of an action (implemented in
    :cpp:func:`murxla::Action::untrace()`)


As a **convention**, an action derived from :cpp:class:`murxla::Action`

- defines its identifier as a public static member ``s_name`` of type
  :cpp:type:`murxla::Action::Kind`, which is then used as its kind
  (see :cpp:func:`murxla::Action::get_kind()`)
- split out the actual execution of the solver wrapper API calls into a member
  function ``run(<args>)`` to ensure that :cpp:func:`murxla::Action::generate()`
  and :cpp:func:`murxla::Action::untrace()` execute an action in the same way

murxla::Action::generate()
--------------------------

Function :cpp:func:`murxla::Action::generate()` is responsible for checking an
action's preconditions and selecting (and, in execeptional cases, creating) the
arguments for its execution.
For this, it queries the solver manager
(see :cpp:class:`murxla::SolverManager`),
which provides a rich interface to pick and manage sorts, terms and manage
a solver's current state.

For example, action :cpp:class:`murxla::ActionAssertFormula`
(from the :ref:`the base set of actions
<advanced/fsm/action:The Base Set of Actions>`)
is responsible for asserting a random formula (SMT-LIB: ``assert``).
It asserts that the solver is initialized for Murxla-level debugging purposes,
and checks the required precondition that Boolean terms already exist in the
term database.
It then generates the arguments to the action execution by picking a
random Boolean term:

.. literalinclude:: ../../../src/action.cpp
   :language: cpp
   :start-after: docs-action-assertformula-generate start
   :end-before: docs-action-assertformula-generate end

In general, :cpp:func:`murxla::Action::generate()` should only pick existing
sorts and terms as arguments. However, there exist some exceptional cases
where it is beneficial to create arguments on demand. For example,
it makes no sense to globally create patterns
(:cpp:member:`murxla::Op::DT_MATCH_CASE`,
:cpp:member:`murxla::Op::DT_MATCH_BIND_CASE`)
for :cpp:member:`murxla::Op::DT_MATCH` (SMT-LIB: ``match``).
If created globally, they would be added to the term database and could
potentially be picked when selecting arguments for an operator other than
:cpp:member:`murxla::Op::DT_MATCH`, which shouldn't be the case.
Instead, we create these patterns on demand
in :cpp:func:`murxla::ActionMkTerm::generate()`.

For example, for a patterns that matches a specific non-nullary datatype constructor (of kind
:cpp:member:`murxla::Op::DT_MATCH_BIND_CASE`),
we need variables of a specific sort for each selector of the
constructor, and a quantified term that possibly uses these variables. We thus
create such patterns on demand as follows:

.. literalinclude:: ../../../src/action.cpp
   :language: cpp
   :dedent: 4
   :start-after: docs-action-mkterm-generate-dt_match_pattern-pre start
   :end-before: docs-action-mkterm-generate-dt_match_pattern-pre end

.. code::

   [ ... ]

.. literalinclude:: ../../../src/action.cpp
   :language: cpp
   :dedent: 10
   :start-after: docs-action-mkterm-generate-dt_match_pattern start
   :end-before: docs-action-mkterm-generate-dt_match_pattern end


murxla::Action<Name>::run(<args>)
---------------------------------

The execution of an action is implemented in a (usually private) member
function ``murxla::Action<Name>::run(<args>)``, which allows to use the same
action execution code for both :cpp:func:`murxla::Action::generate()` and
:cpp:func:`murxla::Action::untrace()`.
This function is responsible for :ref:`tracing <advanced/fsm/action:Tracing>`,
and is usually the
only one to interact with the solver via the generic solver wrapper API (or
directly via the solver API for solver-specific actions).
It is further responsible for registering created sorts and terms with the
solver manager (if to be used in the future).

For example, :cpp:func:`murxla::ActionAssertFormula::run()` is implemented
as follows:

.. literalinclude:: ../../../src/action.cpp
   :language: cpp
   :start-after: docs-action-assertformula-run start
   :end-before: docs-action-assertformula-run end

In this example, we first trace the actioan via :c:macro:`MURXLA_TRACE`,
then reset the solver state from *sat* to *assert* (see Fig. 4.1 of the
`SMT-LIB Standard 2.6
<https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf>`_),
and then assert the formula via :cpp:func:`murxla::Solver::assert_formula()`.

Actions that create new sorts and terms must trace these return values via
macro :c:macro:`MURXLA_TRACE_RETURN`
(see :ref:`tracing <advanced/fsm/action:Tracing>`).
Further, for testing assertions about the solver under test, we use macro
:c:macro:`MURXLA_TEST`.
For example, the action execution of action :cpp:class:`murxla::ActionMkSort`
is implemented as follows:

.. literalinclude:: ../../../src/action.cpp
   :language: cpp
   :start-after: docs-action-mksort-run start
   :end-before: docs-action-mksort-run end

This first traces the action, then asserts that the given sort kind is the
bit-vector sort kind (Murxla-level debug assertion), then creates the sort
via :cpp:func:`murxla::Solver::mk_sort()`, tests if the created sort has
the expected bit-width via :c:macro:`MURXLA_TEST`, adds the sort to the sort
database via :cpp:func:`murxla::SolverManager::add_sort()`, performs some
checks on the sort via :cpp:func:`murxla::ActionMkSort::check_sort()`, traces
the sort as return value via :c:macro:`MURXLA_TRACE_RETURN` and returns its id
(used for untracing only).

Macro for Testing Solver Behavior
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. doxygendefine:: MURXLA_TEST

murxla::Action::untrace()
--------------------------

Actions are replayed via :cpp:func:`murxla::Action::untrace()`,
which takes a vector of tokens as arguments, converts those tokens into
sort and term objects where necessary, and executes the action via
:cpp:func:`murxla::Action::generate()`.

For example, action :cpp:class:`murxla::ActionAssertFormula` is replayed via
:cpp:func:`murxla::ActionAssertFormula::untrace()` as follows:

.. literalinclude:: ../../../src/action.cpp
   :language: cpp
   :start-after: docs-action-assertformula-untrace start
   :end-before: docs-action-assertformula-untrace end

Murxla provides a set of
:ref:`macros for checking expected properties
<advanced/fsm/action:Macros for Checking Trace Tokens>` of given
action line trace tokens.
In the example above, we use macro :c:macro:`MURXLA_CHECK_TRACE_NTOKENS` to
check if ``tokens`` holds exactly one trace token (the id of the asserted term).
We retrieve the term matched to the traced term id via
:cpp:func:`murxla::Action::get_untraced_term()` (similarly, traced sorts are
retrieved from the sort database via
:cpp:func:`murxla::Action::get_untraced_sort()`),
and check if we were able to match the term (or if the given id is unknown)
via :c:macro:`MURXLA_CHECK_TRACE_TERM` (similarly, for sorts, via
:c:macro:`MURXLA_CHECK_TRACE_SORT`).


Macros for Checking Trace Tokens
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Murxla defines the following macros for checking trace line properties.
These macros are only used for error checking traces when untracing.

.. doxygengroup:: macros-check-trace
   :content-only:

Solver-specific Actions
-----------------------

Solver-specific actions derived from :cpp:class:`murxla::Action`
usually access the API of the solver under test directly, without going through
the solver wrapper API.

For example, Bitwuzla defines a solver-specific
action ``BzlaActionTermIsEqualSort`` for comparing the sort of two terms,
and its execution ``BzlaActionTermIsEqualSort::run(Term, Term)`` is implemented
follows:

.. literalinclude:: ../../../src/solver/bzla/bzla_solver.cpp
   :language: cpp
   :start-after: docs-bzla-action-termisequalsort-run start
   :end-before: docs-bzla-action-termisequalsort-run end

Tracing
-------

In order to be able to replay a sequence of actions that triggered an issue
in the solver under test, we trace each action execution in a simple,
easy-to-parse output format.

Each action trace line follows the pattern

.. code::

   <solver RNG seed> <action kind> [<args ...>]

optionally followed by a return statement if the action creates new sorts or
terms:

.. code::

   return <values ...>

Additionally, in the first line of a trace, Murxla records the command line
options provided to generate this trace.

For example, the following trace triggered an issue in cvc5:

.. code-block:: trace
   :linenos:

   set-murxla-options --cvc5 -t 1 -m 10000 --fuzz-opts
   92880 new
   32252 set-logic BVFPNIA
   96760 set-option incremental false
   3046 set-option solve-int-as-bv 925956265872928556
   36189 mk-sort SORT_INT
   return s14
   19629 mk-const s14 "_x35"
   return t46
   81876 mk-term OP_INT_DIV SORT_INT 2 t46 t46
   return t125 s14
   50301 mk-term OP_INT_LTE SORT_BOOL 2 t125 t125
   return t127 s12
   88360 cvc5-simplify t127

As indicated in the first line, this trace  was generated when running Murxla
continuously for 1000 runs to test cvc5 with a one second time limit per run
and with option fuzzing enabled.
Line **2** creates a new solver instance, line **3** restricts the logic to
``BVFPNIA``, lines **4-5** enable incremental solving and a cvc5-specific
option that translates integers to bit-vectors, line **6** queries the integer
sort from the solver, lines **8-9** create and return a constant of that sort,
lines **10-11** create and return an integer division
(:cpp:member:`murxla::Op::INT_DIV`) and an integer less-than-or-equal
(:cpp:member:`murxla::Op::INT_LTE`) term, and line **14** executes a
cvc5-specific action ``cvc5-simplify`` to simplify the integer division term
``t127``.

As shown in lines **10-11**, when creating terms, we trace argument lists
while also providing the number of arguments, e.g., ``2 t46 t46`` in line
**10**. If an operator is indexed, we similarly provide the list of indices
with its size, e.g., a bit-vector extract from index **4** to **3**
on a term ``t99`` of sort ``9`` we would trace as

.. code:: trace

   <seed> mk-term OP_BV_EXTRACT SORT_BV 9 1 t99 2 4 3

Generally, also for solver-specific actions, it is recommended to also trace
the size of argument lists to an action whenever they can be of arbitrary size.

Further, as shown in lines **11** and **13**, for actions that create new terms
that should be added to the term database (and are thus traced in a ``return``
statement), we not only need to the trace the returned term but also its sort.
This is due to the fact that some operators create new sorts
(e.g., :cpp:member:`murxla::Op::BV_EXTRACT`) that may not have been encountered
in the trace yet, but are added to the sorts database and can thus occur
later in the trace.

We use macro :c:macro:`MURXLA_TRACE` for tracing action executions, and macro
:c:macro:`MURXLA_TRACE_RETURN` for tracing an action's return values.

Furthermore, in order to be able to **deterministically** replay a given trace,
even when minimized, solver wrappers maintain an independent RNG to decouple
non-deterministic choices in the solver wrapper from Murxla's main RNG.
The solver wrapper RNG is seeded with a random seed at the
beginning of an action's execution, and this seed is traced as
``<solver RNG seed>``.
Each call to ``run()`` must first trace the Action's execution via macro
:c:macro:`MURXLA_TRACE`, and we automatically seed the solver wrapper's RNG
there and prepend the seed to the trace line:

.. literalinclude:: ../../../src/action.hpp
   :language: cpp
   :start-after: docs-murxla_trace start
   :end-before: docs-murxla_trace end

.. doxygendefine:: MURXLA_TRACE

.. doxygendefine:: MURXLA_TRACE_RETURN

FSM Configuration
-----------------

Actions are added to states of the FSM via
:cpp:func:`murxla::State::add_action()` while optionally defining a next
state to transition into (or remaining in the state it's been added to).
We further derive a class :cpp:class:`murxla::Transition` from
:cpp:class:`murxla::Action`, which represents a transition from one state to
the next without executing any solver API calls (an *empty* action).

Existing states are retrieved via :cpp:func:`murxla::FSM::get_state()`,
new states are created and added via :cpp:func:`murxla::FSM::new_state()`
(see :doc:`state`).

Each action added to a state via :cpp:func:`murxla::State::add_action()` has a
weight, which is defined via its ``priority``, with ``1`` as the highest
priority, ``UINT32_MAX`` the lowest priority, and ``0`` corresponding to
disabling the action.

The Base Class for Actions
--------------------------

.. doxygenclass:: murxla::Action
    :members:
    :undoc-members:

Default Transitions
-------------------

A murxla::Transition is an empty action, i.e., an action that does not generate
and execute solver API calls. It is used to simply transition from the current
state to the next state.

.. doxygenclass:: murxla::Transition
.. doxygenclass:: murxla::TransitionDefault
.. doxygenclass:: murxla::TransitionCreateInputs
.. doxygenclass:: murxla::TransitionCreateSorts

The Base Set of Actions
-----------------------

.. doxygenclass:: murxla::ActionNew
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionDelete
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionSetLogic
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionSetOption
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionSetOptionReq
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkSort
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkTerm
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkConst
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkFun
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkVar
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkValue
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkSpecialValue
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionInstantiateSort
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionAssertFormula
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionCheckSat
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionCheckSatAssuming
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionGetUnsatAssumptions
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionGetUnsatCore
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionGetValue
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionPush
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionPop
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionReset
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionResetAssertions
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionPrintModel
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionTermGetChildren
    :members:
    :undoc-members:
