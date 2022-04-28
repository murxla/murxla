.. _actions:

FSM: Actions
============

An action defines a **specific interaction** with the solver under test.
The actual interaction of the :ref:`the base set of actions <base_actions>`
with the solver happens via one or more calls to the
API of the :ref:`solver wrapper <solver-wrappers>`.
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

For example, action :cpp:class:`murxla::ActionAssertFormula`
(from the :ref:`base set of actions <base_actions>`)
is responsible for asserting a random formula (SMT-LIB: ``assert``).
It generates the arguments to the action execution by picking a random
Boolean term:

.. literalinclude:: ../../../src/action.cpp
  :language: cpp
  :lines: 3159-3168

Its execution is implemented in :cpp:func:`murxla::ActionAssertFormula::run()`
and interacts with the solver via the generic solver wrapper API:

.. literalinclude:: ../../../src/action.cpp
  :language: cpp
  :lines: 3180-3186

Its replayed via :cpp:func:`murxla::ActionAssertFormula::untrace()` as follows:

.. literalinclude:: ../../../src/action.cpp
  :language: cpp
  :lines: 3170-3178


Solver-specific actions derived from :cpp:class:`murxla::Action`, on the other
hand, access the API of the solver under test directly, without going through
the solver wrapper API. For example, Bitwuzla defines a solver-specific
action ``BzlaActionTermIsEqualSort`` for comparing the sort of two terms,
and its execution ``BzlaActionTermIsEqualSort::run(Term, Term)`` is implemented
follows:

.. literalinclude:: ../../../src/solver/bzla/bzla_solver.cpp
  :language: cpp
  :lines: 2412-2421

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
   :lines: 31-36

.. doxygendefine:: MURXLA_TRACE

.. doxygendefine:: MURXLA_TRACE_RETURN

.. _fsm_configuration:

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
(see :ref:`states`).

Each action added to a state via :cpp:func:`murxla::State::add_action()` has a
weight, which is defined via its ``priority``, with ``1`` as the highest
priority, ``UINT32_MAX`` the lowest priority, and ``0`` corresponding to
disabling the action.

.. _base_actions:

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
