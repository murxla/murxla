Solver Wrappers
===============

A solver wrapper provides the glue code between the core components of Murxla
and the solver under test.
The **interface** for solver wrappers is defined at
`src/solver/solver.hpp <https://github.com/murxla/murxla/blob/main/src/solver/solver.hpp>`_.

The wrapper's interface defines **abstract classes** for sorts
(:cpp:class:`murxla::AbsSort`), terms (:cpp:class:`murxla::AbsTerm`) and the
solver itself (:cpp:class:`murxla::Solver`).

.. toctree::
  :maxdepth: 2

  ../../advanced/solver_wrapper_interface/abssort
  ../../advanced/solver_wrapper_interface/absterm
  ../../advanced/solver_wrapper_interface/solver

Solver Wrapper Implementation
-----------------------------

A solver wrapper **derives** solver-specific classes from the three abstract
classes of the interface and must **at least** override the member functions
required to be overriden.
Additionally, for each class, there exists a set of member functions with
default implementations that **should** be overriden (if supported) to test the
solver (see :doc:`the list of required and optional overrides
<overrides>` below).

.. toctree::
  :maxdepth: 2

  overrides

Random Number Generator (RNG)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Murxla's generic solver API as implemented in the solver wrapper interface
aims at providing an interface for the solver under test that allows to plug
in any variants of API functions for specific SMT-LIB features.
For example, :cpp:func:`murxla::Solver::mk_value()` provides one interface
for creating bit-vector values
(``murxla::Solver::mk_value(Sort sort, const std::string& value, Base base)``),
but most solvers provide API functions that take either a string or integer
representation for the value as argument.
For cases like this, it is useful to be able to randomly decide, for each call,
which API function of the solver under test to use.

In order to be able to deterministically replay a given trace, even when
minimized, it is necessary to decouple non-deterministic choices
in the solver wrapper from Murxla's main RNG. Thus, the solver wrapper base
class maintains an independent RNG, which is seeded with a random seed at the
beginning of each call to the execution function of an action (naming
convention: ``<Action>::run(<args>)``). This seed is traced, and since each
call to ``run()`` must first trace the Action's execution via macro
:c:macro:`MURXLA_TRACE`, we automatically seed the solver wrapper's RNG
there and prepend the seed to the trace line:

.. literalinclude:: ../../../src/action.hpp
   :language: cpp
   :start-after: docs-murxla_trace start
   :end-before: docs-murxla_trace end

The solver wrapper's RNG can be directly accessed as the protected member
:cpp:member:`murxla::Solver::d_rng`, or via
:cpp:func:`murxla::Solver::get_rng()`.


Global Sort and Term Handling
-----------------------------

Murxla defines types
:cpp:type:`Sort<murxla::Sort>` and :cpp:type:`Term<murxla::Term>`
for sort and term representations
which are shared pointers
(`std::shared_ptr <https://en.cppreference.com/w/cpp/memory/shared_ptr>`_)
to :cpp:class:`AbsSort<murxla::AbsSort>`
and :cpp:class:`AbsTerm<murxla::AbsTerm>`.
We only deal with :cpp:type:`Sort<murxla::Sort>` and
:cpp:type:`Term<murxla::Term>` objects in Murxla core components
and at the interface between Murxla and the solver wrapper.

.. toctree::
  :maxdepth: 2

  ../../advanced/sort
  ../../advanced/term

Solver-Specific Extensions
--------------------------

Murxla supports various extensions with **solver-specific features**,
i.e., features that cannot be plugged in via the generic solver wrapper API.

Operator Kinds
^^^^^^^^^^^^^^

Murxla defines a :doc:`base set of operator kinds
<../../advanced/operator_kinds>` as static const members of type
:cpp:type:`murxla::Op::Kind` of class :cpp:class:`murxla::Op`.
Solver-specific operator kinds are (by convention) defined as members of the
solver wrapper implementation of :cpp:class:`murxla::AbsTerm`.
By convention, we prefix solver-specific operator kinds with the solver's
(short) name.
For example, the solver wrapper for Bitwuzla defines a bit-vector decrement
operator as member of :cpp:class:`murxla::BitwuzlaTerm` as

.. literalinclude:: ../../../src/solver/bitwuzla/bitwuzla_solver.hpp
   :language: cpp
   :start-after: docs-bitwuzla-op-bv_dec start
   :end-before: docs-bitwuzla-op-bv_dec end

Solver-specific operator kinds are added to the
:ref:`operator kind manager <advanced/operator:Operator Management>` via
overriding :cpp:func:`murxla::Solver::configure_opmgr`, e.g.,

.. literalinclude:: ../../../src/solver/bitwuzla/bitwuzla_solver.cpp
   :language: cpp
   :start-after: docs-bitwuzla-solver-configure_opmgr_bv_dec start
   :end-before: docs-bitwuzla-solver-configure_opmgr_bv_dec end


Special Value Kinds
^^^^^^^^^^^^^^^^^^^

Murxla introduces the notion of :cpp:type:`murxla::AbsTerm::SpecialValueKind`
for values that can be considered a special value in a theory, e.g.,
floating-point NaN (of a given floating-point format), or the minimum signed
bit-vector value (of a given bit-width).

Terms representing special values are created via
:cpp:func:`murxla::Solver::mk_special_value()`. A list of all special value
kinds defined in :cpp:class:`murxla::AbsTerm` is provided below:

.. toctree::
  :maxdepth: 1

  ../../advanced/special_value_kinds

As with solver-specific operator kinds, solver-specific special value kinds are
(by convention) defined as a static const member of type
:cpp:type:`murxla::AbsTerm::SpecialValueKind` of the solver wrapper
implementation of :cpp:class:`murxla::AbsTerm`.
And again, by convention, we prefix solver-specific special value kinds with
the solver's (short) name.

Solver wrappers can extend the pre-defined list of special value kinds with
solver-specific kinds via
:cpp:func:`murxla::Solver::add_special_value()`.

Actions
^^^^^^^

Murxla defines a base API model implementing SMT-LIB semantics
(as a finite state machine, see :doc:`../../advanced/fsm/fsm`) with a
:ref:`base set of actions <advanced/fsm/action:The Base Set Of Actions>`.
This base API model can be extended with solver-specific features that cannot
be immediately plugged into the base API Model by adding transitions with
associated solver-specific actions to the FSM via overriding
:cpp:func:`murxla::Solver::configure_fsm()`.

Solver-specific actions directly interact with the API of the solver under test
(see :doc:`../../advanced/fsm/action`).
They are added to an existing (or new, solver-specific)
state while defining its priority and (optionally) a next state via
:cpp:func:`murxla::State::add_action()`
(see :ref:`advanced/fsm/action:FSM Configuration`).

Features Unsupported By The Solver Under Test
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Murxla requires to define a solver profile (see :doc:`../solver_profile`) to
define the solver test configuration. The solver profile allows to define
which theories to consider and to disable unsupported sort and operator kinds.
Unsupported actions can be disabled via overriding
:cpp:func:`murxla::Solver::disable_unsupported_actions()`.

Solver Options
--------------

To enable option fuzzing, a solver wrapper can advertise a set of options
to Murxla by overriding :cpp:func:`murxla::Solver::configure_options()`.
Options can be added via the :cpp:func:`murxla::SolverManager::add_option()`
of the solver manager object passed to
:cpp:func:`murxla::Solver::configure_options()`.

Murxla distinguishes three different
:doc:`option types <../../advanced/solver_option>`:

- Boolean options (:cpp:class:`murxla::SolverOptionBool`)
- Numeric options (:cpp:class:`murxla::SolverOptionNum`)
- Options with multiple string values (:cpp:class:`murxla::SolverOptionList`)

For example, Bitwuzla supports querying all available options via its API.
This makes adding options via overriding
:cpp:func:`murxla::Solver::configure_options()`
very easy since it allows to add options in an automated way:

.. literalinclude:: ../../../src/solver/bitwuzla/bitwuzla_solver.cpp
   :language: cpp
   :start-after: docs-bitwuzla-solver-configure_options start
   :end-before: docs-bitwuzla-solver-configure_options end
