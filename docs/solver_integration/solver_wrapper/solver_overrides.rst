Solver Wrapper Implementation for Solver
========================================

Solver wrappers derive a solver class from :cpp:class:`murxla::Solver`, which
manages construction and destruction of an instance of the solver under test.
It further implements required and optional member function overrides.

Murxla uses naming convention ``<solver name (short)>Solver`` for solver
wrapper solver implementations, e.g., the cvc5 implementation is called
``Cvc5Solver`` and the Bitwuzla implementation is called ``BzlaSolver``.

Note that the constructor of :cpp:class:`murxla::Solver` is not to be overriden.
A solver instance is created and deleted via the required member function
overrides of functions
:cpp:func:`murxla::Solver::new_solver()` and
:cpp:func:`murxla::Solver::delete_solver()`.
For example, in the solver wrapper for **cvc5** (using its C++ API) these are
implemented as follows:

.. literalinclude:: ../../../src/solver/cvc5/cvc5_solver.cpp
   :language: cpp
   :start-after: docs-cvc5-solver-new_solver start
   :end-before: docs-cvc5-solver-new_solver end

.. literalinclude:: ../../../src/solver/cvc5/cvc5_solver.cpp
   :language: cpp
   :start-after: docs-cvc5-solver-delete_solver start
   :end-before: docs-cvc5-solver-delete_solver end

Another example for a **required** override is member function
:cpp:func:`murxla::Solver::get_name()`, which returns the name of the
solver under test.
It is implemented for **cvc5** as follows:

.. literalinclude:: ../../../src/solver/cvc5/cvc5_solver.cpp
   :language: cpp
   :start-after: docs-cvc5-solver-get_name start
   :end-before: docs-cvc5-solver-get_name end

An example for an **optional** override is member function
:cpp:func:`murxla::Solver::get_unsat_core()`, which returns a vector of
terms representing the unsat core of the currently asserted formula.
It is implemented in the solver wrapper for **Bitwuzla**
(using its C API) as follows:

.. literalinclude:: ../../../src/solver/bzla/bzla_solver.cpp
   :language: cpp
   :start-after: docs-bzla-solver-get_unsat_core start
   :end-before: docs-bzla-solver-get_unsat_core end

The following list provides all the member functions of class
:cpp:class:`murxla::Solver` that are required or optional to be
overriden by a solver wrapper.

.. note::

   Optional overrides have default implementations, but should be overriden
   if supported by the solver.


Solver: Functions Required to be Overriden
------------------------------------------
.. doxygengroup:: solver-must-override
   :content-only:

Solver: Functions to be Overriden Optionally
--------------------------------------------
.. doxygengroup:: solver-may-override
   :content-only:

