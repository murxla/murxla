How to Integrate a Solver
=========================

Integrating a new solver under test into Murxla only requires to implement
a dedicated solver wrapper, which then interfaces with Murxla's core components.
The interface of the wrapper is defined at
:download:`src/solver/solver.hpp <../../src/solver/solver.hpp>`.
It defines abstract classes for sorts (:cpp:class:`murxla::AbsSort`),
terms (:cpp:class:`murxla::AbsTerm`) and the solver itself
(:cpp:class:`murxla::Solver`).

A solver wrapper derives from these three abstract classes and must at least
override the functions required to be overriden (see below). Additionally,
for each class, there exists a set of functions with default implementations
that should be overriden (if supported) to test the solver.

Overrides for Solver Wrapper Implementation
-------------------------------------------

.. toctree::
  :maxdepth: 2

  abssort_overrides
  absterm_overrides
  solver_overrides

Solver Wrapper: Full Interface Documentation
--------------------------------------------

.. toctree::
  :maxdepth: 2

  solver_wrapper/solver_wrapper

Solver Profiles
---------------

.. toctree::
  :maxdepth: 2

  solver_profile

