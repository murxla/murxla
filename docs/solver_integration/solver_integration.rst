How to Integrate a Solver
=========================

Integrating a new solver under test only requires to implement a dedicated
solver wrapper, which then interfaces with Murxla's core components.
The interface of the wrapper is defined at
:download:`src/solver/solver.hpp <../../src/solver/solver.hpp>`.
It defines abstract classes for sorts (:cpp:class:`murxla::AbsSort`),
terms (:cpp:class:`murxla::AbsTerm`) and the solver itself
(:cpp:class:`murxla::Solver`).

A solver wrapper derives from these three abstract classes and must at least
override the member functions required to be overriden. Additionally,
for each class, there exists a set of member functions with default
implementations that should be overriden (if supported) to test the solver
(see :ref:`the list of required and optional overrides <wrapper_overrides>`
below).

.. _wrapper_overrides:

Overrides for Solver Wrapper Implementation
-------------------------------------------

The following list provides all the member functions of classes
:cpp:class:`murxla::AbsSort`, :cpp:class:`murxla::AbsTerm` and
:cpp:class:`murxla::Solver` that are required or optional to be
overriden by a solver wrapper.

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

