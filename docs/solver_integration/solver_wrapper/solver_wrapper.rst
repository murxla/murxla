.. _solver-wrappers:

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

  abssort
  absterm
  solver

A solver wrapper **derives** from these three abstract classes and must
**at least** override the member functions required to be overriden.
Additionally, for each class, there exists a set of member functions with
default implementations that **should** be overriden (if supported) to test the
solver (see :ref:`the list of required and optional overrides
<wrapper_overrides>` below).

.. toctree::
  :maxdepth: 2

  overrides

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

  sort
  term

