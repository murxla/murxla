.. _solver-wrappers:

Solver Wrappers
===============

.. contents::
  :local:

Murxla defines types for sort and term representations
(:cpp:type:`Sort<murxla::Sort>` and :cpp:type:`Term<murxla::Term>`),
which are shared pointers
(`std::shared_ptr <https://en.cppreference.com/w/cpp/memory/shared_ptr>`_)
to :cpp:class:`AbsSort<murxla::AbsSort>`
and :cpp:class:`AbsTerm<murxla::AbsTerm>`.

.. todo:: more on what to implement in solver wrapper

----

Sort
----

.. doxygentypedef:: murxla::Sort

.. doxygenfunction:: murxla::operator==(const Sort& a, const Sort& b)
.. doxygenfunction:: murxla::operator!=(const Sort& a, const Sort& b)
.. doxygenfunction:: murxla::operator<<(std::ostream& out, const Sort s)
.. doxygenfunction:: murxla::operator<<(std::ostream& out, const std::vector<Sort>& vector)

----

Term
----

.. doxygentypedef:: murxla::Term

.. doxygenfunction:: murxla::operator==(const Term& a, const Term& b)
.. doxygenfunction:: murxla::operator!=(const Term& a, const Term& b)
.. doxygenfunction:: murxla::operator<<(std::ostream& out, const Term t)
.. doxygenfunction:: murxla::operator<<(std::ostream& out, const std::vector<Term>& vector)

----

Solver Wrapper Interface
------------------------

.. toctree::
  :maxdepth: 2

  solver/abssort
  solver/absterm
  solver/solver
