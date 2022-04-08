Solver Wrapper Implementation for Sorts
=======================================

Solver wrappers derive a sort class from :cpp:class:`murxla::AbsSort`, which
manages construction and destruction of solver sort objects and implements
required and optional member function overrides.

Murxla uses naming convention ``<solver name (short)>Sort`` for solver wrapper
sort implementations, e.g., the cvc5 implementation is called ``Cvc5Sort`` and
the Bitwuzla implementation is called ``BzlaSort``.

An example for a **required** override is member function
:cpp:func:`murxla::AbsSort::equals()`, which determines if two given sorts
are equal. It is implemented in the solver wrapper for **cvc5** (using its
C++ API) as follows:

.. literalinclude:: ../../src/solver/cvc5/cvc5_solver.cpp
   :language: cpp
   :lines: 61-70

An example for an **optional** override is member function
:cpp:func:`murxla::AbsSort::is_bv()`, which determines if a given sort
is a bit-vector sort. It is implemented in the solver wrapper for **Bitwuzla**
(using its C API) as follows:

.. literalinclude:: ../../src/solver/bzla/bzla_solver.cpp
   :language: cpp
   :lines: 108-112

The following list provides all the member functions of class
:cpp:class:`murxla::AbsSort` that are required or optional to be
overriden by a solver wrapper.

.. note::

   Optional overrides have default implementations, but should be overriden
   if supported by the solver.

AbsSort: Functions Required to be Overriden
-------------------------------------------

.. doxygengroup:: sort-must-override
   :content-only:

AbsSort: Functions to be Overriden Optionally
---------------------------------------------
.. doxygengroup:: sort-may-override
   :content-only:

