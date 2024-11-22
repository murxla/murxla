Solver Wrapper Implementation for Sorts
=======================================

Solver wrappers derive a sort class from :cpp:class:`murxla::AbsSort`, which
manages construction and destruction of solver sort objects and implements
required and optional member function overrides.

Murxla uses naming convention ``<solver name (short)>Sort`` for solver wrapper
sort implementations, e.g., the cvc5 implementation is called ``Cvc5Sort`` and
the Bitwuzla implementation is called ``BitwuzlaSort``.

An example for a **required** override is member function
:cpp:func:`murxla::AbsSort::equals()`, which determines if two given sorts
are equal. It is implemented in the solver wrapper for **cvc5** (using its
C++ API) as follows:

.. literalinclude:: ../../../src/solver/cvc5/cvc5_solver.cpp
   :language: cpp
   :start-after: docs-cvc5-sort-equals start
   :end-before: docs-cvc5-sort-equals end

An example for an **optional** override is member function
:cpp:func:`murxla::AbsSort::is_bv()`, which determines if a given sort
is a bit-vector sort. It is implemented in the solver wrapper for **Bitwuzla**
(using its C API) as follows:

.. literalinclude:: ../../../src/solver/bitwuzla/bitwuzla_solver.cpp
   :language: cpp
   :start-after: docs-bitwuzla-sort-is_bv start
   :end-before: docs-bitwuzla-sort-is_bv end

.. note::

   Optional overrides have default implementations, but should be overriden
   if supported by the solver.

