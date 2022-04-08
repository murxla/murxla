Solver Wrapper Implementation for Terms
=======================================

Solver wrappers derive a term class from :cpp:class:`murxla::AbsTerm`, which
manages construction and destruction of solver term objects and implements
required and optional member function overrides.

Murxla uses naming convention ``<solver name (short)>Term`` for solver wrapper
term implementations, e.g., the cvc5 implementation is called ``Cvc5Term`` and
the Bitwuzla implementation is called ``BzlaTerm``.

An example for a **required** override is member function
:cpp:func:`murxla::AbsTerm::hash()`, which returns a hash value for 
a given term. It is implemented in the solver wrapper for **cvc5** (using
its C++ API) as follows:

.. literalinclude:: ../../src/solver/cvc5/cvc5_solver.cpp
   :language: cpp
   :lines: 974-978

An example for an **optional** override is member function
:cpp:func:`murxla::AbsTerm::get_children()`, which returns the children
of a given term. It is implemented in the solver wrapper for **Bitwuzla**
(using its C API) as follows:

.. literalinclude:: ../../src/solver/bzla/bzla_solver.cpp
   :language: cpp
   :lines: 673-680

We use a helper function
``std::vector<Term> BzlaTerm::bzla_terms_to_terms(const BitwuzlaTerm**, size_t)``
to convert Bitwuzla term objects to Bitwuzla solver wrapper term objects,
which is defined as follows:

.. literalinclude:: ../../src/solver/bzla/bzla_solver.cpp
   :language: cpp
   :lines: 471-480

The following list provides all the member functions of class
:cpp:class:`murxla::AbsTerm` that are required or optional to be
overriden by a solver wrapper.

.. note::

   Optional overrides have default implementations, but should be overriden
   if supported by the solver.

AbsTerm: Functions Required to be Overriden
-------------------------------------------
.. doxygengroup:: term-must-override
   :content-only:

AbsTerm: Functions to be Overriden Optionally
---------------------------------------------
.. doxygengroup:: term-may-override
   :content-only:

