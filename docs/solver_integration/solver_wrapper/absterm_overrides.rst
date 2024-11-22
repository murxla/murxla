Solver Wrapper Implementation for Terms
=======================================

Solver wrappers derive a term class from :cpp:class:`murxla::AbsTerm`, which
manages construction and destruction of solver term objects and implements
required and optional member function overrides.

Murxla uses naming convention ``<solver name (short)>Term`` for solver wrapper
term implementations, e.g., the cvc5 implementation is called ``Cvc5Term`` and
the Bitwuzla implementation is called ``BitwuzlaTerm``.

An example for a **required** override is member function
:cpp:func:`murxla::AbsTerm::hash()`, which returns a hash value for 
a given term. It is implemented in the solver wrapper for **cvc5** (using
its C++ API) as follows:

.. literalinclude:: ../../../src/solver/cvc5/cvc5_solver.cpp
   :language: cpp
   :start-after: docs-cvc5-term-hash start
   :end-before: docs-cvc5-term-hash end

An example for an **optional** override is member function
:cpp:func:`murxla::AbsTerm::get_children()`, which returns the children
of a given term. It is implemented in the solver wrapper for **Bitwuzla**
(using its C API) as follows:

.. literalinclude:: ../../../src/solver/bitwuzla/bitwuzla_solver.cpp
   :language: cpp
   :start-after: docs-bitwuzla-term-get_children start
   :end-before: docs-bitwuzla-term-get_children end

We use a helper function
``std::vector<Term> BitwuzlaTerm::bitwuzla_terms_to_terms(const BitwuzlaTerm**, size_t)``
to convert Bitwuzla term objects to Bitwuzla solver wrapper term objects,
which is defined as follows:

.. literalinclude:: ../../../src/solver/bitwuzla/bitwuzla_solver.cpp
   :language: cpp
   :start-after: docs-bitwuzla-term-bitwuzla_terms_to_terms start
   :end-before: docs-bitwuzla-term-bitwuzla_terms_to_terms end

.. note::

   Optional overrides have default implementations, but should be overriden
   if supported by the solver.
