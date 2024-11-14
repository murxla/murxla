Operators
=========

Murxla **globally** defines a :doc:`base set of operator kinds
<operator_kinds>` as static const members of type :cpp:type:`murxla::Op::Kind`
of class :cpp:class:`murxla::Op`.
Operator kinds are maintained by an operator kind manager
(:cpp:class:`murxla::OpKindManager`),
and each kind is associated with an :cpp:class:`murxla::Op` object, which
maintains configuration data such as its associated theory, arity, number of
indices, the sort kind of a term of that operator kind and the sort kinds of
its arguments.

**Solver-specific** operator kinds are (by convention) defined as a static
const member of type :cpp:type:`murxla::Op::Kind` of the solver wrapper
implementation of :cpp:class:`murxla::AbsTerm`.
By convention, we prefix solver-specific operator kinds with the solver's
(short) name.
For example, the solver wrapper for Bitwuzla defines a bit-vector decrement
operator as member of :cpp:class:`murxla::BitwuzlaTerm` as

.. literalinclude:: ../../src/solver/bitwuzla/bitwuzla_solver.hpp
   :language: cpp
   :start-after: docs-bitwuzla-op-bv_dec start
   :end-before: docs-bitwuzla-op-bv_dec end

Solver-specific operator kinds are added to the
:ref:`operator kind manager <advanced/operator:Operator Management>` via
overriding :cpp:func:`murxla::Solver::configure_opmgr`, e.g.,

.. literalinclude:: ../../src/solver/bitwuzla/bitwuzla_solver.cpp
   :language: cpp
   :start-after: docs-bitwuzla-solver-configure_opmgr_bv_dec start
   :end-before: docs-bitwuzla-solver-configure_opmgr_bv_dec end

Configuration Macros
--------------------
.. doxygendefine:: MURXLA_MK_TERM_N_ARGS
.. doxygendefine:: MURXLA_MK_TERM_N_ARGS_BIN

Operator and Operator Kind
--------------------------

.. doxygentypedef:: murxla::OpKindVector
.. doxygentypedef:: murxla::OpKindSet
.. doxygentypedef:: murxla::OpKindMap
.. doxygentypedef:: murxla::OpKinds

.. doxygenstruct:: murxla::Op
    :members:
    :undoc-members:

Operator Management
-------------------
.. doxygenclass:: murxla::OpKindManager
    :members:
    :undoc-members:
