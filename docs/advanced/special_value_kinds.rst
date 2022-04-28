.. _special-value-kinds:

Pre-Defined Special Value Kinds
===============================

The list of special value kinds globally defined in
:cpp:class:`murxla::AbsTerm`.

Special values are created via :cpp:func:`murxla::Solver::mk_special_value()`.
The set of special value kinds can be extended with solver-specific special
value kinds via overriding :cpp:fun:`murxla::Solver::add_special_value()`.

.. doxygengroup:: special-value-kinds
   :content-only:


