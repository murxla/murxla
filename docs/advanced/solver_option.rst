.. _solver-options:

Solver Options
==============

Murxla supports **option fuzzing**, that is, randomly configuring solver
options based on the options model of the solver.
This options model is advertised to Murxla via configuring a
:cpp:class:`murxla::SolverOption` for each option and adding it to the
solver manager via :cpp:func:`murxla::Solver::configure_options()`
(for more details, see :ref:`configure_solver_options`).

Murxla supports Boolean options (:cpp:class:`murxla::SolverOptionBool`),
numeric options (:cpp:class:`murxla::SolverOptionNum`) and
options with multiple string values (:cpp:class:`murxla::SolverOptionList`).

.. doxygenclass:: murxla::SolverOption
    :members:
    :private-members:

.. doxygenclass:: murxla::SolverOptionBool
    :members:
    :private-members:

.. doxygenclass:: murxla::SolverOptionNum
    :members:
    :private-members:

.. doxygenclass:: murxla::SolverOptionList
    :members:
    :private-members:
