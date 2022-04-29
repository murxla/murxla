How to Integrate a Solver
=========================

Integrating a new solver under test only requires defining a
**solver configuration JSON profile** (see :ref:`solver-profiles`)
and implementing a dedicated **solver wrapper**.
The solver profile configures what and how to test, and the solver wrapper
interfaces with Murxla's core components.

.. toctree::
   :maxdepth: 2

   solver_profile
   solver_wrapper/solver_wrapper
