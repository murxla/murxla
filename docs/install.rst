Installation
============

.. code-block:: bash

  git clone https://github.com/murxla/murxla.git
  cd murxla
  mkdir build
  cmake ..
  make

During the configuration phase (``cmake ..``) the build system checks whether any
of the supported solvers are installed. If a solver was installed to a custom
path ``<path>`` you can tell the build system by specifying the path as follows:

.. code-block:: bash

  cmake .. -DCMAKE_PREFIX_PATH=<path>

After successful compilation you can find the Murxla binary in ``build/bin/``.
Please refer to the :ref:`User Guide <user-guide>` for how to use Murxla.

Supported Solver
****************

Murxla currently has native integration for the following solvers:

- `Bitwuzla <https://github.com/bitwuzla/bitwuzla>`_
- `Boolector <https://github.com/boolector/boolector>`_
- `cvc5 <https://github.com/cvc5/cvc5>`_
- `Yices <https://github.com/SRI-CSL/yices2>`_

Solvers without native integration can still be tested via the SMT-LIBv2
interface (option ``--smt2 <solver-binary>``).


Code Coverage Reports
*********************

Generating coverage reports requires `lcov` and `fastcov`.
Make sure to install `fastcov` via `pip`.

1. Configure Murxla with ``cmake .. -DGCOV=ON`` and make sure that the relevant
   solvers are configured and built to produce coverage information.
2. Prior to running Murxla reset the coverage data via ``make coverage-reset``
3. Run Murxla for some time
4. Generate the coverage report via ``make coverage``, which can be found in
   ``coverage/index.html`` of the build directory.
