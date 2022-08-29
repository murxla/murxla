Installation
============

Murxla is available on `GitHub <https://github.com/murxla/murxla>`_.

Building Murxla
---------------

.. code-block:: bash

  git clone https://github.com/murxla/murxla.git
  cd murxla
  cd build
  mkdir build
  cmake ..
  make

During the configuration phase (``cmake ..``), the build system checks whether
any of the supported solvers are installed. Configure a custom solver
installation path ``<path>`` via

.. code-block:: bash

  cmake .. -DCMAKE_PREFIX_PATH=<path>

Alternatively, you can use the ``scripts/setup-solvers.sh`` script to setup
solvers supported by Murxla.
By default the script will download and build all supported solvers. Please
refer to ``setup-solver.sh -h`` for further options.

After successful compilation you can find the Murxla binary in ``build/bin/``.
Please refer to the :doc:`user_guide` for how to use Murxla.

Supported Solvers
-----------------

Murxla currently has native integration for the following solvers:

- `Bitwuzla <https://bitwuzla.github.io>`_
- `Boolector <https://boolector.github.io>`_
- `cvc5 <https://cvc5.github.io>`_
- `Yices <https://github.com/SRI-CSL/yices2>`_

Solvers without native integration can still be tested via the SMT-LIBv2
interface (option ``--smt2 <solver-binary>``).


Code Coverage Reports
---------------------

Generating coverage reports requires `lcov` and `fastcov`.
Make sure to install `fastcov` via `pip`.

1. Configure Murxla with ``cmake .. -DGCOV=ON`` and make sure that the relevant
   solvers are configured and built to produce coverage information.
2. Prior to running Murxla, reset the coverage data via ``make coverage-reset``
3. Run Murxla for some time
4. Generate the coverage report via ``make coverage``, which can be found in
   ``coverage/index.html`` of the build directory.
