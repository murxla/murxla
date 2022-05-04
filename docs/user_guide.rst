User Guide
==========

This guide covers the most common usage scenarios of Murxla.

Testing an Integrated Solver
----------------------------

Fuzz testing a solver natively supported by Murxla requires only to enable
the solver via the corresponding solver option.
For example, testing Bitwuzla is done as follows.

.. code-block:: bash

   murxla --bzla


Murxla continously prints overall fuzzing statistics while running.
``seed`` refers to the random number generator seed that produced the run,
``runs`` corresponds to the total number of runs so far,
``r/s`` is the run throughput per second,
``sat``, ``unsat``, ``unknw`` are the number sat/unsat/unknown answers of the
solver, while ``to`` and ``err`` refer to the number of timeouts and errors
encountered so far.

Each time Murxla encounters a timeout it will print the seed of the instance.
When an error is encountered it will also print the recorded trace as well
as the error message of the solver.
Murxla groups error traces that trigger the same error message into
subdirectories (1, 2, 3, ...) and stores the corresponding error message in
in a file called ``error.txt``.

.. code-block:: bash

                seed  runs      r/s   sat unsat unknw    to   err
    b26a7cc83776f149    50    40.49    39    42     0     0     0 [timeout]
    98f13b87a5752b3b   136    35.10   129    88     0     1     0 [timeout]
    970db7d5eb91f78e   137    28.01   132    90     0     2     0 [timeout]
    8ff9472ab9d37c40   237    30.28   219   159     0     3     0 [timeout]
    aacf82a16bb98777   366    31.92   328   248     0     4     0 [timeout]
    f086b8bb42a62fc5   382    30.20   349   261     0     5     0 [timeout]
    ...
    2287b2bd77a3b84c  1209    21.53  1033   825     0    23     0 [error:1] 1/murxla-2287b2bd77a3b84c.trace

    [bzlachkmodel] bzla_check_model: invalid model
    ...

.. note::

   The default time limit per run is 1 second and can be changed via option
   ``-t``.


Testing via the SMT2-LIB Interface
----------------------------------


Tracing and Untracing
---------------------


Minimizing Traces
-----------------


Solver API Traces
-----------------


Command Line Options
--------------------

.. include:: ../build/docs/cli_options.rst

