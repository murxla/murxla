User Guide
==========

This guide covers the most common usage scenarios of Murxla.

Testing an SMT Solver
---------------------

Murxla provides a **continuous** and **one-shot** mode for testing an SMT solver.
In the continuous mode, Murxla will continuously fuzz test a solver until Murxla
is interrupted or a specified maximum number of test runs were performed
(option ``-m``).
This mode is usually used to find solver errors.

In the one-shot mode, Murxla will perform one test run given a specific seed
for Murxla's random number generator (option ``-s``) or an API trace (option
``-u``).
This mode is usually used to inspect a specific test run in more detail, .e.g,
for debugging purposes.

Testing an Integrated Solver
****************************

Fuzz testing a solver natively supported by Murxla only requires to enable
the solver via the corresponding solver option.
For example, testing Bitwuzla is done as follows.

.. code-block:: bash

   $ murxla --bzla


In continuous mode, Murxla prints overall **fuzzing statistics** while running.
``seed`` refers to the random number generator seed that produced the run,
``runs`` corresponds to the total number of runs so far,
``r/s`` is the run throughput per second,
``sat``, ``unsat``, ``unknw`` are the numbers of sat/unsat/unknown answers of the
solver, while ``to`` and ``err`` refer to the number of timeouts and issues
encountered so far.

Each time Murxla encounters a **timeout** it will print the seed of the
instance.
When an **issue** is encountered, it will also print the name of the recorded
trace as well as the error message of the solver.
Murxla groups error traces that trigger the same error message into
subdirectories (1, 2, ...) and stores the corresponding error message in
in a file called ``error.txt``.

Murxla stores all generated API traces (and subdirectories) in the current
working directory.
It is recommended to use option ``-O <dir>`` to specify an output directory to
store all these files and directories in ``<dir>`` in order to separate them
from previous Murxla runs.


.. code-block:: none
   :caption: Example: Murxla continuous mode output

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

   The default time limit per run is 1 second and can be changed with option
   ``-t``.

.. note::

   The above seeds may not produce the same API traces on different machines
   due to different library versions installed on a system.
   However, replaying a trace on a different machine will trigger the original
   behavior.


Testing via the SMT2-LIB Interface
**********************************

If an SMT solver is not natively integrated into Murxla, the solver binary can
still be tested via Murxla's interactive SMT-LIBv2 interface.
In this mode, Murxla will randomly generate SMT-LIBv2 compliant problems with
all SMT-LIBv2 theories enabled.
If the solver under test does not support specific theories or operators, the
default SMT-LIBv2 profile can be overridden with a custom
:ref:`solver profile <solver-profiles>`,
which can be loaded via option ``-p``.

.. todo:: example call with solver

Replaying and Minimizing Traces
-------------------------------

Murxla generates API trace files if an issue is encountered.
Replaying a trace file with Murxla executes the exact same API call sequence
that was executed when recording the trace and will trigger the same error
behavior.

In the above example,
seed ``2287b2bd77a3b84c`` triggered an issue in Bitwuzla.
Murxla stores the API trace
in ``1/murxla-2287b2bd77a3b84c.trace``, which can be replayed as follows.

.. code-block:: trace
   :caption: Example: Replaying API Traces

   $ murxla -u 1/murxla-2287b2bd77a3b84c.trace

     set-murxla-options --bzla
    1174 new
   97715 set-logic QF_UFBVFP
   15569 set-option produce-models true
   14778 set-option incremental true
   60732 set-option produce-unsat-assumptions false
    3698 set-option produce-unsat-cores true
   34675 mk-sort SORT_FP 15 113
         return s1
   34675 mk-sort SORT_BV 1
         return s2
   34675 mk-sort SORT_BV 15
         return s3

   ... (cut) ...

   32294 mk-term OP_FP_EQ SORT_BOOL 2 t191 t155
         return t198 s8
   33829 check-sat
    9200 get-value 5 t197 t24 t198 t147 t163
   99576 bzla-get-fun-value t174
   [bzlachkmodel] bzla_check_model: invalid model




Minimizing Traces
*****************

Murxla provides a trace minimizer that takes an API trace and tries to minimize
it while preserving the behavior of the original execution.

The trace minimizer implements simple minimization techniques in the following
three phases:

1. line-based minimization to reduce the number of trace lines
2. minimization of action lines to reduce the number of arguments
3. term substitution, where terms are replaced with simpler terms of the same
   sort

For example, API trace ``1/murxla-2287b2bd77a3b84c.trace`` has 602 lines and
can be minimized with option ``-d`` as follows.

.. code-block:: none
   :caption: Example: Minimizing API Traces

   $ murxla -u 1/murxla-2287b2bd77a3b84c.trace -d

   [murxla] dd: minimizing untraced file '1/murxla-2287b2bd77a3b84c.trace'
   [murxla] dd: start minimizing file '/tmp/murxla-63714/tmp.trace'
   [murxla] dd: golden exit: error
   [murxla] dd: golden stdout output:
   [murxla] dd: golden stderr output: [bzlachkmodel] bzla_check_model: invalid model

   [murxla] dd: trying to minimize number of trace lines ...
   [murxla] dd: >> number of lines reduced to 92.21% of original number
   [murxla] dd: >> number of lines reduced to 74.77% of original number
   [murxla] dd: >> number of lines reduced to 31.15% of original number
   [murxla] dd: trying to minimize trace lines ...

   ... (cut) ...

   [murxla] dd: trying to minimize number of trace lines ...
   [murxla] dd:
   [murxla] dd: 276 (of 1491) tests reduced successfully
   [murxla] dd: written to: 1/murxla-2287b2bd77a3b84c.min.trace
   [murxla] dd: file reduced to 7.50% of original size

The minimized trace is 7.5% of the original trace (59 lines) but still triggers
the original erroneous behavior.
If the minimized API trace does not contain any solver-specific extensions
it can usually be translated to SMT-LIB via option ``--smt2`` (without a
binary), which can then often be further reduced using a delta-debugging tool
such as `ddSMT <https://github.com/ddsmt/ddsmt>`_.




Advanced Usage Scenarios
------------------------

Cross-Checking Solvers
**********************

Murxla's cross-checking feature (option ``-c``) can be used to find problems on
which two solvers disagree.
It compares the results of two solvers after each ``(check-sat)`` or
``(check-sat-assuming)`` call and reports an error if the two solvers disagree.



.. code-block:: bash
   :caption: Cross-checking Bitwuzla against cvc5

   murxla --bzla -c cvc5




Murxla also allows to cross-check solver binaries used via the
SMT-LIBv2 interface against the native solvers.

.. code-block:: bash
   :caption: Cross-checking a z3 binary via the SMT-LIB interface against cvc5

   murxla --smt2 z3 -c cvc5


Command Line Options
--------------------

.. include:: ../build/docs/cli_options.rst

