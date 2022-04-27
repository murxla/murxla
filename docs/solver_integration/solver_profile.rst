Solver Profiles
###############

A solver profile is a JSON file ``profile.json`` located in the solver
directory
(e.g., `src/solver/cvc5/profile.json <https://github.com/murxla/murxla/blob/main/src/solver/cvc5/profile.json>`_)
and allows to arbitrarily configure how and what should be tested.
The profile file defines what is supported by the solver and therefore each
solver must provide a profile.

Murxla recognizes a set of *predefined* JSON keys as described below, which will
affect how Murxla generates API calls. The solver profile JSON file can be
arbitrarily extended with *solver-specific* keys.

The predefined keys allow to define which theories to include, and optionally
restrict sort and operator kinds.
They further allow defining restrictions for unsupported features
(or to configure a specific test environment, e.g., for fragments of a
theory),
skipping issues based on output patterns (useful for false positives that
require an unreasonable amount of implementation effort to be avoided),
and explicitly filtering for specific issues.



**Predefined keys used by Murxla:**
  - ``theories`` (`<Theory Restrictions_>`_)
  - ``sorts`` (`<Sort Restrictions_>`_)
  - ``operators`` (`<Operator Restrictions_>`_)
  - ``errors`` (`<Filtering Errors_>`_)

In the following, ``<THEORY>`` refers to theories defined in
:cpp:enum:`murxla::Theory`,
``<SORT>`` refers to any sort kind :cpp:enum:`murxla::SortKind`,
and ``<OP>`` refers to any operator :cpp:type:`murxla::Op::Kind`.

Theory Restrictions
*******************

The ``theories`` key restricts how Murxla enables/disables theories.

**Available keys:**
  - ``include``: List of supported theories. (see :cpp:enum:`murxla::Theory`)
  - ``exclude-combinations``: Dictionary of unsupported theory combinations.

Supported Theories (required)
=============================

A profile is required to define the list of theories supported by a solver.
This will configure Murxla to use all sorts and operators associated with a
theory in this list. The use of sorts and operators can be further restricted
as described below
(`sorts <Sort Restrictions_>`_, `operators <Operator Restrictions_>`_).

.. code-block:: JSON

  {
    "theories": {
      "include": [
        "<THEORY>", "..."
      ]
    }
  }

.. note::
   - The `include` attribute is a required attribute for `theories`.
   - Any theory from :cpp:enum:`murxla::Theory` can be included except
     `THEORY_ALL`.
   - `THEORY_BOOL` is always implicitly included.


Excluding Theory Combinations
=============================

If a solver does not support certain combinations of theories they can be
excluded as follow.

.. code-block:: JSON

  {
    "theories": {
      "exclude-combinations": {
        "<THEORY>": [
          "<THEORY>", "..."
        ]
      }
    }
  }

For example, to configure Murxla to not use quantifiers in combination with
arrays or uninterpreted functions use:

.. code-block:: JSON

  {
    "theories": {
      "exclude-combinations": {
        "THEORY_QUANT": [
          "THEORY_ARRAY",
          "THEORY_UF"
        ]
      }
    }
  }


Sort Restrictions
*****************

**Available keys:**
  - ``exclude``: List of sort kinds to exclude.
  - ``array-index``: Array index sort restrictions.
  - ``array-element``: Array element sort restrictions.
  - ``bag-element``: Bag element sort restrictions.
  - ``datatype-match``: Datatype match construct sort restrictions.
  - ``datatype-selector-codomain``: Datatype selector codomain sort restrictions.
  - ``fun-domain``: Domain sort restrictions when creating functions
    (``define-fun`` in SMT-LIBv2, :cpp:class:`murxla::ActionMkFun`).
  - ``fun-codomain``: Codomain sort restrictions when creating functions
    (``define-fun`` in SMT-LIBv2, :cpp:class:`murxla::ActionMkFun`).
  - ``fun-sort-domain``: Domain sort restrictions when creating function sorts.
  - ``fun-sort-codomain``: Codomain sort restrictions when creating function
    sorts.
  - ``get-value``: Sort restrictions on terms for querying model values
    (``get-value`` in SMT-LIBv2, :cpp:class:`murxla::ActionGetValue`).
  - ``seq-element``: Sequence element sort restrictions.
  - ``set-element``: Set element sort restrictions.
  - ``sort-param``: Sort restrictions on parameters of parametric sorts.
  - ``var``: Variable sort restrictions.

The list of available sort kinds can be found here:
:cpp:enum:`murxla::SortKind`.

Excluding Sort Kinds
====================

In special cases a solver may not support not all sort kinds associated to a
theory. For example, a solver may support `THEORY_UF`, but does not supported
uninterpreted sorts. For these cases Murxla can be instructed to not create
uninterpreted sorts as follows.

.. code-block:: JSON

  {
    "sorts": {
      "exclude": [
        "<SORT>", "..."
      ]
    }
  }

.. note::
   Disabling a sort kind will also disable all operators that require terms of
   that sort kind.


For all other keys ``<KEY>`` listed above sort restrictions can be defined as
follows.

.. code-block:: JSON

  {
    "sorts": {
      "<KEY>": {
        "exclude": [
          "<SORT>", "..."
        ]
      }
    }
  }



Operator Restrictions
*********************

**Available keys:**
  - ``exclude``: List of operators. (see :cpp:type:`murxla::Op::Kind`)
  - ``sort-restrictions``: Dictionary of operators to sort kinds (only useful
    for restricting sorts for operators with sort kind ``SORT_ANY``).


Certain operators can be disabled as follows.

.. code-block:: JSON

  {
    "operators": {
      "exclude": [
        "<OP>", "..."
      ]
    }
  }

Some operators in Murxla have arguments of sort kind ``SORT_ANY``
(e.g., ``Op::EQUAL``, ``Op::DISTINCT``).
Further restricting the sorts of the operator's arguments can be done as
follows.

.. code-block:: JSON

  {
    "operators": {
      "sort-restrictions": {
        "<OP>": [
          "<SORT>", "..."
        ]
      }
    }
  }


Filtering Errors
****************

Error messages can be filtered out as follows.

.. code-block:: JSON

  {
     "errors": {
      "exclude": [
        "foo",
        "bar"
      ]
    }
  }

This will ignore all triggered error messages containing ``foo`` or ``bar``.


Customizing Solver Profiles
***************************

Murxla provides option ``-p <JSON>`` (``--profile <JSON>``) to customize
the default solver profile.
If this options is used the specified profile will be merged with the default
solver profile, i.e., it takes the union of all ``exclude`` keys and the
intersection of all ``include`` keys.


Default Profiles of Supported Solvers
*************************************

.. tabs::

   .. tab:: Bitwuzla

      `src/solver/bzla/profile.json <https://github.com/murxla/murxla/blob/main/src/solver/bzla/profile.json>`_

      .. literalinclude:: ../../src/solver/bzla/profile.json
         :language: JSON

   .. tab:: Boolector

      `src/solver/btor/profile.json <https://github.com/murxla/murxla/blob/main/src/solver/btor/profile.json>`_

      .. literalinclude:: ../../src/solver/btor/profile.json
         :language: JSON

   .. tab:: cvc5

      `src/solver/cvc5/profile.json <https://github.com/murxla/murxla/blob/main/src/solver/cvc5/profile.json>`_

      .. literalinclude:: ../../src/solver/cvc5/profile.json
         :language: JSON

   .. tab:: Yices

      `src/solver/yices/profile.json <https://github.com/murxla/murxla/blob/main/src/solver/yices/profile.json>`_

      .. literalinclude:: ../../src/solver/yices/profile.json
         :language: JSON

   .. tab:: SMT2 Solver

      `src/solver/smt2/profile.json <https://github.com/murxla/murxla/blob/main/src/solver/smt2/profile.json>`_

      .. literalinclude:: ../../src/solver/smt2/profile.json
         :language: JSON
