FSM: Actions
============

.. contents::
  :local:

An action defines a specific interaction with the solver under test.
The actual interaction with the solver happens via one or more calls to the
API of the :ref:`solver wrapper <solver-wrappers>`.

Actions perform **three tasks**:

(1) randomly **generating** API call arguments
    (implemented in :cpp:func:`murxla::Action::generate()`)
(2) **executing** solver wrapper API calls with the generated set of arguments
    while tracing this execution (implemented in member function ``run()`` of
    an action)
(3) **replaying** the trace of an action (implemented in
    :cpp:func:`murxla::Action::untrace()`)


As a **convention**, an action derived from :cpp:class:`murxla::Action`

- defines its identifier as a public static member `s_name` of type
  :cpp:type:`murxla::Action::Kind`, which is then used for
  :cpp:member:`murxla::Action::d_kind`
- split out the actual execution of the solver wrapper API calls into a member
  function ``run()`` to ensure that :cpp:func:`murxla::Action::generate()`
  and :cpp:func:`murxla::Action::untrace()` execute an action in the same way

.. note::
   Solver-specific actions derived from :cpp:class:`murxla::Action` access
   the API of the solver under test directly, without going through the
   solver wrapper API.


The Base Class for Actions
--------------------------

.. doxygenclass:: murxla::Action
    :members:
    :undoc-members:

The Base Set of Actions
-----------------------

.. doxygenclass:: murxla::ActionNew
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionDelete
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionSetLogic
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionSetOption
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionSetOptionReq
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkSort
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkTerm
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkConst
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkFun
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkVar
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkValue
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionMkSpecialValue
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionInstantiateSort
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionAssertFormula
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionCheckSat
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionCheckSatAssuming
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionGetUnsatAssumptions
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionGetUnsatCore
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionGetValue
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionPush
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionPop
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionReset
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionResetAssertions
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionPrintModel
    :members:
    :undoc-members:

.. doxygenclass:: murxla::ActionTermGetChildren
    :members:
    :undoc-members:
