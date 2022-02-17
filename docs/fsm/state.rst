FSM: States
===========

.. contents::
  :local:

A state of the FSM corresponds to the current state of the solver under test.
Transitions from one state to another (or the same) state either have an
"action" (the execution of one or more solver API calls) associated,
or are "empty", i.e., do not execute any solver API calls.

Transitions are weighted, and their weight is defined via its *priority*,
where ``1`` is the highest priority, ``UINT32_MAX`` is the lowest priority,
and ``0`` disables the transition.
A transition with an associated action is defined by adding an
:cpp:class:`murxla::Action` to a state via
:cpp:func:`murxla::State::add_action()` while defining its priority and next
state.
Similarly, empty transitions are added as instances of
:cpp:class:`murxla::Transition`.

Each state of the FSM may provide a pre-condition for transitioning into
that state (:cpp:member:`murxla::State::f_precond`).
Use :cpp:func:`murxla::FSM::new_state()` to create and add new states to the
FSM.
To add solver-specific actions to a state, retrieve the state via
:cpp:func:`murxla::FSM::get_state()`.

State
-----

.. doxygenclass:: murxla::State
    :members:
    :undoc-members:
