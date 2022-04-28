Term
====

Murxla defines type
:cpp:type:`Term<murxla::Term>`
for term representations
as an alias of shared pointer
(`std::shared_ptr <https://en.cppreference.com/w/cpp/memory/shared_ptr>`_)
to :cpp:class:`AbsTerm<murxla::AbsTerm>`.
We only deal with :cpp:type:`Term<murxla::Term>` objects in Murxla core
components and at the interface between Murxla and the solver wrapper.

.. doxygentypedef:: murxla::Term

.. doxygenfunction:: murxla::operator==(const Term& a, const Term& b)
.. doxygenfunction:: murxla::operator!=(const Term& a, const Term& b)
.. doxygenfunction:: murxla::operator<<(std::ostream& out, const Term t)
.. doxygenfunction:: murxla::operator<<(std::ostream& out, const std::vector<Term>& vector)
