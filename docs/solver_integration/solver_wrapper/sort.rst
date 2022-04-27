Sort
====

Murxla defines type
:cpp:type:`Sort<murxla::Sort>`
for sort representations
as an alias of shared pointer
(`std::shared_ptr <https://en.cppreference.com/w/cpp/memory/shared_ptr>`_)
to :cpp:class:`AbsSort<murxla::AbsSort>`.
We only deal with :cpp:type:`Sort<murxla::Sort>` objects in Murxla core
components and at the interface between Murxla and the solver wrapper.

.. doxygentypedef:: murxla::Sort

.. doxygenfunction:: murxla::operator==(const Sort& a, const Sort& b)
.. doxygenfunction:: murxla::operator!=(const Sort& a, const Sort& b)
.. doxygenfunction:: murxla::operator<<(std::ostream& out, const Sort s)
.. doxygenfunction:: murxla::operator<<(std::ostream& out, const std::vector<Sort>& vector)
