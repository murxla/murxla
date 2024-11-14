Pre-Defined Operator Kinds
==========================

The list of operator kinds globally defined in :cpp:class:`murxla::Op`.

.. It would be better to define this list as a group in the c++ code and
   display with doxygengroup. However, \addtogroup in the c++ code to define a
   group as a subsection of a class/struct breaks listing classes/structs via
   the doxygenclass directive of Breathe. That's why list these explicitly here.

Internal Kinds
--------------

.. doxygengroup:: op-kinds-internal
   :content-only:

Leaf Kinds
----------

.. note:: These kinds are only needed for :cpp:function:`murxla::Term::get_kind()`.

.. doxygengroup:: op-kinds-leafs
   :content-only:

Special Cases
-------------

.. doxygengroup:: op-kinds-special-cases
   :content-only:

Arrays
------

.. doxygengroup:: op-kinds-arrays
   :content-only:

Boolean
-------

.. doxygengroup:: op-kinds-boolean
   :content-only:

Bit-Vectors
-----------

.. doxygengroup:: op-kinds-bv
   :content-only:

Datatypes
---------

.. doxygengroup:: op-kinds-dt
   :content-only:

Finite Fields
-------------

.. doxygengroup:: op-kinds-ff
   :content-only:

Floating-Point Arithmetic
-------------------------

.. doxygengroup:: op-kinds-fp
   :content-only:

Integers
--------

.. doxygengroup:: op-kinds-ints
   :content-only:

Reals
-----

.. doxygengroup:: op-kinds-reals
   :content-only:

Quantifiers
-----------

.. doxygengroup:: op-kinds-quants
   :content-only:

Strings
-------

.. doxygengroup:: op-kinds-strings
   :content-only:

Transcendentals
---------------

.. doxygengroup:: op-kinds-trans
   :content-only:

Uninterpreted Functions
-----------------------

.. doxygengroup:: op-kinds-uf
   :content-only:

Operators of Non-Standardized Theories
--------------------------------------

Bags
....

.. doxygengroup:: op-kinds-bags
   :content-only:

Sequences
.........

.. doxygengroup:: op-kinds-seq
   :content-only:

Sets
....

.. doxygengroup:: op-kinds-sets
   :content-only:

Relations
.........

.. doxygengroup:: op-kinds-rels
   :content-only:
