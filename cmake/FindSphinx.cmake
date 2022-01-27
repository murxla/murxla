###
# Murxla: A Model-Based API Fuzzer for SMT solvers.
#
# This file is part of Murxla.
#
# Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
#
# See LICENSE for more information on using this software.
##
##
# Find Sphinx

find_program(SPHINX_EXECUTABLE
             NAMES sphinx-build
             DOC "Path to sphinx-build executable")
include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Sphinx DEFAULT_MSG SPHINX_EXECUTABLE)
