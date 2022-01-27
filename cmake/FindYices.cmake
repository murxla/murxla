###
# Murxla: A Model-Based API Fuzzer for SMT solvers.
#
# This file is part of Murxla.
#
# Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
#
# See LICENSE for more information on using this software.
##
# Find Yices
# Yices_FOUND - found Yices lib
# Yices_INCLUDE_DIR - the Yices include directory
# Yices_LIBRARIES - Libraries needed to use Yices

find_path(Yices_INCLUDE_DIR NAMES yices.h)
find_library(Yices_LIBRARIES NAMES yices)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Yices
  DEFAULT_MSG Yices_INCLUDE_DIR Yices_LIBRARIES)

mark_as_advanced(Yices_INCLUDE_DIR Yices_LIBRARIES)
if(Yices_LIBRARIES)
  message(STATUS "Found Yices library: ${Yices_LIBRARIES}")
endif()
