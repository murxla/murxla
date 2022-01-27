###
# Murxla: A Model-Based API Fuzzer for SMT solvers.
#
# This file is part of Murxla.
#
# Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
#
# See LICENSE for more information on using this software.
##
find_package(Sphinx REQUIRED)
check_python_module(breathe)

set(SPHINX_INPUT_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set(SPHINX_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/sphinx)

add_subdirectory(solver)

configure_file(conf.py.in ${CMAKE_CURRENT_BINARY_DIR}/conf.py)

add_custom_target(
  docs
  DEPENDS docs-doxygen murxla
  COMMAND
    ${SPHINX_EXECUTABLE} -v -b html -c ${CMAKE_CURRENT_BINARY_DIR}
    # Tell Breathe where to find the Doxygen output
    -Dbreathe_projects.cvc5=${CPP_DOXYGEN_XML_DIR}
    -Dbreathe_projects.std=${CPP_DOXYGEN_XML_DIR} ${SPHINX_INPUT_DIR}
    ${SPHINX_OUTPUT_DIR}
  WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
  COMMENT "Generating docs"
)

add_custom_command(
  TARGET docs
  POST_BUILD
  COMMAND
    ${CMAKE_COMMAND} -E cmake_echo_color --cyan "Preview docs in browser: file://localhost${SPHINX_OUTPUT_DIR}/index.html"
)
