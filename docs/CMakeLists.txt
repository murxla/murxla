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

add_subdirectory(doxygen)

configure_file(conf.py.in ${CMAKE_CURRENT_BINARY_DIR}/conf.py)

add_custom_target(
  docs
  DEPENDS docs-doxygen murxla
  COMMAND
    ${SPHINX_EXECUTABLE} -v -b html -c ${CMAKE_CURRENT_BINARY_DIR}
    # Tell Breathe where to find the Doxygen output
    -Dbreathe_projects.Murxla=${DOXYGEN_XML_DIR}
    -Dbreathe_projects.std=${DOXYGEN_XML_DIR} ${SPHINX_INPUT_DIR}
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

set(SPHINX_GH_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/sphinx-gh)
add_custom_target(docs-gh ALL
                  DEPENDS docs
                  COMMAND ${CMAKE_COMMAND} -E remove_directory
                    ${SPHINX_GH_OUTPUT_DIR}
                  COMMAND ${CMAKE_COMMAND} -E copy_directory
                    ${SPHINX_OUTPUT_DIR} ${SPHINX_GH_OUTPUT_DIR}
                  COMMAND ${CMAKE_COMMAND} -E remove_directory
                    ${SPHINX_GH_OUTPUT_DIR}/_sources
                  COMMAND ${CMAKE_COMMAND} -E remove
                    ${SPHINX_GH_OUTPUT_DIR}/objects.inv
                  COMMAND ${CMAKE_COMMAND} -E rename
                    ${SPHINX_GH_OUTPUT_DIR}/_static
                    ${SPHINX_GH_OUTPUT_DIR}/static
                  COMMAND find ${SPHINX_GH_OUTPUT_DIR} -type f |
                    xargs sed -i'orig' 's/_static/static/g'
                  COMMAND ${CMAKE_COMMAND} -E rename
                    ${SPHINX_GH_OUTPUT_DIR}/_images
                    ${SPHINX_GH_OUTPUT_DIR}/images
                  COMMAND find ${SPHINX_GH_OUTPUT_DIR} -type f |
                    xargs sed -i'orig' 's/_images/images/g'
                  COMMAND find ${SPHINX_GH_OUTPUT_DIR} -name '*orig' -delete
                  COMMENT "Generating GitHub Api docs")

add_custom_command(
  TARGET docs-gh
  POST_BUILD
  COMMAND
    ${CMAKE_COMMAND} -E cmake_echo_color --cyan "Preview GH docs in browser: file://localhost${SPHINX_GH_OUTPUT_DIR}/index.html"
)

