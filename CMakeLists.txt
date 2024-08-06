###
# Murxla: A Model-Based API Fuzzer for SMT solvers.
#
# This file is part of Murxla.
#
# Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
#
# See LICENSE for more information on using this software.
##
cmake_minimum_required(VERSION 3.5)

#-----------------------------------------------------------------------------#

project(murxla)

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 17)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
message(STATUS "LIB directory is '${CMAKE_BINARY_DIR}/lib'")
message(STATUS "BIN directory is '${CMAKE_BINARY_DIR}/bin'")

include(Helpers)

#-----------------------------------------------------------------------------#

option(GCOV "enable code coverage" OFF)
option(ENABLE_BOOLECTOR "enable Boolector" ON)
option(ENABLE_BITWUZLA "enable Bitwuzla" ON)
option(ENABLE_CVC5 "enable cvc5" ON)
option(ENABLE_YICES "enable Yices" ON)
option(ASAN "compile with ASAN support" OFF)
option(DOCS "build documentation" OFF)

#-----------------------------------------------------------------------------#

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Debug)
endif()

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  add_required_cxx_flag("-g")
  add_check_cxx_flag("-g3")
  add_check_cxx_flag("-ggdb")
elseif (CMAKE_BUILD_TYPE STREQUAL "Release")
  add_check_cxx_flag("-O3")
endif()

add_check_cxx_flag("-Wall")
add_check_cxx_flag("-Wconversion")

if(ASAN)
  # -fsanitize=address requires CMAKE_REQUIRED_FLAGS to be explicitely set,
  # otherwise the -fsanitize=address check will fail while linking.
  set(CMAKE_REQUIRED_FLAGS -fsanitize=address)
  add_required_cxx_flag("-fsanitize=address")
  unset(CMAKE_REQUIRED_FLAGS)
  add_check_cxx_flag("-fno-omit-frame-pointer")
  add_required_cxx_flag("-fsanitize-recover=address")
endif()

#-----------------------------------------------------------------------------#

option(WITH_TESTS "Build with unit tests")
if(WITH_TESTS)
  include(cmake/googletest.cmake)
  fetch_googletest(
      ${PROJECT_SOURCE_DIR}/cmake
      ${PROJECT_BINARY_DIR}/googletest
      )
  enable_testing()
  add_subdirectory(test)
endif()

#-----------------------------------------------------------------------------#
# Find enabled dependencies

list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps")

link_directories(AFTER "${PROJECT_SOURCE_DIR}/deps/lib")

if(ENABLE_BOOLECTOR)
  find_package(Boolector QUIET)
endif()
if(ENABLE_BITWUZLA)
  include(FindPkgConfig)
  find_package(PkgConfig)
  if(PkgConfig_FOUND)
    pkg_check_modules(Bitwuzla IMPORTED_TARGET bitwuzla)
  endif()
endif()
if(ENABLE_CVC5)
  find_package(cvc5 QUIET)
endif()
if(ENABLE_YICES)
  find_package(Yices QUIET)
endif()

if(GCOV)
  include(CodeCoverage)
  append_coverage_compiler_flags()

  # Coverage report for solvers only
  setup_code_coverage_fastcov(
    NAME coverage
    PATH "${PROJECT_SOURCE_DIR}"
    EXCLUDE
      "${PROJECT_SOURCE_DIR}/deps"
      "${PROJECT_SOURCE_DIR}/src"
    DEPENDENCIES murxla)

  # Coverage report including murxla code base
  setup_code_coverage_fastcov(
    NAME coverage-all
    PATH "${PROJECT_SOURCE_DIR}"
    EXCLUDE
      "${PROJECT_SOURCE_DIR}/deps"
    DEPENDENCIES murxla)
endif()

#-----------------------------------------------------------------------------#
# Add subdirectories

add_subdirectory(src)

if(DOCS)
  find_package(PythonInterp 3 REQUIRED)
  add_subdirectory(docs)
endif()

print_config_value("Found Bitwuzla:   " Bitwuzla_FOUND)
print_config_value("Found Boolector:  " Boolector_FOUND)
print_config_value("Found cvc5:       " cvc5_FOUND)
print_config_value("Found Yices2:     " Yices_FOUND)
