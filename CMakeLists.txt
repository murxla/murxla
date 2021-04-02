cmake_minimum_required(VERSION 3.3)

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

#if(ASAN)
  # -fsanitize=address requires CMAKE_REQUIRED_FLAGS to be explicitely set,
  # otherwise the -fsanitize=address check will fail while linking.
  set(CMAKE_REQUIRED_FLAGS -fsanitize=address)
  add_required_cxx_flag("-fsanitize=address")
  unset(CMAKE_REQUIRED_FLAGS)
  add_check_cxx_flag("-fno-omit-frame-pointer")
  add_required_cxx_flag("-fsanitize-recover=address")
#endif()

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

list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps")
find_package(Boolector)
find_package(Bitwuzla)
find_package(CVC4)
find_package(toml11)
find_package(Yices)

add_subdirectory(src)

