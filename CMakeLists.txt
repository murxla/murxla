cmake_minimum_required(VERSION 3.3)

#-----------------------------------------------------------------------------#

project(smtmbt)

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 14)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

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

list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps")
find_package(Boolector)
find_package(CVC4)

add_subdirectory(src)
