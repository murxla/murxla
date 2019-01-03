cmake_minimum_required(VERSION 3.3)

#-----------------------------------------------------------------------------#

project(smtmbt)

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
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

#-----------------------------------------------------------------------------#

add_subdirectory(src)
