###
# Murxla: A Model-Based API Fuzzer for SMT solvers.
#
# This file is part of Murxla.
#
# Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
#
# See LICENSE for more information on using this software.
##
include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

# Add a CXX flag to the global list of CXX flags.
macro(add_cxx_flag flag)
  if(CMAKE_CXX_FLAGS)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
  else()
    set(CMAKE_CXX_FLAGS "${flag}")
  endif()
  message(STATUS "Configuring with CXX flag '${flag}'")
endmacro()

# Check if CXX flag is supported and add to global list of CXX flags.
macro(add_check_cxx_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_cxx_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if(HAVE_FLAG${flagname})
    add_cxx_flag(${flag})
  endif()
endmacro()

# Add required CXX flag. Configuration fails if the CXX flag is not supported
# by the compiler.
macro(add_required_cxx_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagnamename ${flag})
  check_cxx_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if (NOT HAVE_FLAG${flagname})
    message(FATAL_ERROR "Required compiler flag ${flag} not supported")
  endif()
  add_cxx_flag(${flag})
endmacro()

# Check if given Python module is installed and raises a FATAL_ERROR error
# if the module cannot be found.
function(check_python_module module)
  execute_process(
    COMMAND
    ${PYTHON_EXECUTABLE} -c "import ${module}"
    RESULT_VARIABLE
      RET_MODULE_TEST
    ERROR_QUIET
  )
  set(module_name ${ARGN})
  if(NOT module_name)
    set(module_name ${module})
  endif()

  if(RET_MODULE_TEST)
    message(FATAL_ERROR
        "Could not find module ${module_name} for Python "
        "version ${PYTHON_VERSION_MAJOR}.${PYTHON_VERSION_MINOR}. "
        "Make sure to install ${module_name} for this Python version "
        "via \n`${PYTHON_EXECUTABLE} -m pip install ${module_name}'.\n"
        "Note: You need to have pip installed for this Python version.")
  endif()
endfunction()
