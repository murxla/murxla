###
# Murxla: A Model-Based API Fuzzer for SMT solvers.
#
# This file is part of Murxla.
#
# Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
#
# See LICENSE for more information on using this software.
##

set(murxla_src_files
  action.cpp
  dd.cpp
  except.cpp
  fsm.cpp
  main.cpp
  murxla.cpp
  op.cpp
  result.cpp
  rng.cpp
  solver_manager.cpp
  solver_option.cpp
  sort.cpp
  statistics.cpp
  term_db.cpp
  theory.cpp
  util.cpp
  solver/solver.cpp
  solver/btor/btor_solver.cpp
  solver/bzla/bzla_solver.cpp
  solver/cvc5/cvc5_solver.cpp
  solver/yices/yices_solver.cpp
  solver/smt2/smt2_solver.cpp
  solver/meta/check_solver.cpp
  solver/meta/shadow_solver.cpp
)

add_executable(murxla ${murxla_src_files})
target_include_directories(murxla PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})

if(GCOV)
  target_compile_definitions(murxla PUBLIC MURXLA_COVERAGE)
endif()

include(CheckIncludeFileCXX)
# Workaround to support compilation with gcc7.
check_include_file_cxx(<filesystem> HAVE_FILESYSTEM_INCLUDE)
if(NOT HAVE_FILESYSTEM_INCLUDE)
  target_link_libraries(murxla stdc++fs)
endif()

if(Boolector_FOUND)
  target_link_libraries(murxla Boolector::boolector)
  target_compile_definitions(murxla PUBLIC MURXLA_USE_BOOLECTOR)
endif()

if(Bitwuzla_FOUND)
  target_link_libraries(murxla Bitwuzla::bitwuzla)
  target_compile_definitions(murxla PUBLIC MURXLA_USE_BITWUZLA)
  # TODO: Bitwuzla options
endif()

if(cvc5_FOUND)
  target_link_libraries(murxla cvc5::cvc5)
  target_compile_definitions(murxla PUBLIC MURXLA_USE_CVC5)
endif()

if (Yices_FOUND)
  target_include_directories(murxla PRIVATE ${Yices_INCLUDE_DIR})
  target_link_libraries(murxla ${Yices_LIBRARIES})
  target_compile_definitions(murxla PUBLIC MURXLA_USE_YICES)
  # TODO: Yices options
endif()
