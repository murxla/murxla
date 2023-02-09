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
  solver/bitwuzla/bitwuzla_solver.cpp
  solver/cvc5/cvc5_solver.cpp
  solver/cvc5/cvc5_tracer.cpp
  solver/yices/yices_solver.cpp
  solver/smt2/smt2_solver.cpp
  solver/meta/check_solver.cpp
  solver/meta/shadow_solver.cpp
  solver/solver_profile.cpp
)

# Setup JSON library
include(${PROJECT_SOURCE_DIR}/cmake/json.cmake)

add_executable(murxla ${murxla_src_files})
target_include_directories(murxla PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(murxla PRIVATE nlohmann_json::nlohmann_json)

if(GCOV)
  target_compile_definitions(murxla PUBLIC MURXLA_COVERAGE)
endif()

if (NOT APPLE)
  include(CheckIncludeFileCXX)
  # Workaround to support compilation with gcc7.
  check_include_file_cxx(<filesystem> HAVE_FILESYSTEM_INCLUDE)
  if(NOT HAVE_FILESYSTEM_INCLUDE)
    target_link_libraries(murxla PRIVATE stdc++fs)
  endif()
endif()

if(Boolector_FOUND)
  target_link_libraries(murxla PRIVATE Boolector::boolector)
  target_compile_definitions(murxla PUBLIC MURXLA_USE_BOOLECTOR)
endif()

if(Bitwuzla_FOUND)
  target_link_libraries(murxla PRIVATE Bitwuzla::bitwuzla)
  target_compile_definitions(murxla PUBLIC MURXLA_USE_BITWUZLA)
endif()

if(cvc5_FOUND)
  target_link_libraries(murxla PRIVATE cvc5::cvc5)
  target_compile_definitions(murxla PUBLIC MURXLA_USE_CVC5)
endif()

if (Yices_FOUND)
  target_include_directories(murxla PRIVATE ${Yices_INCLUDE_DIR})
  target_link_libraries(murxla PRIVATE ${Yices_LIBRARIES})
  target_compile_definitions(murxla PUBLIC MURXLA_USE_YICES)
endif()

# Generate solver profile headers
file(GENERATE
  OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/gen_profile.cmake"
  CONTENT [[
file(READ ${PROFILE_INPUT_FILE} JSON)
set(PROFILE "\
#include <string>\n\
namespace murxla {\n\
namespace ${SOLVER} {\n\
  static const std::string s_profile=R\"(${JSON})\";\n\
}\n}\n")
file(WRITE "${PROFILE_OUTPUT_FILE}" "${PROFILE}")]]
)

foreach(solver btor bitwuzla cvc5 yices smt2)
  set(JSON_FILE
      "${CMAKE_CURRENT_SOURCE_DIR}/solver/${solver}/profile.json")
  set(PROFILE_HEADER_FILE
      "${CMAKE_CURRENT_BINARY_DIR}/solver/${solver}/profile.hpp")

  add_custom_command(
    OUTPUT ${PROFILE_HEADER_FILE}
    COMMAND
      ${CMAKE_COMMAND}
        -DSOLVER="${solver}"
        -DPROFILE_INPUT_FILE="${JSON_FILE}"
        -DPROFILE_OUTPUT_FILE="${PROFILE_HEADER_FILE}"
        -P gen_profile.cmake
    DEPENDS ${JSON_FILE} gen_profile.cmake
  )
  add_custom_target(gen-profile-${solver} DEPENDS ${PROFILE_HEADER_FILE})
  add_dependencies(murxla gen-profile-${solver})
endforeach()
target_include_directories(murxla PRIVATE ${CMAKE_CURRENT_BINARY_DIR})
