###
# Murxla: A Model-Based API Fuzzer for SMT solvers.
#
# This file is part of Murxla.
#
# Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
#
# See LICENSE for more information on using this software.
##
set(test_util_src_files
  ${PROJECT_SOURCE_DIR}/src/util.cpp
  test_util.cpp
)
add_executable (testutil ${test_util_src_files})
target_include_directories(testutil PRIVATE ${PROJECT_SOURCE_DIR}/src)
target_link_libraries(testutil gtest_main)
set_target_properties(testutil PROPERTIES OUTPUT_NAME testutil)
add_test(util ${CMAKE_BINARY_DIR}/bin/testutil)
