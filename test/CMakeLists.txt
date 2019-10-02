set(test_src_files
  ${PROJECT_SOURCE_DIR}/src/util.cpp
  test_util.cpp
)
add_executable (testsmtmbt ${test_src_files})
target_include_directories(testsmtmbt PRIVATE ${PROJECT_SOURCE_DIR}/src)
target_link_libraries(testsmtmbt gtest_main)
set_target_properties(testsmtmbt PROPERTIES OUTPUT_NAME test)
add_test(unit ${CMAKE_BINARY_DIR}/bin/test)
