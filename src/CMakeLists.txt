set(smtmbt_src_files
  main.cpp
)

add_executable(smtmbt ${smtmbt_src_files})
set_target_properties(smtmbt
  PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
