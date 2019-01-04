set(smtmbt_src_files
  btor_solver_manager.cpp
  cvc4_solver_manager.cpp
  fsm.cpp
  main.cpp
)

add_executable(smtmbt ${smtmbt_src_files})

if(Boolector_FOUND)
  set(THREADS_PREFER_PTHREAD_FLAG ON)
  find_package(Threads REQUIRED)
  if(THREADS_HAVE_PTHREAD_ARG)
    add_check_cxx_flag(-pthread)
  endif()
  target_link_libraries(smtmbt ${Boolector_LIBRARIES})
  target_include_directories(smtmbt PRIVATE ${Boolector_INCLUDE_DIR})
  target_compile_definitions(smtmbt PUBLIC SMTMBT_USE_BOOLECTOR)
endif()

if(CVC4_FOUND)
  target_link_libraries(smtmbt ${CVC4_LIBRARIES})
  target_include_directories(smtmbt PRIVATE ${CVC4_INCLUDE_DIR})
  target_compile_definitions(smtmbt PUBLIC SMTMBT_USE_CVC4)
endif()

set_target_properties(smtmbt
  PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
