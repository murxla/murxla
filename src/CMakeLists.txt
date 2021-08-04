set(murxla_src_files
  action.cpp
  btor_solver.cpp
  bzla_solver.cpp
  cross_check_solver.cpp
  cvc5_solver.cpp
  except.cpp
  fsm.cpp
  main.cpp
  murxla.cpp
  op.cpp
  rng.cpp
  smt2_solver.cpp
  solver.cpp
  solver_manager.cpp
  solver_option.cpp
  sort.cpp
  statistics.cpp
  term_db.cpp
  theory.cpp
  util.cpp
  yices_solver.cpp
)

add_executable(murxla ${murxla_src_files})

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
