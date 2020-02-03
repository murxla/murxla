set(smtmbt_src_files
  btor_solver.cpp
  cvc4_solver.cpp
  fsm.cpp
  main.cpp
  op.cpp
  solver.cpp
  solver_manager.cpp
  solver_option.cpp
  sort.cpp
  theory.cpp
  util.cpp
)

add_executable(smtmbt ${smtmbt_src_files})

if(Boolector_FOUND)
  target_link_libraries(smtmbt Boolector::boolector)
  target_compile_definitions(smtmbt PUBLIC SMTMBT_USE_BOOLECTOR)

  add_executable(genbtoropt btor/gen_btor_options.cpp)
  target_link_libraries(genbtoropt Boolector::boolector)
endif()

if(CVC4_FOUND)
  target_link_libraries(smtmbt CVC4::cvc4)
  target_compile_definitions(smtmbt PUBLIC SMTMBT_USE_CVC4)
endif()

if(toml11_FOUND)
  target_link_libraries(smtmbt toml11::toml11)
  target_compile_definitions(smtmbt PUBLIC HAVE_TOML11)
endif()
