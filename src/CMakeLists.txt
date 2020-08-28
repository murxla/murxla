set(smtmbt_src_files
  btor_solver.cpp
  cvc4_solver.cpp
  fsm.cpp
  main.cpp
  op.cpp
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

  if(toml11_FOUND)
    add_executable(gencvc4options cvc4/gen_cvc4_options.cpp)
    target_link_libraries(gencvc4options toml11::toml11)
  endif()
endif()

if(toml11_FOUND)
  target_link_libraries(smtmbt toml11::toml11)
  target_compile_definitions(smtmbt PUBLIC HAVE_TOML11)
endif()

if (Yices_FOUND)
  target_include_directories(smtmbt PRIVATE ${Yices_INCLUDE_DIR})
  target_link_libraries(smtmbt ${Yices_LIBRARIES})
  target_compile_definitions(smtmbt PUBLIC SMTMBT_USE_YICES)
  # TODO: Yices options
endif()
