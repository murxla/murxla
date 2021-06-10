set(murxla_src_files
  btor_solver.cpp
  bzla_solver.cpp
  cvc4_solver.cpp
  except.cpp
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

add_executable(murxla ${murxla_src_files})

if(Boolector_FOUND)
  target_link_libraries(murxla Boolector::boolector)
  target_compile_definitions(murxla PUBLIC MURXLA_USE_BOOLECTOR)

  add_executable(genbtoropt btor/gen_btor_options.cpp)
  target_link_libraries(genbtoropt Boolector::boolector)
endif()

if(Bitwuzla_FOUND)
  target_link_libraries(murxla Bitwuzla::bitwuzla)
  target_compile_definitions(murxla PUBLIC MURXLA_USE_BITWUZLA)
  # TODO: Bitwuzla options
endif()

if(cvc5_FOUND)
  target_link_libraries(murxla cvc5::cvc5)
  target_compile_definitions(murxla PUBLIC MURXLA_USE_CVC5)

  if(toml11_FOUND)
    add_executable(gencvc4options cvc4/gen_cvc4_options.cpp)
    target_link_libraries(gencvc4options toml11::toml11)
  endif()
endif()

if(toml11_FOUND)
  target_link_libraries(murxla toml11::toml11)
  target_compile_definitions(murxla PUBLIC HAVE_TOML11)
endif()

if (Yices_FOUND)
  target_include_directories(murxla PRIVATE ${Yices_INCLUDE_DIR})
  target_link_libraries(murxla ${Yices_LIBRARIES})
  target_compile_definitions(murxla PUBLIC MURXLA_USE_YICES)
  # TODO: Yices options
endif()
