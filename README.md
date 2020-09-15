# smtmbt

## How to plug in a yet unsupported SMT solver

add repo as submodule
git submodule add git@github.com:SRI-CSL/yices2.git solvers/yices

add to setup_deps.sh

provide package finder `Find<Solver>` for cmake in folder cmake/
if `make install` of the solver build system doesn't provide any
-> do we have explain in detail what it has to contain? maybe give example?

in `CMakeLists.txt` add
`find_package(<Solver>)`

in `src/CMakeLists.txt` add (example)
```
if(Boolector_FOUND)
  target_link_libraries(smtmbt Boolector::boolector)
  target_compile_definitions(smtmbt PUBLIC SMTMBT_USE_BOOLECTOR)

  add_executable(genbtoropt btor/gen_btor_options.cpp)
  target_link_libraries(genbtoropt Boolector::boolector)
endif()

if (Yices_FOUND)
  target_link_libraries(smtmbt ${YICES_LIBRARIES})
  target_compile_definitions(smtmbt PUBLIC SMTMBT_USE_YICES)
  # TODO: Yices options
endif()
```

add `<solver>_solver.cpp` to `smtmbt_src_files` in `src/CMakeLists.txt`

derive `<Solver>Solver` from `Solver`
derive `<Solver>Sort` from `AbsSort`
derive `<Solver>Term` from `AbsTerm`

in file `<solver>_solver.(h|cpp)`
wrap in namespace `smtmbt::<solver>`
override all pure virtual functions
override all virtual functions that correspond to theories supported by solver
-> we need to document this

header wrapped in
```
#ifdef SMTMBT_USE_<SOLVER>
#ifndef __SMTMBT__<SOLVER>_SOLVER_H
#define __SMTMBT__<SOLVER>_SOLVER_H
...
#endif
#endif
```

explain
`get_supported_op_kinds` vs `get_unsupported_op_kinds`

helpers needed:
`<solver term type> get_<solver>_term(Term term) const;`
`<solver sort type> get_<solver>_sort(Sort sort) const;`


solver options??

solver specific actions
solver specific operators
supported/unsupported ops/theories

call `Action::reset_sat()` in solver-specific actions that perform
actions that require to leave the SAT state (SMT-LIB state)

if solver caches a model, unsat core, or similar, make sure to override
`Solver::reset_sat()` (called by `Action`)

main.cpp:
`#define SMTMBT_SOLVER_<SOLVER> "<solver>"`
add option `--<solver>`
add
```
    if (options.solver == SMTMBT_SOLVER_<SOLVER>)
    {
      solver = new <solver>::<Solver>Solver(rng);
    }
```

## Solver-Specific Operators
override op string
solver manager: add op kind
-> override `Solver::configure_smgr()`
