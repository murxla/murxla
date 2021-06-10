# murxla

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
  target_link_libraries(murxla Boolector::boolector)
  target_compile_definitions(murxla PUBLIC MURXLA_USE_BOOLECTOR)

  add_executable(genbtoropt btor/gen_btor_options.cpp)
  target_link_libraries(genbtoropt Boolector::boolector)
endif()

if (Yices_FOUND)
  target_link_libraries(murxla ${YICES_LIBRARIES})
  target_compile_definitions(murxla PUBLIC MURXLA_USE_YICES)
  # TODO: Yices options
endif()
```

add `<solver>_solver.cpp` to `murxla_src_files` in `src/CMakeLists.txt`

derive `<Solver>Solver` from `Solver`
derive `<Solver>Sort` from `AbsSort`
derive `<Solver>Term` from `AbsTerm`

in file `<solver>_solver.(h|cpp)`
wrap in namespace `murxla::<solver>`
override all pure virtual functions
override all virtual functions that correspond to theories supported by solver
-> we need to document this

header wrapped in
```
#ifdef MURXLA_USE_<SOLVER>
#ifndef __MURXLA__<SOLVER>_SOLVER_H
#define __MURXLA__<SOLVER>_SOLVER_H
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
`#define MURXLA_SOLVER_<SOLVER> "<solver>"`
add option `--<solver>`
add
```
    if (options.solver == MURXLA_SOLVER_<SOLVER>)
    {
      solver = new <solver>::<Solver>Solver(rng);
    }
```

## Solver-Specific Operators
override op string
solver manager: add op kind
-> override `Solver::configure_smgr()`

## Solver-specific Special Values
Special BV values (0, 1, ones, min and max signed) are defined for all solvers
but don't have an SMT-LIB equivalent. Solvers that support theory of BV must
override `Solver::mk_special_value` to handle these special values.
If the solver doesn't provide a dedicated API function for these values,
convert them to binary, decimal or hexadecimal strings or integer values
with the utility functions for provided in `src/util.hpp`.

Add in `Solver::new_solver()` via `Solver::add_special_value`
Add handling in `Solver::mk_special_value`.


# Coverage Reports

1. Configure with `cmake .. -DGCOV=ON` and setup solvers with `--coverage`
2. Prior to running `murxla` reset the coverage data via `make coverage-reset`
3. Run `murxla` for some time
4. Generate the coverage report via `make coverage`
