# murxla

## Quickstart

**Prerequisite:** Solver(s) to test installed to `<prefix-path>`

Currently supported solvers are
[Bitwuzla](https://github.com/bitwuzla/bitwuzla),
[Boolector](https://github.com/boolector/boolector),
[cvc5](https://github.com/cvc5/cvc5), and
[Yices](https://github.com/SRI-CSL/yices2).

```
git clone https://github.com/murxla/murxla.git
cd murxla
mkdir build
cmake .. -DCMAKE_PREFIX_PATH=<prefix-path> // this will configure murxla with support for the solvers in `<prefix-path>`
make
```

After successful compilation you can find the murxla binary in `build/bin/`.
Please refer to `bin/murxla -h` for a list of available options.

**Note:** You can link against any supported solver versions that are
compatiable with the solver versions in [solvers/](https://github.com/murxla/murxla/tree/main/solvers).

**Note:** If murxla is configured without any solver it is still possible to
generate SMT-LIBv2 output and test solver binaries.


## Using murxla

Testing Bitwuzla:

```
murxla --bzla
```

Testing Boolector:
```
murxla --btor
```

Testing cvc5:
```
murxla --cvc5
```

Testing Yices:
```
murxla --yices
```


