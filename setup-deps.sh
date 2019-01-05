#!/bin/bash

git submodule init
git submodule update --recursive --remote

deps_dir=$(pwd)/deps

if [ -e "$deps_dir" ]; then
  echo "Dependencies already installed or delete '$deps_dir'"
  exit 0
fi

mkdir -p "$deps_dir"

# Setup Boolector
(
  cd solvers/boolector || exit 1
  ./contrib/setup-btor2tools.sh
  ./contrib/setup-lingeling.sh

  rm build -rf
  ./configure.sh --prefix "$deps_dir"
  cd build || exit 1
  make install -j $(nproc)
)

# Setup CVC4
(
  cd solvers/cvc4 || exit 1
  ./contrib/get-antlr-3.4

  rm build -rf
  ./configure.sh --prefix="$deps_dir"
  cd build || exit 1
  make install -j $(nproc)
)

# Setup cxxopts
(
  cd libs/cxxopts || exit 1

  rm build -rf
  mkdir -p build || exit 1
  cd build || exit 1
  cmake .. -DCMAKE_INSTALL_PREFIX="$deps_dir"
  make install -j $(nproc)
)
