#!/bin/bash

deps_dir=$(pwd)/deps
reinstall=no

git submodule init

if [ -e "$deps_dir" ]; then
  echo "Dependencies already installed -- will reinstall without cloning."
  echo "If you want to install from a fresh checkout first delete '$deps_dir'."
  echo ""
  reinstall=yes
  git submodule update --recursive --remote
fi

mkdir -p "$deps_dir"

# Setup Boolector
(
  cd solvers/boolector || exit 1

  if [ "$reinstall" == "no" ]
  then
    ./contrib/setup-btor2tools.sh
    ./contrib/setup-lingeling.sh
  fi

  rm build -rf
  ./configure.sh -g --asan --prefix "$deps_dir"
  cd build || exit 1
  make install -j $(nproc)
)

# Setup CVC4
(
  cd solvers/cvc4 || exit 1

  if [ "$reinstall" == "no" ]
  then
    ./contrib/get-antlr-3.4
  fi

  rm build -rf
  ./configure.sh debug --asan --prefix="$deps_dir"
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
