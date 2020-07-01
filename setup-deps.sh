#!/usr/bin/env bash

set -e -o pipefail

deps_dir=$(pwd)/deps
toml_dir=$(pwd)/libs/toml11
reinstall=no

git submodule update --init --recursive

if [ -e "$deps_dir" ]; then
  echo "Dependencies already installed -- will reinstall without cloning."
  echo "If you want to install from a fresh checkout first delete '$deps_dir'."
  echo ""
  reinstall=yes
fi

mkdir -p "$deps_dir"
rm -rf "$toml_dir"

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
  cd build
  make install -j $(nproc)
)

# Setup CVC4
(
  cd solvers/cvc4 || exit 1

  if [ "$reinstall" == "no" ]
  then
    ./contrib/get-antlr-3.4
    ./contrib/get-symfpu
  fi

  rm build -rf
  ./configure.sh debug --asan --prefix="$deps_dir" --symfpu
  cd build
  make install -j $(nproc)
)

# Setup toml11
(
  mkdir -p libs
  git clone https://github.com/ToruNiina/toml11.git libs/toml11
  cd libs/toml11

  rm build -rf
  mkdir -p build
  cd build
  cmake .. -DCMAKE_INSTALL_PREFIX="$deps_dir" -Dtoml11_BUILD_TEST=OFF
  make install -j $(nproc)
)
