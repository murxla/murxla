#!/usr/bin/env bash

set -e -o pipefail

deps_dir=$(pwd)/deps
toml_dir=$(pwd)/libs/toml11

reinstall=no
freshinstall=no
coverage=no

btor=yes
bzla=yes
cvc4=yes
yices=yes

#--------------------------------------------------------------------------#

die () {
  echo "*** `basename "$0"`: $*" 1>&2
  exit 1
}

usage () {
cat <<EOF
usage: $0 [<option> ...]

where <option> is one of the following:

  -h, --help            print this message and exit
  -f, --fresh-install   install solvers from a fresh checkout
  -c, --coverage        compile solvers with support for coverage testing
  --only-btor           only set up Boolector
  --only-bzla           only set up Bitwuzla
  --only-cvc4           only set up CVC4
  --only-yices          only set up Yices
EOF
  exit 0
}

while [ $# -gt 0 ]
do
  opt=$1
  case $opt in
    -h|--help) usage;;
    -f|--fresh-install) freshinstall=yes;;
    -c|--coverage) coverage=yes;;
    --only-btor) cvc4=no; yices=no;;
    --only-cvc4) btor=no; yices=no;;
    --only-yices) btor=no; cvc4=no;;

    -*) die "invalid option '$opt' (try '-h')";;
  esac
  shift
done

#--------------------------------------------------------------------------#

git submodule update --init --recursive

if [ "$freshinstall" == "yes" ]
then
  rm -rf "$deps_dir"
fi
if [ -e "$deps_dir" ]; then
  echo "(Some) dependencies already installed. Will reinstall already installed"
  echo "dependencies without cloning."
  echo "If you want to install from a fresh checkout, use -f (--fresh-install) "
  echo "or delete $deps_dir."
  echo ""
  reinstall=yes
fi

mkdir -p "$deps_dir"
rm -rf "$toml_dir"

# Setup Boolector
(
  if [ "$btor" == "yes" ]
  then
    cd solvers/boolector || exit 1

    if [ "$reinstall" == "no" ]
    then
      ./contrib/setup-btor2tools.sh
      ./contrib/setup-lingeling.sh
      ./contrib/setup-cadical.sh
    else
      if [[ ! -d solvers/boolector/deps/btor2tools ]]
      then
        ./contrib/setup-btor2tools.sh
      fi
      if [[ ! -d solvers/boolector/deps/lingeling ]]
      then
        ./contrib/setup-lingeling.sh
      fi
      if [[ ! -d solvers/boolector/deps/cadical ]]
      then
        ./contrib/setup-cadical.sh
      fi
    fi

    cov=
    if [ "$coverage" == "yes" ]
    then
      cov="-gcov"
    fi

    rm build -rf
    ./configure.sh -g --asan --prefix "$deps_dir" "$cov"
    cd build
    make install -j $(nproc)
  fi
)

# Setup Bitwuzla
(
  if [ "$bzla" == "yes" ]
  then
    cd solvers/cbitwuzla || exit 1

    if [ "$reinstall" == "no" ]
    then
      ./contrib/setup-btor2tools.sh
      ./contrib/setup-lingeling.sh
      ./contrib/setup-cadical.sh
    else
      if [[ ! -d solvers/cbitwuzla/deps/btor2tools ]]
      then
        ./contrib/setup-btor2tools.sh
      fi
      if [[ ! -d solvers/cbitwuzla/deps/lingeling ]]
      then
        ./contrib/setup-lingeling.sh
      fi
      if [[ ! -d solvers/cbitwuzla/deps/cadical ]]
      then
        ./contrib/setup-cadical.sh
      fi
    fi

    cov=
    if [ "$coverage" == "yes" ]
    then
      cov="-gcov"
    fi

    rm build -rf
    ./configure.sh -g --asan --symfpu --prefix "$deps_dir" "$cov"
    cd build
    make install -j $(nproc)
  fi
)

# Setup CVC4
(
  if [ "$cvc4" == "yes" ]
  then
    cd solvers/cvc4 || exit 1

    if [ "$reinstall" == "no" ]
    then
      ./contrib/get-antlr-3.4
      ./contrib/get-symfpu
    else
      if [[ ! -d solvers/cvc4/deps/antlr-3.4 ]]
      then
        ./contrib/get-antlr-3.4
      fi
      if [[ ! -d solvers/cvc4/deps/symfpu-CVC4 ]]
      then
        ./contrib/get-symfpu
      fi
    fi

    cov=
    if [ "$coverage" == "yes" ]
    then
      cov="--coverage"
    fi

    rm build -rf
    ./configure.sh debug --asan --prefix="$deps_dir" --symfpu $cov
    cd build
    make install -j $(nproc)
  fi
)

# Setup Yices
(
  if [ "$yices" == "yes" ]
  then
    cd solvers/yices || exit 1

    rm build -rf
    autoconf
    if [ "$coverage" == "yes" ]
    then
      cov="-fprofile-arcs -ftest-coverage"
    fi
    CCFLAGS="-g -g3 -ggdb $cov" ./configure --prefix="$deps_dir"
    make -j $(nproc)
    make install -j $(nproc)
  fi
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
