#!/usr/bin/env bash

set -e -o pipefail

deps_dir=$(pwd)/deps

reinstall=no
freshinstall=no
coverage=no
asan=no

btor=yes
bzla=yes
cvc5=yes
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
  -a, --asan            build solvers with ASan instrumentation
  --only-btor           only set up Boolector
  --only-bzla           only set up Bitwuzla
  --only-cvc5           only set up cvc5
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
    -a|--asan) asan=yes;;
    --only-btor) bzla=no; cvc5=no; yices=no;;
    --only-cvc5) bzla=no; btor=no; yices=no;;
    --only-yices) bzla=no; btor=no; cvc5=no;;
    --only-bzla) btor=no; cvc5=no; yices=no;;

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
      cov="--gcov"
    fi

    as=
    if [ "$asan" == "yes" ]
    then
      as="--asan"
    fi

    rm build -rf
    ./configure.sh -g --prefix "$deps_dir" $cov $as --no-testing
    cd build
    make install -j $(nproc)
  fi
)

# Setup Bitwuzla
(
  if [ "$bzla" == "yes" ]
  then
    cd solvers/bitwuzla || exit 1

    if [ "$reinstall" == "no" ]
    then
      ./contrib/setup-btor2tools.sh
      ./contrib/setup-lingeling.sh
      ./contrib/setup-cadical.sh
      ./contrib/setup-symfpu.sh
    else
      if [[ ! -d solvers/bitwuzla/deps/btor2tools ]]
      then
        ./contrib/setup-btor2tools.sh
      fi
      if [[ ! -d solvers/bitwuzla/deps/lingeling ]]
      then
        ./contrib/setup-lingeling.sh
      fi
      if [[ ! -d solvers/bitwuzla/deps/cadical ]]
      then
        ./contrib/setup-cadical.sh
      fi
      if [[ ! -d solvers/bitwuzla/deps/symfpu ]]
      then
        ./contrib/setup-symfpu.sh
      fi
    fi

    cov=
    if [ "$coverage" == "yes" ]
    then
      cov="--gcov"
    fi

    as=
    if [ "$asan" == "yes" ]
    then
      as="--asan"
    fi

    rm build -rf
    ./configure.sh debug --prefix "$deps_dir" $cov $as --no-testing
    cd build
    make install -j $(nproc)
  fi
)

# Setup cvc5
(
  if [ "$cvc5" == "yes" ]
  then
    cd solvers/cvc5 || exit 1

    cov=
    if [ "$coverage" == "yes" ]
    then
      cov="--coverage"
    fi

    as=
    if [ "$asan" == "yes" ]
    then
      as="--asan"
    fi

    rm build -rf
    ./configure.sh debug --prefix="$deps_dir" --auto-download $cov $as
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

    cov=
    if [ "$coverage" == "yes" ]
    then
      cov="-fprofile-arcs -ftest-coverage"
    fi

    as=
    if [ "$asan" == "yes" ]
    then
      as="-fsanitize=address -fno-omit-frame-pointer -fsanitize-recover=address"
    fi
    CFLAGS="$cov $as" CPPFLAGS="$cov $as" ./configure --prefix="$deps_dir"
    make -j $(nproc) MODE=debug
    make install -j $(nproc) MODE=debug
  fi
)
