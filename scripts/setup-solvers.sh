#!/usr/bin/env bash

set -e -o pipefail

deps_dir=$(pwd)/deps
src_dir="$deps_dir"/src
bitwuzla_dir="$src_dir"/bitwuzla
cvc5_dir="$src_dir"/cvc5
yices_dir="$src_dir"/yices

reinstall=no
freshinstall=no
coverage=no
asan=no

bitwuzla=yes
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
  --only-bitwuzla       only set up Bitwuzla
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
    --only-cvc5) bitwuzla=no; yices=no;;
    --only-yices) bitwuzla=no; cvc5=no;;
    --only-bitwuzla) cvc5=no; yices=no;;

    -*) die "invalid option '$opt' (try '-h')";;
  esac
  shift
done

#--------------------------------------------------------------------------#

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
mkdir -p "$src_dir"

# Setup Bitwuzla
(
  if [ "$bitwuzla" == "yes" ]
  then
    if [ ! -d "$bitwuzla_dir" ]
    then
      git clone https://github.com/bitwuzla/bitwuzla.git "$bitwuzla_dir"
    fi
    cd "$bitwuzla_dir" || exit 1

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

    rm -rf build
    ./configure.py debug --prefix "$deps_dir" $cov $as --no-testing
    cd build
    ninja install
  fi
)

# Setup cvc5
(
  if [ "$cvc5" == "yes" ]
  then
    if [ ! -d "$cvc5_dir" ]
    then
      git clone https://github.com/cvc5/cvc5.git "$cvc5_dir"
    fi
    cd "$cvc5_dir" || exit 1

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

    rm -rf build
    ./configure.sh debug --prefix="$deps_dir" --auto-download $cov $as --cocoa --gpl
    cd build
    make install -j $(nproc)
  fi
)

# Setup Yices
(
  if [ "$yices" == "yes" ]
  then
    if [ ! -d "$yices_dir" ]
    then
      git clone https://github.com/SRI-CSL/yices2.git "$yices_dir"
    fi
    cd "$yices_dir" || exit 1

    rm -rf build
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
