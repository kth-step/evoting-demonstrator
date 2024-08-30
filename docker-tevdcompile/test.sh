#!/usr/bin/env dash
# Build HOL4 with prerequisites for CakeML.
# then set HOL4 read-only and build CakeML
# The commits of HOL4 and CakeML match.
#
# run with:
#   env -u CAKEMLDIR -u HOLDIR dash ./test.sh

# bash: set -o pipefail
set -eux

HOL_COMMIT="fd366fde86123cf8d42ca2530fa10c15fbf14549"
CAKEML_COMMIT="9c063a7d92cadb36c49a6e45856ae0db734dc9e5"

HOL_COMMIT="2d2cddffe3dfeee7bc31b0fb499fb32cd2218dd2"
CAKEML_COMMIT="08588c8c69a14aa1e36010a05c6545e7a12a4924"

DIR="$(pwd)"

HOLDIR="$DIR/HOL"
export HOLDIR="$DIR/HOL"
echo ":: HOLDIR: $HOLDIR"
git clone https://github.com/HOL-Theorem-Prover/HOL/ "$HOLDIR"
cd "$HOLDIR"
git checkout "$HOL_COMMIT"

poly < tools/smart-configure.sml
./bin/build --fullbuild

# chmod --recursive u+w "$HOLDIR"

for x in $(seq 1 2); do
{
cat <<EOF
examples/algorithms
examples/algorithms/unification/triangular/first-order
examples/balanced_bst
examples/bootstrap
examples/Crypto/AES
examples/Crypto/RC6
examples/Crypto/TEA
examples/formal-languages
examples/formal-languages/regular
examples/formal-languages/context-free
examples/fun-op-sem/lprefix_lub
examples/l3-machine-code/common
examples/l3-machine-code/lib
examples/l3-machine-code/arm/model
examples/l3-machine-code/arm/step
examples/l3-machine-code/arm8/model
examples/l3-machine-code/arm8/step
examples/l3-machine-code/mips/model
examples/l3-machine-code/mips/step
examples/l3-machine-code/riscv/model
examples/l3-machine-code/riscv/step
examples/l3-machine-code/x64/model
examples/l3-machine-code/x64/step
examples/l3-machine-code/x64/prog
examples/machine-code/decompiler
examples/machine-code/hoare-triple
examples/machine-code/multiword
examples/miller/miller
EOF
} | while read -r dir; do
  echo ":: building \$HOLDIR/$dir"
  pushd "$HOLDIR/$dir" > /dev/null
  "$HOLDIR/bin/Holmake" --nolmbc --holdir="$HOLDIR"
  popd > /dev/null
done
done

chmod --recursive u+w "$HOLDIR"
chmod --recursive a-w "$HOLDIR"

# compile dependencies of CakeML twice to avoid the following later failure
# when compiling CakeML:
#    :: building $CAKEMLDIR/misc
#    Scanning $(HOLDIR)/examples/formal-languages/context-free
#    Holmake failed with exception: Io {cause = SysErr ("Permission denied", SOME EACCES), function = "TextIO.openOut", name = ".HOLMK/NTpropertiesTheory.sml.d"}
#    Raised from: ./basis/TextIO.sml: 258:0 - 258:0


CAKEMLDIR="$DIR/cakeml"
# export CAKEMLDIR="$(pwd)"
export CAKEMLDIR="$DIR/cakeml"
#git clone https://github.com/CakeML/cakeml "$CAKEMLDIR"
cd "$CAKEMLDIR"

echo ":: CAKEMLDIR: $CAKEMLDIR"

git checkout "$CAKEML_COMMIT"

for x in $(seq 1 2); do
{
cat <<EOF
developers
misc
semantics
basis/pure
characteristic
translator
translator/monadic
compiler/parsing
basis
compiler/backend/pattern_matching
unverified/sexpr-bootstrap
unverified/reg_alloc
compiler/backend/reg_alloc
compiler/encoders/asm
compiler/backend
compiler/encoders/ag32
compiler/backend/ag32
compiler/compiler/arm7
EOF
} | while read -r dir; do
  echo ":: building \$CAKEMLDIR/$dir"
  pushd "$CAKEMLDIR/$dir" > /dev/null
  env HOLDIR="$HOLDIR" "$HOLDIR/bin/Holmake" --nolmbc --holdir="$HOLDIR"
  popd > /dev/null
done
done

# chmod --recursive u+w "$CAKEMLDIR"
chmod --recursive a-w "$CAKEMLDIR"

