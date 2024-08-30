set -eux

HOL_COMMIT="fd366fde86123cf8d42ca2530fa10c15fbf14549"

DIR="$(pwd)"

HOLDIR="$DIR/HOL"
export HOLDIR="$DIR/HOL"

echo ":: HOLDIR: $HOLDIR"

# circumvent error with git github curl RPC failed expected packfile
# export GIT_CURL_VERBOSE=1
export GIT_HTTP_MAX_REQUESTS=16
git config --global http.version HTTP/1.1
git config --global http.postBuffer 524288000
git clone --depth=1 --verbose --no-checkout https://github.com/HOL-Theorem-Prover/HOL/ "$HOLDIR"

cd "$HOLDIR"
git fetch --unshallow origin
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
examples/machine-code/decompiler
examples/machine-code/hoare-triple
examples/machine-code/multiword
examples/miller/miller
EOF
} | while read -r dir; do
  echo ":: building \$HOLDIR/$dir"
  #pushd "$HOLDIR/$dir" > /dev/null
  cd "$HOLDIR/$dir"
  "$HOLDIR/bin/Holmake" --nolmbc --holdir="$HOLDIR"
  #popd > /dev/null
  cd -
done
done

