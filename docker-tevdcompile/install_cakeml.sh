set -eux

CAKEML_COMMIT="9c063a7d92cadb36c49a6e45856ae0db734dc9e5"

DIR="$(pwd)"

HOLDIR="$DIR/HOL"
export HOLDIR="$DIR/HOL"

CAKEMLDIR="$DIR/cakeml"
# export CAKEMLDIR="$(pwd)"
export CAKEMLDIR="$DIR/cakeml"

echo ":: CAKEMLDIR: $CAKEMLDIR"

# circumvent error with git github curl RPC failed expected packfile
# export GIT_CURL_VERBOSE=1
export GIT_HTTP_MAX_REQUESTS=16
git config --global http.version HTTP/1.1
git config --global http.postBuffer 524288000
git clone --depth=1 --verbose --no-checkout https://github.com/CakeML/cakeml "$CAKEMLDIR"

cd "$CAKEMLDIR"
git fetch --deepen=10
git fetch --deepen=10
git fetch --deepen=10
git fetch --deepen=10
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
compiler/backend/arm7
compiler/backend/serialiser
compiler
EOF
} | while read -r dir; do
  echo ":: building \$CAKEMLDIR/$dir"
  cd "$CAKEMLDIR/$dir" > /dev/null
  env HOLDIR="$HOLDIR" "$HOLDIR/bin/Holmake" --nolmbc --holdir="$HOLDIR"
  cd - > /dev/null
done
done

