# Trustfull Electronic Voting Demonstrator

The verified vote collection server for the Trustfull Electronic Voting
Demonstrator (TEVD) is hosted in this directory.

## Repository structure

- `base64` in-logic base64 transformation
- `c_crypto_lib` C library for cryptography (for embedded)
- `rust_crypto_lib` Rust library for cryptography (for native)
- `crosscompile` code for cross compilation
- `deser` library for matching Rust and HOL4 (de)serialisation
- `doc` documentation, like paper draft
- `ffi` unverified cakeml FFI library functions
- `emulation` further cross compilation code
- `json` in-logic json parsing
- `rust_app_lib` trusted application with hypercalls
- `rust_min_app` trusted application with hypercalls, variant with minimal
  memory footprint.
  Serves as a replacement of core parts of `rust_app_lib` and can be changed
  with the `RUSTNAME` make variable.
- `rust_client_server` server that receives client votes and inserts these into
  the VCS
- `rust_premix_server` server between VCS and mixnet that receives votes
- `src` the HOL4 theories
  - `src/tevd/hol4` HOL4 models, and refinement proofs
  - `src/tevd/cakeml` translation and binary code extraction
- `test_assets` pre-cast votes for testing
- `tests` test cases named in the paper

## Main theorems

The two theorems
`network_step_execution_system_transition_correct1` and
`network_step_execution_system_transition_correct2`
at the path `src/tevd/hol/TevDNetworkedSystemProofScript.sml` contain the main
correctness result, and use refinement theorems from the same theory.
Files located at `src/tevd/cakeml/` contain the extraction

## Dependencies

- `emulation/` contains code to prepare and compile the guest and the host applications
  ```sh
  cd emulation/
  make demo; killall make
  ```
- `rust_app_lib/` contains some libraries, the main server application, and clients
  For example to start the election run the admin client
  ```sh
  cd rust_app_lib/
  cargo run --bin=input_admin_start
  cargo run --bin=input_admin_end
  ```
- `rust_client_server/` contains the voting-client server
  ```sh
  cd rust_client_server/
  SERVER_ADDRESS="127.0.0.1:7878" cargo run
  ```
  Use curl to submit the ballot `vote.json` to the voting-client server:
  ```sh
  curl "127.0.0.1:7878" --data-urlencode "ballot@test_assets/new_signed_vote.json"
  curl "127.0.0.1:7878" --data-urlencode "ballot@test_assets/aman_vote_240205.json"
  curl "127.0.0.1:7878" --data-urlencode "ballot@test_assets/arve_vote_240201.json"
  curl "127.0.0.1:7878" --data-urlencode "ballot@test_assets/arve_vote_240205.json"
  ```
- `ffi/test/` code for testing the ffi crypto code for vote verification
  independent of the server
  ```sh
  make
  ```
- `test_assets/` example votes used throughout the code for testing

## Build Instructions

Save and set environment variables:
```sh
cat <<<EOF > .envrc
export HYP_ROOT=.../hypervisor-total/
export HOLDIR=.../HOL/
export CAKEMLDIR=/home/arolle/Documents/cakeml/
export CAKEDIR=$HYP_ROOT/hypervisor-cakeml/lib/
export VCSDIR=$(pwd)
EOF
```
Load these into the environment `. .envrc`

With the dependencies in place the extraction can be started by the following
commands, where `$VCSDIR` refers to the root of the checkout of this
repository.

```sh
cd $VCSDIR
rm wolfsslout{,arm}/lib/libwolfssl.a
make wolfsslout/lib/libwolfssl.a
make wolfssloutarm/lib/libwolfssl.a
# test crypto -- with WolfSSL (requires some test_assets)
cd $VCSDIR/ffi/test
make WOLFSSL=1
cd $VCSDIR/crosscompile
make
```

```
cd "$VCSDIR/emulation/"
make
```

### Running the System

The following command starts a `tmux` session with all nodes of the system.
`tmux` is instructed to store the log to `<node_name>.log` when terminating
a node with <kbd>Ctrl</kbd>+<kbd>c</kbd>.

### Demo

A sample election is run with the following commands. All but the last one
start servers and run indefinitely:
```
env RUSTNAME=rust_min_app make -C $VCSDIR/emulation demo LOCAL=1
cd $VCSDIR/rust_app_lib
cargo run --bin=input_admin_start
cd $VCSDIR/rust_client_server/
SERVER_ADDRESS="127.0.0.1:7878" cargo run
cd $VCSDIR/tests
sh test7_verif.sh
```

