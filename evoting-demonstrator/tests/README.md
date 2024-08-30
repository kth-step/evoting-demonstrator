# collection of all test scenarios

Run a tests as follows.
Start a server that converts HTTP traffic into the input format for
the verified application.
```sh
cd ../rust_client_server
SERVER_ADDRESS="127.0.0.1:7878" cargo run
```
Run one of the tests
```sh
./testscript_unverif.sh test1_unverif.sh
./testscript_verif.sh test1_verif.sh
```

- `test1` correct ballot
- `test2` not yet in voting phase
- vote format is invalid -- format_check
  (hashes don't match, invalid jws, cannot extract username )
  - `test3` hashes don't match
  - `test4` invalid jws (cannot extract username)
  - vote is not a valid bytetree -- needs to be signed
- vote is unauthenticated -- auth_check fail (covered by invalid jws)
- `test5` voter is not eligible
- `test6` vote stored followed by voter has already voted
- `test7` submission of votes for several voters

