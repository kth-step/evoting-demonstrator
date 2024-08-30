# The foreign function bindings for CakeML against the rust library

run tests:

```sh
cd test/
make && ./checks.full
```

For using the libcrypto (OpenSSL) based cryptography, additonally supply
`make C_CRYPTO=1` in compilation, for wolfSSL supply
`make C_CRYPTO=1 WOLFSSL=1`

