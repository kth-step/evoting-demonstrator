This contains the CakeML program code for the guest and a `basis_ffi.c` that
will provide hypercall-responses from secure to linux.

Example usage:
- `make CAKEFLAGS='--target=arm7' helloworld.S`
  compiles `helloworld.cml` to produce the object file for arm7
- `make CAKEFLAGS='--target=arm7' helloworld`
  compiles `helloworld.cml` to an arm7 ELF executable linked against
  `basis_ffi.c`
- `make EXTRA="basis_ffi_echo.c" echo`
  compiles `echo.cml`, which relies on `basis_ffi_echo.c` for the foreign
  function
- `make EXTRA=basis_ffi_echo.c timing`
- for producing a locally runnable hypercall executable:
  `make hypercall BASIS=../lib/basis_ffi.c EXTRA=basis_ffi_hypercall.c CAKE=.../cake`
  Both `BASIS` and `CAKE` should be left out when compiling for armv7

