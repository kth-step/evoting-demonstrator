Contains a rudimentary application for linux written in Rust and linked against `libhypercall` derived from `hypercall.c`.

Compilation is done by using cross-compilers provided by Buildroot. Compilation can be done by means of the following commands, provided that invoke_cakeml.c and rust_app.rs are stored in the current directory:
<path-to-arm-gcc-cross-compiler>/arm-buildroot-linux-gnueabihf-gcc-8.4.0 -static -c invoke_cakeml.c -o invoke_cakeml.o
<path-to-arm-gcc-cross-compiler>/arm-buildroot-linux-gnueabihf-ar rcs libinvoke_cakeml.a invoke_cakeml.o
<path-to-arm-rust-cross-compiler>/rustc --target=armv7-unknown-linux-gnueabihf -Clinker=arm-linux-gnueabihf-gcc -Ctarget-feature=+crt-static -L . rust_app.rs -o rust_app
