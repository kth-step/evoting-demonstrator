../lib/cake64 --target=x64 <../cakeml/trusted.cml >../cakeml/trusted.S -B
gcc -D EMULATE_HYPERVISOR -static ../cakeml/trusted.S ../cakeml/basis_ffi.c -o cake_app

gcc -D EMULATE_HYPERVISOR -static -c ../linuxapp/invoke_cakeml.c -o invoke_cakeml.o
ar rcs libinvoke_cake.a invoke_cakeml.o
rustc --cfg 'emulate_hypervisor' -L . ../linuxapp/rust_app.rs -o rust_app

gcc emulation.c -o emulation
