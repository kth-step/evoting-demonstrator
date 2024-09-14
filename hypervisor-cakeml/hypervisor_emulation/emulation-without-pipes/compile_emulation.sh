#cd hypervisor_emulation
#../cakeml-kth-repo/hypervisor-cakeml/lib/cake <../cakeml-kth-repo/hypervisor-cakeml/cakeml/trusted.cml >trusted.S -B
#gcc -D EMULATE_HYPERVISOR -nostdlib trusted.S ../cakeml-kth-repo/hypervisor-cakeml/cakeml/basis_ffi.c ../cakeml-kth-repo/hypervisor-cakeml/cakeml/start.S -T cake_guest.ld -o cakeml







#gcc -D EMULATE_HYPERVISOR -static -c ../cakeml-kth-repo/hypervisor-cakeml/linuxapp/invoke_cakeml.c cakeml -o invoke_cakeml.o
#ar rcs libinvoke_cakeml.a invoke_cakeml.o
#rustc -L . ../cakeml-kth-repo/hypervisor-cakeml/linuxapp/rust_app.rs -o rust_app


#gcc -D EMULATE_HYPERVISOR -static -c invoke_cakeml.c -o invoke_cakeml.o
#gcc -D EMULATE_HYPERVISOR -static -c cakeml_emulation.c -o cakeml_emulation.o
#gcc -D EMULATE_HYPERVISOR -static -c rust_to_cakeml.S -o rust_to_cakeml.o
#gcc -D EMULATE_HYPERVISOR -static -c ../cakeml/cakeml_to_rust.S -o cakeml_to_rust.o
#ar rcs libinvoke_cakeml.a invoke_cakeml.o
#ar rcs libcakeml_emulation.a cakeml_emulation.o
#ar rcs librust_to_cakeml.a rust_to_cakeml.o
#ar rcs libcakeml_to_rust.a cakeml_to_rust.o
#rustc -Ctarget-feature=+crt-static -L . rust_app.rs -o rust_app


#rm rust_app.rust_app.dd01047c-cgu.*
#rm cakeml_emulation.o 
#rm cakeml_to_rust.o 
#rm emulation.o 
#rm libcakeml_emulation.a 
#rm libcakeml_to_rust.a 
#rm libemulation.a 
#rm libinvoke_cakeml.a 
#rm librust_to_cakeml.a 
#rm rust_app.4kfwhl4ncix86by.rcgu.o

#The name of the library must match the name given in rust for C library in #[link(name = "invoke_cake", ...)]
#gcc -D TEST -c -static invoke_cakeml.c -o invoke_cakeml.o
#ar rcs libinvoke_cake.a invoke_cakeml.o
#rustc -L . rust_app.rs -o rust_app
#rustc -L /home/jhagl/PhD/BBB/rajat/cakeml-kth-repo/hypervisor-cakeml/linuxapp rust_app.rs -o rust_app

#THIS WORKS
#gcc -D TEST -static -c invoke_cakeml.c -o invoke_cakeml.o
#gcc -D TEST -static -c external_printf.c -o external_printf.o
#ar rcs libinvoke_cakeml.a invoke_cakeml.o external_printf.o
#rustc -L . rust_app.rs -o rust_app

#Hypervisor emulation without pipes
#../lib/cake64 --target=x64 <../cakeml/trusted.cml >../cakeml/trusted.S -B
#gcc -static -c ../cakeml/trusted.S -o trusted.o
#gcc -static -c ../cakeml/cakeml_to_rust.S -o cakeml_to_rust.o
#gcc -D EMULATE_HYPERVISOR -static -c ../cakeml/basis_ffi.c -o basis_ffi.o
#gcc -D EMULATE_HYPERVISOR -static -c invoke_cakeml.c -o invoke_cakeml.o
#gcc -static -c rust_to_cakeml.S -o rust_to_cakeml.o
#ar rcs libinvoke_cake.a trusted.o cakeml_to_rust.o basis_ffi.o invoke_cakeml.o rust_to_cakeml.o
#rustc -L . rust_app.rs -o rust_app

../lib/cake64 --target=x64 <../cakeml/trusted.cml >../cakeml/trusted.S -B
gcc -D EMULATE_HYPERVISOR -static ../cakeml/trusted.S ../cakeml/basis_ffi.c -o cake_app

gcc -D EMULATE_HYPERVISOR -static -c ../linuxapp/invoke_cakeml.c -o invoke_cakeml.o
ar rcs libinvoke_cake.a invoke_cakeml.o
rustc --cfg 'emulate_hypervisor' -L . ../linuxapp/rust_app.rs -o rust_app
#rustc -L . rust_app.rs -o rust_app

gcc emulation.c -o emulation
