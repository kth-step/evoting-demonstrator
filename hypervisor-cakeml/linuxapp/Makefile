
.PHONY: all run
all: libhypercall.so build.rs
	cargo build

run: libhypercall.so
	@: TODO: pass library path through Cargo.toml
	env LD_LIBRARY_PATH=$(CURDIR) cargo run -- argument1

hypercall.o: hypercall.c
	@: object file with position indepenent code
	$(CC) -c -fPIC hypercall.c

libhypercall.so: hypercall.o
	@: link object file into shared library
	$(CC) -shared -o libhypercall.so hypercall.o

