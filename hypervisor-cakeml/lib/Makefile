
CAKEML32=cake-x64-32
CAKEML64=cake-x64-64

all: cake32 cake64

cake32.S basis_ffi.c:
	curl --location --silent --continue-at - --output "$(CAKEML32).tar.gz" "https://github.com/CakeML/cakeml/releases/download/v2117/$(CAKEML32).tar.gz"
	tar -zxf "$(CAKEML32).tar.gz" "$(CAKEML32)/basis_ffi.c" "$(CAKEML32)/cake.S" --strip-components 1
	mv cake.S $@

# both use same basis_ffi.c
cake64.S:
	curl --location --silent --continue-at - --output "$(CAKEML64).tar.gz" "https://github.com/CakeML/cakeml/releases/download/v2117/$(CAKEML64).tar.gz"
	tar -zxf "$(CAKEML64).tar.gz" "$(CAKEML64)/basis_ffi.c" "$(CAKEML64)/cake.S" --strip-components 1
	mv cake.S $@

cake32: cake32.S basis_ffi.c
	$(CC) $(LDFLAGS) $< basis_ffi.c $(LOADLIBES) $(LDLIBS) -o $@

cake64: cake64.S basis_ffi.c
	$(CC) $(LDFLAGS) $< basis_ffi.c $(LOADLIBES) $(LDLIBS) -o $@

