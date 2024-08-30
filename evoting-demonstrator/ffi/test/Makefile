MAKEFLAGS += --no-builtin-rules

ifndef VCSDIR
$(error VCSDIR is not set)
endif

ifndef CAKEDIR
$(error CAKEDIR is not set)
endif

CML_BASIS_FFI=$(CAKEDIR)/basis_ffi.c
CAKE64=$(CAKEDIR)/cake64

-include $(VCSDIR)/Makefile.ubuntucheck

RUSTNAME=rust_crypto_lib
RUSTLIB_NAME=lib$(RUSTNAME).a
RUST_DEV_PATH=$(VCSDIR)/rust_crypto_lib/
RUSTLIB_EMULATION_PATH=$(RUST_DEV_PATH)/target/release/
RUSTLIB_PATH=$(RUST_DEV_PATH)/target/debug/

# show static link dependencies
# cd $RUSTLIB_PATH
# cargo rustc --lib -- --print native-static-libs
NATIVE_LIBS= -lgcc_s -lutil -lrt -lpthread -lm -ldl -lc

CMLMODULES:= $(shell find $(VCSDIR) -iname "*Module.cml" -type f)

ifdef WOLFSSL
	C_CRYPTO=1
endif

.SUFFIXES:  # disable built-in rules

.PRECIOUS: %.S %.cml %.sexp

.PHONY: all
all: checks.full.S checks.full
	./checks.full

checks.full.cml: $(CMLMODULES) ../functionslib.cml ../cryptffilib.cml ../tevdlib.cml checks.cml
	echo "main();" | cat $^ - > $@

%.S: %.cml
	$(CAKE64) <$< >$@

ifdef C_CRYPTO
LIB_CRYPTO=$(VCSDIR)/c_crypto_lib/
ifdef UBUNTU
CRYPTO_FLAGS=-L /usr/lib/x86_64-linux-gnu/ -lcrypto
else
CRYPTO_FLAGS=-L /usr/lib -lcrypto
endif
ifdef WOLFSSL
CRYPTO_FLAGS=-L $(VCSDIR)/wolfsslout/lib -lwolfssl
endif

checks.full: checks.full.S $(CML_BASIS_FFI) basis_ffi_print.c $(EXTRA) $(LIB_CRYPTO)/libmycrypto.a
	$(CC) $(CML_BASIS_FFI) basis_ffi_print.c $(EXTRA) $< -o $@ \
		-L $(LIB_CRYPTO) -lmycrypto \
		$(CRYPTO_FLAGS)

$(LIB_CRYPTO)/libmycrypto.a: $(LIB_CRYPTO)/mycrypto.c
	$(MAKE) -C $(LIB_CRYPTO) ARCH=

else

checks.full: checks.full.S $(CML_BASIS_FFI) basis_ffi_print.c $(EXTRA) $(RUSTLIB_EMULATION_PATH)/$(RUSTLIB_NAME)
	$(CC) $(CML_BASIS_FFI) basis_ffi_print.c $(EXTRA) $< -o $@ \
		-L $(RUSTLIB_EMULATION_PATH) -l$(RUSTNAME) \
		$(NATIVE_LIBS)

# TODO define $(RUSTLIB_EMULATION_PATH)/$(RUSTLIB_NAME):

endif

.PHONY: clean
clean:
	rm checks.full.cml checks.full.S checks.full

