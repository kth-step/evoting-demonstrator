
ifndef VCSDIR
$(error VCSDIR is not set)
endif

ifndef HOLDIR
$(error HOLDIR is not set)
endif

ifndef HYP_ROOT
$(error HYP_ROOT is not set)
endif

ifndef TOOLCHAIN
$(error TOOLCHAIN is not set)
endif

ifndef CAKEDIR
$(error CAKEDIR is not set)
endif

CAKE32=$(CAKEDIR)/cake32

# flag to enforce cross compilation with WOLFSSL library
WOLFSSL=1

-include $(VCSDIR)/Makefile.ubuntucheck

# adjustments for compilation on ubuntu
ifdef UBUNTU
	ARM_NONE_EABI_HEADER=/usr/lib/arm-none-eabi/newlib
	# for print.c inclusion
	UBUNTU_ONLY=-DUBUNTU
else
	ARM_NONE_EABI_HEADER=/usr/arm-none-eabi/lib/
	UBUNTU_ONLY=
endif


# adjust path if we run debug or release version
ifdef RUST_LINUX_DEBUG
	RUST_LINUX_DEBUG_FLAGS=
	RUST_LINUX_DEBUG_PATH=debug
else
	RUST_LINUX_DEBUG_FLAGS=--release
	RUST_LINUX_DEBUG_PATH=release
endif

RUSTNAME?=rust_app_lib
RUST_LINUX_APP_PATH=$(VCSDIR)/$(RUSTNAME)
RUST_LINUX_APP_FILES:=$(shell find $(RUST_LINUX_APP_PATH)/src -type f -iname "*.rs")
OUTDIR=out
OUTDIR_ABS=$(abspath $(OUTDIR))

# for cross compiling the cakeml application
CC=arm-none-eabi-gcc
LD=arm-none-eabi-ld
AR=arm-none-eabi-ar
RANLIB=arm-none-eabi-ranlib
OBJCOPY=arm-none-eabi-objcopy

HOL_EXTRACT_DIR=$(VCSDIR)/src/tevd/cakeml/
HOL_EXTRACT_FILE= tevdProg.sexp
HOL_EXTRACT_DEPS= \
	$(shell find $(VCSDIR)/ffi -name "*lib.cml" -type f) \
	$(HOL_EXTRACT_DIR)/../hol/TevDNetworkedSystemScript.sml \
	$(HOL_EXTRACT_DIR)/TevDLibsProgScript.sml \
	$(HOL_EXTRACT_DIR)/TevDNetworkedSystemProgScript.sml \

# CAKEML_EXTRA= ../../../hypervisor-cakeml/cakeml/print.c
CAKEML_BASIS=$(VCSDIR)/emulation/basis_ffi_emulation.c
CAKEML_EXTRA=print.c
HYP_LIB=$(VCSDIR)/emulation/invoke_cakeml.c


CAKEFLAGS=--target=arm7
CCFLAGS=-nostdlib
LOADLIBS=-T cake_guest.ld start.S
# cargo rustc -- --print native-static-libs
NATIVE_LIBS= -lgcc_s -lutil -lrt -lpthread -lm -ldl -lc

RUST_LIB_CRYPTO_NAME=rust_crypto_lib
RUST_LIB_CRYPTO_FILE=lib$(RUST_LIB_CRYPTO_NAME).a
RUST_LIB_CRYPTO_PATH=../rust_crypto_lib/
RUST_LIB_CRYPTO_FILES:=$(shell find $(RUST_LIB_CRYPTO_PATH)/src -type f -iname "*.rs")
RUST_LIB_OUTDIR=$(OUTDIR_ABS)/armv7-*/release/

# keep intermediate output
.PRECIOUS: %.S %.cml %.sexp \
	tevdProg tevdProg.S

.PHONY: all
all: $(OUTDIR)/server tevdProg.bin


# cross compile the linux application
$(OUTDIR)/server: $(OUTDIR)/libinvoke_cakeml.a $(RUST_LINUX_APP_FILES)
	cd $(RUST_LINUX_APP_PATH) && \
		cargo rustc --bin=server --target-dir="$(OUTDIR_ABS)" \
			$(RUST_LINUX_DEBUG_FLAGS) --target=armv7-unknown-linux-gnueabihf \
			-- -Ctarget-feature=+crt-static \
			-Clinker=$(TOOLCHAIN)gcc \
			-L"$(OUTDIR_ABS)" \
			-linvoke_cakeml
	ln -sf "$(OUTDIR_ABS)/"armv7-*/$(RUST_LINUX_DEBUG_PATH)/server $(OUTDIR)/server

$(OUTDIR):
	mkdir -p $@

# cross compile the linux application

$(OUTDIR)/invoke_cakeml.o: | $(HYP_LIB) $(OUTDIR)
	$(TOOLCHAIN)gcc -nostdlib -static -c $| -o $@

$(OUTDIR)/libinvoke_cakeml.a: $(OUTDIR)/invoke_cakeml.o
	$(TOOLCHAIN)ar rcs $@ $<

$(OUTDIR)/$(RUST_LIB_CRYPTO_FILE): $(RUST_LIB_CRYPTO_FILES)
	cd $(RUST_LIB_CRYPTO_PATH) && \
		cargo +nightly-2023-01-15-x86_64-unknown-linux-gnu rustc \
			--lib --target-dir="$(OUTDIR_ABS)" \
			--target=armv7-unknown-linux-gnueabihf \
			--release \
			-- -Ctarget-feature=+crt-static -L . -L "$(OUTDIR_ABS)"
	ln -sf $(RUST_LIB_OUTDIR)/$(RUST_LIB_CRYPTO_FILE) $(OUTDIR)/$(RUST_LIB_CRYPTO_FILE)

# cross compile the cakeml application

ifdef WOLFSSL
LIB_CRYPTO=$(VCSDIR)/c_crypto_lib/
WOLFSSL_HEADERS=$(VCSDIR)/wolfssl
ARCH=arm

ifdef NO_CRYPTO
%: %.S $(CAKEML_EXTRA) $(CAKEML_BASIS) start.S cake_guest.ld
	env \
	$(CC) $(CAKEML_BASIS) $(CAKEML_EXTRA) $< -o $@ \
		-L $(ARM_NONE_EABI_HEADER) -lc -lgcc -lrdimon \
		$(UBUNTU_ONLY) \
		$(LOADLIBS) \
		-nostdlib -static
else
%: %.S $(CAKEML_EXTRA) $(LIB_CRYPTO)/lib$(ARCH)mycrypto.a $(CAKEML_BASIS) newlib_params.c start.S cake_guest.ld
	env \
	$(CC) $(CAKEML_BASIS) $(CAKEML_EXTRA) $< -o $@ \
		-L $(LIB_CRYPTO) -larmmycrypto \
		-L $(VCSDIR)/wolfssloutarm/lib -lwolfssl \
		-L $(ARM_NONE_EABI_HEADER) -lc -lgcc -lrdimon \
		$(UBUNTU_ONLY) \
		$(LOADLIBS) newlib_params.c \
		-nostdlib -static
endif

$(LIB_CRYPTO)/lib$(ARCH)mycrypto.a: | $(LIB_CRYPTO)/mycrypto.c $(LIB_CRYPTO)/wolfsslcrypto.c
	$(MAKE) -C $(LIB_CRYPTO) WOLFSSL=1 ARCH=arm lib$(ARCH)mycrypto.a

else
%: %.S $(RUST_LIB_CRYPTO_FILE) $(CAKEML_BASIS)
	$(CC) $(CAKEML_BASIS) $< -o $@ \
		-L . -l$(RUST_LIB_CRYPTO_NAME) \
		$(NATIVE_LIBS)
endif

%.S : %.cml
	$(CAKE32) $(CAKEFLAGS) <$< >$@

%.S: %.sexp
	$(CAKE32) $(CAKEFLAGS) \
		--exclude_prelude=true \
		--sexp=true \
		< $< > $@

%.sexp: %Script.sml
	$(HOLDIR)/bin/Holmake --nolmbc

$(HOL_EXTRACT_DIR)/$(HOL_EXTRACT_FILE): $(HOL_EXTRACT_DEPS)
	cd $(HOL_EXTRACT_DIR) && $(HOLDIR)/bin/Holmake --nolmbc

$(HOL_EXTRACT_FILE): $(HOL_EXTRACT_DIR)/$(HOL_EXTRACT_FILE)
	ln -sf $< $@

%.bin: %
	$(OBJCOPY) $< -O binary $@

.PHONY: clean
clean:
	rm -rf $(OUTDIR) tevdProg tevdProg.sexp

.PHONY: cleanCake
cleanCake:
	rm $(HOL_EXTRACT_DIR)/tevdProg.sexp

