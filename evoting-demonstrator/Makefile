
-include Makefile.ubuntucheck

# adjustments for compilation on ubuntu
ifdef UBUNTU
	ARM_NONE_EABI_HEADER=/usr/lib/arm-none-eabi/newlib
else
	ARM_NONE_EABI_HEADER=/usr/arm-none-eabi/lib/
endif

# init hacspec
hacspec:
	git clone --depth=1 https://github.com/hacspec/hacspec.git
	git -C $@ fetch origin --depth=1 4ecc847fc944fe996e19423aa41f002f2039dab0
	git -C $@ checkout 4ecc847fc944fe996e19423aa41f002f2039dab0
	sed -i -e '48d' $@/lib/src/bigint_integers.rs
	cd hacspec/examples/sha256 && cargo build

wolfssl:
	git clone --depth=1 https://github.com/wolfSSL/wolfssl
	git -C $@ fetch origin --depth=1 8b587b563ca20da4f43da5f8b9e88ffe0ccb9828
	git -C $@ checkout 8b587b563ca20da4f43da5f8b9e88ffe0ccb9828

# absolute path
WOLFSSLOUT=wolfsslout
WOLFSSLOUT_ABS=$(abspath $(WOLFSSLOUT))

WOLFSSL_OPTIONS= \
	--disable-benchmark \
	--disable-brainpool \
	--disable-chacha \
	--disable-crypttests \
	--disable-des3 \
	--disable-dh \
	--disable-errorstrings \
	--disable-examples  \
	--disable-filesystem \
	--disable-inline \
	--disable-md5 \
	--disable-oldtls \
	--disable-pkcs12 \
	--disable-poly1305 \
	--disable-sha3 \
	--disable-shared \
	--disable-sp \
	--disable-sys-ca-certs \
	--disable-tlsv12 \
	--enable-fastmath \
	--enable-opensslall \
	--enable-reproducible-build \
	--enable-singlethreaded

$(WOLFSSLOUT):
	mkdir -p "$@"

$(WOLFSSLOUT)/lib/libwolfssl.a: | wolfssl $(WOLFSSLOUT)
	cd wolfssl && { \
		make clean ; \
		git clean -xdf ; \
		./autogen.sh ; \
		./configure --prefix=$(WOLFSSLOUT_ABS) \
			CFLAGS="\
					-DHAVE_PK_CALLBACKS -DWOLFSSL_USER_IO -DNO_WRITEV \
					-DNO_WOLFSSL_SERVER -DNO_PWDBASED \
					-DNO_SIMPLE_SERVER -DNO_SIMPLE_CLIENT \
					-DNO_MD5 -DNO_MD4 -DNO_SESSION_CACHE -DNO_RC4 \
					-DNO_DEV_URANDOM -DNO_RESUME_SUITE_CHECK -DNO_OLD_TLS \
					-DNO_SHA -DNO_DSA -DNO_DES3 \
					-DWOLFSSL_NO_SOCK \
				" \
			$(WOLFSSL_OPTIONS) ; \
		$(MAKE) ; \
		$(MAKE) install ; \
	}

WOLFSSLOUT_ARM=wolfssloutarm
WOLFSSLOUT_ARM_ABS=$(abspath $(WOLFSSLOUT_ARM))

$(WOLFSSLOUT_ARM):
	mkdir -p $@

$(WOLFSSLOUT_ARM)/lib/libwolfssl.a: | wolfssl $(WOLFSSLOUT_ARM)
	cd wolfssl && { \
		$(MAKE) clean ; \
		git clean -xdf ; \
		./autogen.sh ; \
		./configure \
			--host=arm-non-eabi \
			CC=arm-none-eabi-gcc \
			AR=arm-none-eabi-ar \
			STRIP=arm-none-eabi-strip \
			RANLIB=arm-none-eabi-ranlib \
			--prefix=$(WOLFSSLOUT_ARM_ABS) \
			CFLAGS="-march=armv8-a --specs=nosys.specs \
					-DHAVE_PK_CALLBACKS -DWOLFSSL_USER_IO -DNO_WRITEV \
					-DTIME_T_NOT_64BIT \
					-DNO_WOLFSSL_SERVER -DNO_PWDBASED \
					-DNO_SIMPLE_SERVER -DNO_SIMPLE_CLIENT \
					-DNO_MD5 -DNO_MD4 -DNO_SESSION_CACHE -DNO_RC4 \
					-DNO_DEV_URANDOM -DNO_RESUME_SUITE_CHECK -DNO_OLD_TLS \
					-DNO_SHA -DNO_DSA -DNO_DES3 \
					-DWOLFSSL_NO_SOCK \
				" \
				$(WOLFSSL_OPTIONS) ; \
		$(MAKE) ; \
		$(MAKE) install ; \
	}

wolfssl-examples:
	git clone --depth=1 https://github.com/wolfSSL/wolfssl-examples
	git -C $@ fetch origin --depth=1 a70760ed82b1b1a09ec5ebcf0ee4e8b83c77a0f3
	git -C $@ checkout a70760ed82b1b1a09ec5ebcf0ee4e8b83c77a0f3

wolfssl-examples/signature/signature: $(WOLFSSLOUT)/lib/libwolfssl.a | wolfssl-examples
	cd wolfssl-examples/signature && { \
		$(MAKE) C_INCLUDE_PATH=$(WOLFSSLOUT_ABS) \
			LD_LIBRARY_PATH=$(WOLFSSLOUT)/lib/ \
			CFLAGS=-L$(WOLFSSLOUT_ABS)/lib ; \
	}

.PHONY: run_wolfssl_signature
run_wolfssl_signature: wolfssl-examples/signature/signature
	env LD_LIBRARY_PATH=$(WOLFSSLOUT)/lib \
		wolfssl-examples/signature/signature \
			wolfssl-examples/signature/signature

openssl:
	git clone --depth=1 git://git.openssl.org/openssl.git
	git -C $@ fetch origin --depth=1 60f6968
	git -C $@ checkout 60f6968

opensslout:
	mkdir -p $@

CROSS_COMPILE_PREFIX=arm-linux-gnueabihf-

openssl/Makefile: openssl | opensslout
	cd $< && \
	perl Configure linux-generic32 --cross-compile-prefix=$(CROSS_COMPILE_PREFIX) \
	--prefix=$(abspath opensslout) --openssldir=$(abspath opensslout) \
	no-apps no-atexit no-docs no-dso no-ec no-ocsp no-posix-io \
	no-shared no-sock no-ssl-trace no-stdio no-quic no-threads no-thread-pool \
	no-uplink no-bulk no-err \
	no-dso no-dgram no-ct no-gost no-http

opensslout/lib/libcrypto.a: openssl/Makefile
	$(MAKE) -C openssl CROSS_COMPILE=$(CROSS_COMPILE_PREFIX)
	$(MAKE) -C openssl install

.PHONY: clean
clean:
	rm -rf \
		$(WOLFSSLOUT)/lib \
		opensslout/lib \

.PHONY: cleanHOL
cleanHOL:
	find -type d \( \
		-name '.HOLMK' \
		-o -name '.hollogs' \
		-o -name '.holobjs' \) -execdir $(HOLDIR)/bin/Holmake cleanAll \;

# ar -t lib*.a
# libtool library file,
# nm -D --defined-only lib*.la
# nm -D /usr/lib/libopenal.so.1
# objdump -T *.so
#
# readelf -sW /lib/liblzma.so.5 |head -n10

