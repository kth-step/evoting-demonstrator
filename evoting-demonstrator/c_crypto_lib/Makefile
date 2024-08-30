
ifndef VCSDIR
$(error VCSDIR is not set)
endif

-include $(VCSDIR)/Makefile.ubuntucheck

ifdef WOLFSSL
	LIBNAME=wolfssl
	WOLFSSL_FLAGS=
#		-DNO_FILESYSTEM \
#		-DSINGLE_THREADED \
#		-DWOLFSSL_NO_SOCK \
#		-DNO_WOLFSSL_DIR \
#		-DWOLFSSL_ALLOW_NO_SUITES \
#		-DWOLFSSL_USER_IO \
#		-DNO_WRITEV
else
	LIBNAME=openssl
	WOLFSSL_FLAGS=
endif

# default to x86
ifndef ARCH
	C_INCLUDE_PATH=/usr/include/openssl
	LD_LIBRARY_PATH=/usr/lib
	CRYPTO_FLAGS=-L $(LD_LIBRARY_PATH) -lcrypto
ifdef WOLFSSL
	C_INCLUDE_PATH=$(VCSDIR)/wolfssl
	LD_LIBRARY_PATH=$(VCSDIR)/wolfsslout/lib
	CRYPTO_FLAGS=-L $(LD_LIBRARY_PATH) -lwolfssl
endif
	CROSS_COMPILE_PREFIX=
	ARCH=
else # arm
	ARCH=arm
	C_INCLUDE_PATH=$(VCSDIR)/openssl/include
	LD_LIBRARY_PATH=$(VCSDIR)/opensslout
	CRYPTO_FLAGS=-L $(LD_LIBRARY_PATH) -lcrypto
ifdef WOLFSSL
	C_INCLUDE_PATH=$(VCSDIR)/wolfssl
	LD_LIBRARY_PATH=$(VCSDIR)/wolfsslout$(ARCH)/lib
	CRYPTO_FLAGS=-L $(LD_LIBRARY_PATH) -lwolfssl
ifdef UBUNTU
	CRYPTO_FLAGS+=-L /usr/lib/arm-none-eabi/newlib -lc -lgcc -lrdimon
endif
endif
	CROSS_COMPILE_PREFIX=arm-none-eabi-
endif

lib$(ARCH)mycrypto.a: $(ARCH)mycrypto.o $(ARCH)$(LIBNAME)crypto.o
	test -r $@ && unlink $@ || true
	$(CROSS_COMPILE_PREFIX)ar rcs $@ $^

$(ARCH)mycrypto.o: mycrypto.c
	env \
		LD_LIBRARY_PATH=$(LD_LIBRARY_PATH) \
		C_INCLUDE_PATH=$(C_INCLUDE_PATH) \
	$(CROSS_COMPILE_PREFIX)gcc $^ -o $@ $(CRYPTO_FLAGS) \
		-c -static -nostdlib \
		$(WOLFSSL_FLAGS)

lib$(ARCH)$(LIBNAME)crypto.a: $(ARCH)$(LIBNAME)crypto.o
	test -r $@ && unlink $@ || true
	$(CROSS_COMPILE_PREFIX)ar rcs $@ $^

$(ARCH)$(LIBNAME)crypto.o: $(LIBNAME)crypto.c
	env \
		LD_LIBRARY_PATH=$(LD_LIBRARY_PATH) \
		C_INCLUDE_PATH=$(C_INCLUDE_PATH) \
	$(CROSS_COMPILE_PREFIX)gcc $^ -o $@ $(CRYPTO_FLAGS) \
		-c -static -nostdlib \
		$(WOLFSSL_FLAGS)

