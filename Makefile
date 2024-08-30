MAKEFLAGS += -rR

ifndef VCSDIR
$(error VCSDIR is not set)
endif

ifndef TOOLCHAIN
$(error TOOLCHAIN is not set)
endif

ifndef HYP_ROOT
$(error HYP_ROOT is not set)
endif

# when not run in docker some commands require sudo
ifndef DOCKER_RUNNING
	SUDO=sudo
else
	SUDO=
endif

# optional parameter: TEVD_rs TEVD_cml
ROOTFS=rootfs
HYP_RS=$(HYP_ROOT)/$(ROOTFS)/root/app
LINUX_ZIMAGE=hypervisor/guests/linux/build/zImage.bin
HYP_CML=hypervisor/guests/trusted/build/trusted.bin
HYP_OUT=hypervisor/core/build/sth_beaglebone.fw.img

.PHONY: all
all: $(HYP_OUT)

# prepare dependencies

BUILDROOT=buildroot-2021.02.8
LINUX_KERNEL=linux-5.15.13
LINUX_KERNEL_TAR=$(LINUX_KERNEL).tar.xz

.PHONY: deps
deps: lib/cake32 lib/cake64 $(BUILDROOT) $(LINUX_KERNEL_TAR)

lib/cake%:
	$(MAKE) -C lib

$(BUILDROOT):
	curl --location --silent --continue-at - --output "$(BUILDROOT).tar.gz" \
		"https://buildroot.org/downloads/$(BUILDROOT).tar.gz"
	tar -zxf "$(BUILDROOT).tar.gz"

$(LINUX_KERNEL_TAR):
	curl --location --silent --continue-at - --output $@ \
		"https://cdn.kernel.org/pub/linux/kernel/v5.x/"$@

$(BUILDROOT)/.config: | $(BUILDROOT) $(LINUX_KERNEL_TAR)
	cp sources/buildroot-config $(BUILDROOT)/.config
	sed -i 's|@@LINUX_SRC_PATH@@|'"$(PWD)/$(LINUX_KERNEL_TAR)"'|g' $(BUILDROOT)/.config

$(BUILDROOT)/output/host/bin/arm-linux-gcc : | $(BUILDROOT)/.config
	$(MAKE) ARCH=arm -C $(BUILDROOT)

.PHONY: runserial
## serial console for UART (exit with C-c to save output)
runserial:
	env PS1="> " tmux -f /dev/null \
		new-session -s "runserial" \
			"printf '\033]2;seriallog\033\\'; \
				$(shell which python3 || which python) \
					-m serial.tools.miniterm /dev/ttyUSB0 115200 --filter colorize " \; \
		set-option status off\; \
		set -g automatic-rename on \; \
		set -g automatic-rename-format "#T" \; \
		set -g remain-on-exit on \; \
		bind-key -n C-c "run-shell 'tmux capture-pane -t #{pane_title} -p -S - -E - -C \
			> #{pane_title}-$(git rev-parse --short HEAD)-$(shell date +'%Y%m%d%H%M').log'; killp" \; \

# Full build

$(ROOTFS):
	mkdir -p "$@"

$(ROOTFS)/root: | $(ROOTFS)
	cd "$(ROOTFS)" && \
		$(SUDO) cpio -i -d -H newc -F ../linux-5.15.13/rootfs.cpio --no-absolute-filenames
	$(SUDO) chown $(USER):$(USER) "$(ROOTFS)" -R
	cp sources/S60confnet.sh "$(ROOTFS)/etc/init.d/"
	chmod +x "$(ROOTFS)/etc/init.d/S60confnet.sh"

# build the rust program

ifndef TEST_rs
RUST_DEPS=$(shell find $(VCSDIR)/rust_app_lib -type f -name "*.rs")

$(HYP_RS): $(RUST_DEPS) | $(ROOTFS)/root
	@echo
	@echo "build tevd rust program"
	$(MAKE) -C $(VCSDIR)/crosscompile out/server
	cp $(VCSDIR)/crosscompile/out/server $@
else
RUST_DEPS=\
	hypervisor-cakeml/linuxapp/rust_app.rs \
	hypervisor-cakeml/cakeml/basis_ffi.c \
	hypervisor-cakeml/cakeml/start.S \

$(HYP_RS): $(RUST_DEPS) | $(ROOTFS)/root
	@echo
	@echo "build simple rust program"
	cd hypervisor-cakeml/linuxapp && \
		$(TOOLCHAIN)gcc -static -c invoke_cakeml.c -o invoke_cakeml.o
	cd hypervisor-cakeml/linuxapp && \
		$(TOOLCHAIN)ar rcs libinvoke_cakeml.a invoke_cakeml.o
	cd hypervisor-cakeml/linuxapp && \
		rustc --target=armv7-unknown-linux-gnueabihf -Clinker=$(TOOLCHAIN)gcc -Ctarget-feature=+crt-static -L . rust_app.rs -o $@
endif

# build the cakeml program

ifndef TEST_cml
CML_DEPS= \
	$(VCSDIR)/crosscompile/cake_guest.ld \
	$(VCSDIR)/crosscompile/start.S \

$(HYP_CML): $(CML_DEPS)
	@echo
	@echo "build tevd cakeml program"
	$(MAKE) -C $(VCSDIR)/crosscompile NO_CRYPTO=1 WOLFSSL=1 tevdProg tevdProg.bin
	cp $(VCSDIR)/crosscompile/tevdProg.bin $@
else
$(HYP_CML): hypervisor-cakeml/cakeml/trusted.cml lib/cake32
	@echo
	@echo "build simple cakeml program"
	sh compile_cakeml.sh
	cp hypervisor-cakeml/cakeml/trusted.bin $@
endif

# build linux

$(LINUX_ZIMAGE): $(HYP_RS)
	@echo
	@echo "build linux"
	cp sources/hypervisor.linux-config linux-5.15.13/.config
	cd linux-5.15.13/ && \
		$(MAKE) oldconfig ARCH=arm CC=arm-linux-gnueabihf-gcc CROSS_COMPILE=arm-linux-gnueabihf-
	cd linux-5.15.13/ && \
		$(MAKE) ARCH=arm CC=arm-linux-gnueabihf-gcc CROSS_COMPILE=arm-linux-gnueabihf- -j8
	cat linux-5.15.13/arch/arm/boot/zImage \
			linux-5.15.13/arch/arm/boot/dts/am335x-boneblack.dtb \
			> $(LINUX_ZIMAGE)

# build the hypervisor

HYP_DEPS= \
	hypervisor/core/hypervisor/handlers.c \
	hypervisor/core/hypervisor/guest_config/linux_config.c \

ifndef DOCKER_RUNNING
$(HYP_OUT): $(LINUX_ZIMAGE) $(HYP_CML) $(HYP_DEPS)
	@echo
	@echo "build hypervisor"
	docker run --rm -v ./hypervisor:/usr/src/myapp -w /usr/src/myapp -it xenialarmgnueabigcc4.7 make
else
$(HYP_OUT): $(LINUX_ZIMAGE) $(HYP_CML) $(HYP_DEPS)
	@echo
	@echo "cannot build the hypervisor from within this docker container"
	@echo "run make in  ./hypervisor  directory within the container xenialarmgnueabigcc4.7"
	@echo "	docker run --rm -v ./hypervisor:/usr/src/myapp -w /usr/src/myapp -it xenialarmgnueabigcc4.7 make"
	@echo
	@exit 1
endif

TARFLAGS= \
	--sort=name --format=posix \
	--pax-option='exthdr.name=%d/PaxHeaders/%f' \
	--pax-option=delete=atime,delete=ctime \
	--clamp-mtime --mtime='@0' \
	--numeric-owner --owner=0 --group=0 \
	--mode=go+u,go-w \

GZIPFLAGS=--no-name --best

TEVD_ARCHIVE_FILE=tevd.tar.gz

# https://www.gnu.org/software/tar/manual/html_section/Reproducibility.html
# excludes paper draft in doc
$(TEVD_ARCHIVE_FILE):
	env LC_ALL=C tar $(TARFLAGS) --exclude-vcs \
		--exclude='*.tar.*' \
		--exclude='doc' \
		-cf - -C $(HYP_ROOT) . | \
		gzip $(GZIPFLAGS) > $@

.PHONY: clean
clean:
	rm $(LINUX_ZIMAGE) $(HYP_CML) $(HYP_RS) $(HYP_OUT)
	@echo "Should the preceeding command fail with 'Permission denied'"
	@echo "rerun make with the flag  --dry-run  and remove the files"
	@echo "manually with administrator access."

