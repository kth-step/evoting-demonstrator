
ifndef VCSDIR
$(error VCSDIR is not set)
endif

ifndef CAKEDIR
$(error CAKEDIR is not set)
endif

LOG_DATE=$(shell date +'%Y%m%d%H%M')
CAKE64=$(CAKEDIR)/cake64

BASIS_FFI_EMULATION:= basis_ffi_emulation.c

# keep intermediate output
.PRECIOUS: %.S %.cml %.sexp ffiext.cake ffiext.cml \
	tevdProg tevdProg.S

HOL_EXTRACT_DIR=../src/tevd/cakeml/
HOL_EXTRACT_FILE=tevdProg.sexp

# allows invocation of either
#   env RUSTNAME=rust_min_app make
# or only
#   make
RUSTNAME ?= rust_app_lib
RUSTLIB_NAME=lib$(RUSTNAME).a
RUST_DEV_PATH=../$(RUSTNAME)/
RUSTLIB_EMULATION_PATH=$(RUST_DEV_PATH)/emulation/debug/
RUSTLIB_PATH=$(RUST_DEV_PATH)/target/debug/


RUSTLIB_CRYPTO_CRATE_PATH=$(VCSDIR)/rust_crypto_lib/
RUSTLIB_CRYPTO_PATH=$(RUSTLIB_CRYPTO_CRATE_PATH)/target/release/
#RUSTLIB_CRYPTO_PATH=$(RUSTLIB_CRYPTO_CRATE_PATH)/target/debug/
RUSTLIB_CRYPTO_NAME=rust_crypto_lib
RUSTLIB_CRYPTO_FILE=lib$(RUSTLIB_CRYPTO_NAME).a

RUST_FILES:=$(shell find $(RUST_DEV_PATH)/src -type f -iname "*.rs")
RUSTCRYPTO_FILES:=$(shell find $(RUSTLIB_CRYPTO_CRATE_PATH)/src -type f -iname "*.rs")

# show static link dependencies
# cd $RUSTLIB_PATH
# cargo rustc --lib -- --print native-static-libs
NATIVE_LIBS= -lgcc_s -lutil -lrt -lpthread -lm -ldl -lc

args := \
	--node    vcs:192.100.1.2:8080 \
	--node  admin:127.0.0.1:8081 \
	--node mixnet:127.0.0.1:8082\
	--node client:127.0.0.1:8083 \
	-v -v -v -v -v -v

ifdef LOCAL
# for local runs
args := \
	--node    vcs:127.0.0.1:8080 \
	--node  admin:127.0.0.1:8081 \
	--node mixnet:127.0.0.1:8082\
	--node client:127.0.0.1:8083 \
	-v -v -v -v -v -v
endif

.PHONY: all
all: emulation

emulation: emulation.c cake_app rust_app
	gcc $< -o $@

.PHONY: run_vcs
run_vcs: emulation
	./$< vcs $(args)

.PHONY: run_admin
run_admin: emulation
	./$< admin --socket /tmp/admin.sock $(args)

.PHONY: run_client
run_client: emulation
	./$< client --socket /tmp/client.sock $(args)

.PHONY: demo
demo: emulation
	env PS1="> " tmux \
		new-session -s "demo" \
			"printf '\033]2;vcs\033\\'; make run_vcs" \; \
		set-hook -g after-split-window "selectl even-vertical" \; \
		split-window "printf '\033]2;admin\033\\';  make run_admin" \; \
		split-window "printf '\033]2;client\033\\'; make run_client" \; \
		set-option status off\; \
		set -g automatic-rename on \; \
		set -g automatic-rename-format "#T" \; \
		set -g remain-on-exit on \; \
		bind-key -n C-c "run-shell 'tmux capture-pane -t #{pane_title} -p -S - -E - -C \
			> #{pane_title}--$(LOG_DATE).log'; killp" \; \

.PHONY: bbb
bbb: emulation
	env PS1="> " tmux \
		new-session -s "demo" \
			"printf '\033]2;admin\033\\';  make run_admin" \; \
		set-hook -g after-split-window "selectl even-vertical" \; \
		split-window "printf '\033]2;client\033\\'; make run_client" \; \
		split-window "printf '\033]2;client-server\033\\'; \
			cd ../rust_client_server; \
			SERVER_ADDRESS=127.0.0.1:7878 cargo run " \; \
		set-option status off\; \
		set -g automatic-rename on \; \
		set -g automatic-rename-format "#T" \; \
		set -g remain-on-exit on \; \
		bind-key -n C-c "run-shell 'tmux capture-pane -t #{pane_title} -p -S - -E - -C \
			> #{pane_title}--$(LOG_DATE).log'; killp" \; \


%: %.S $(BASIS_FFI_EMULATION) $(RUSTLIB_CRYPTO_FILE)
	$(CC) -D EMULATE_HYPERVISOR $(BASIS_FFI_EMULATION) $< -o $@ \
		-L. -l$(RUSTLIB_CRYPTO_NAME) \
		$(NATIVE_LIBS)

%.S: %.cml
	$(CAKE64) <$< >$@

%.S: %.sexp
	$(CAKE64) \
		--exclude_prelude=true \
		--sexp=true \
		< $< > $@

%.sexp: %Script.sml
	$(HOLDIR)/bin/Holmake

$(HOL_EXTRACT_DIR)/$(HOL_EXTRACT_FILE): $(HOL_EXTRACT_DIR)/TevDNetworkedSystemProgScript.sml $(HOL_EXTRACT_DIR)/../hol/TevDNetworkedSystemScript.sml
	cd $(HOL_EXTRACT_DIR) && $(HOLDIR)/bin/Holmake

tevdProg.sexp: $(HOL_EXTRACT_DIR)/tevdProg.sexp
	ln -sf $< $@

rust_app: $(RUSTLIB_EMULATION_PATH)/server
	ln -sf $< $@

cake_app: tevdProg
	ln -sf $< $@

invoke_cakeml.o: invoke_cakeml.c
	$(CC) -D EMULATE_HYPERVISOR -static -c $< -o $@

libinvoke_cakeml.a: invoke_cakeml.o
	ar rcs $@ $<

$(RUSTLIB_EMULATION_PATH):
	mkdir -p $@

$(RUSTLIB_EMULATION_PATH)/server: libinvoke_cakeml.a $(RUST_FILES) | $(RUSTLIB_EMULATION_PATH)
	cd $(RUST_DEV_PATH) && \
		cargo rustc --features=emulation --bin=server \
			--target-dir=emulation \
			-- -L $(VCSDIR)/emulation -l invoke_cakeml

$(RUSTLIB_CRYPTO_PATH)/$(RUSTLIB_CRYPTO_FILE): $(RUSTCRYPTO_FILES)
	cd "$(RUSTLIB_CRYPTO_CRATE_PATH)" && \
		cargo rustc --lib --release

$(RUSTLIB_CRYPTO_FILE): $(RUSTLIB_CRYPTO_PATH)/$(RUSTLIB_CRYPTO_FILE)
	ln -sf $< $@

.PHONY: clean
clean:
	-rm \
		$(RUSTLIB_EMULATION_PATH)/server \
		invoke_cakeml.o libinvoke_cakeml.a \
		emulation rust_app cake_app \

.PHONY: cleanlogs
cleanlogs:
	-rm {admin,client,vcs,mixnet}--*.log

