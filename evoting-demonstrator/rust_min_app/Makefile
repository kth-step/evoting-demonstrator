
.PHONY: all
all: emulation

.PHONY: emulation
emulation:
	cargo rustc --features=emulation --bin=server \
		--target-dir=emulation \
		-- -L $(VCSDIR)/emulation -l invoke_cakeml

