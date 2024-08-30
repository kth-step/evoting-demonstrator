
ifndef CAKEDIR
$(error environment variable CAKEDIR need to be set)
endif

CAKE=$(CAKEDIR)/cake64
BASIS=$(CAKEDIR)/basis_ffi.c

%.cml: %Module.cml %Prog.cml
	cat $^ > $@

%.cake.S : %.cml
	$(CAKE) $(CAKEFLAGS) <$< >$@

% : %.S
	$(CC) $(LDFLAGS) $^ $(BASIS) $(LOADLIBES) $(LDLIBS) -o $@

