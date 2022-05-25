# configuration flags

# build directory, inside dist-newstyle by default to avoid 2 build directories
build:=dist-newstyle/aith
# limit memory usage to 64 mb incase compiler explodes
aith_flags:=+RTS -M67108864 -K67108864 -RTS
# copy / link command 
cp:=cp -l

find=$(wildcard $1/*.$2) $(foreach directory,$(wildcard $1/*),$(call find,$(directory),$2))
source:=$(call find,source,hs)

.SECONDEXPANSION:

%/:
	mkdir $@ -p

aith: $(source) cabal.project cabal.project.local aith.cabal
	cabal build aith
	rm -f aith
	$(cp) "$$(cabal exec which aith)" aith
	touch aith

cabal.project.local:
	touch $@

format:=$(source:%.hs=$(build)/format/%.format) 
.PHONY: format
format : $(format)
$(format) : $(build)/format/%.format : %.hs | $$(dir $$@)
	ormolu -o -XTypeApplications -i $<
	touch $@

test.c: test.aith aith
	./aith $(aith_flags) $< -C -o $@

.PHONY: tests
tests: $(build)/test/idempotency

$(build)/test/format1.aith: test.aith aith | $$(dir $$@)
	./aith $(aith_flags) $< --format -o $@
$(build)/test/annotate1.aith: test.aith aith | $$(dir $$@)
	./aith $(aith_flags) $< --annotate -o $@
$(build)/test/reduce1.aith: test.aith aith | $$(dir $$@)
	./aith $(aith_flags) $< --reduce -o $@

$(build)/test/format2.aith : $(build)/test/format1.aith aith | $$(dir $$@)
	./aith $(aith_flags) $< --format -o $@
$(build)/test/annotate2.aith : $(build)/test/annotate1.aith aith | $$(dir $$@)
	./aith $(aith_flags) $< --annotate -o $@
$(build)/test/reduce2.aith : $(build)/test/reduce1.aith aith | $$(dir $$@)
	./aith $(aith_flags) $< --reduce -o $@

idempotency_format:=$(build)/test/format1.aith $(build)/test/format2.aith
idempotency_annotate:=$(build)/test/annotate1.aith $(build)/test/annotate2.aith 
idempotency_reduce:=$(build)/test/reduce1.aith $(build)/test/reduce2.aith

$(build)/test/idempotency: $(idempotency_format) $(idempotency_annotate) $(idempotency_reduce) | $$(dir $$@)
	diff $(idempotency_format)
	diff $(idempotency_annotate)
	diff $(idempotency_reduce)
	touch $@
