#Environment variables:
# dc : d compiler
# dflags : compiler flags
# dformatter : formatter
# dformatter_flags : formatter flags
# build : build directory
# incremental : if true then do incremental build

dc ?= ldc2
dflags ?=
dformatter ?= dfmt
dformatter_flags ?= --inplace --brace_style=otbs --indent_style=tab
build ?= build
incremental ?= false


.SECONDEXPANSION:

find = $(wildcard $1/*.$2) $(foreach directory,$(wildcard $1/*),$(call find,$(directory),$2))
hash = $(shell echo $1 | md5sum | cut -d ' ' -f 1)

ifeq ($(dc),gdc)
-o = -o 
else
-o = -of
endif
-I = -I
-c = -c


$(build)/typi:

%/:
	mkdir -p $@
.PRECIOUS: %/

#hack to check compiler flags
flags := $(build)/flags/$(call hash,$(dc) $(dflags))
$(flags): | $$(dir $$@)
	$(foreach old,$(wildcard $(build)/flags/*),rm $(old))
	touch $@

sources := $(call find,source,d)
ifeq ($(incremental),true)
objects = $(sources:%.d=$(build)/%.o)
$(objects) : $(build)/%.o : %.d $(flags)
	$(dc) $(dflags)  $(-o)$@ $< $(-c) $(-I)source


$(build)/typi: $(objects) $(flags) | $$(dir $$)
	$(dc) $(dflags) $(-o)$@ $(objects)
else
$(build)/typi : $(sources) $(flags) | $$(dir $$)
	$(dc) $(dflags) $(-o)$@ $(sources)
endif
test := $(call find,test,typi)
test_output := $(test:%.typi=$(build)/%.js)
$(test_output): $(build)/%.js : %.typi runtime/runtime.js $(build)/typi | $$(dir $$@)
	$(build)/typi $< runtime/runtime.js -o $@
test_build : $(test_output)
.PHONY: test_build

test_run := $(test_output:%=%.run)
$(test_run): %.run : %
	node $<
	touch $@
test: $(test_run)
.PHONY: test

format := $(sources:%=$(build)/%.format)
$(format): $(build)/%.format : % | $$(dir $$@)
	$(dformatter) $(dformatter_flags) $<
	touch $@
format: $(format)
.PHONY: format
