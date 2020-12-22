# Variables, set with ``make x='e'``
#  build : build directory
#  dc : d compiler
#  dflags : compiler flags
#  dformatter : formatter
#  dformatter_flags : formatter flags
#  python : python interpreter
#  no_objects : if true then compile everything at once



build := build
dc = $(shell which dmd || which ldc2 || which ghc2)
dflags =
dformatter = dfmt
dformatter_flags = --inplace --brace_style=otbs --indent_style=tab --soft_max_line_length=65535 --max_line_length=65535
python = $(shell which python3 || which python)
no_objects = false


dc := $(dc)
python := $(python)

.SECONDEXPANSION:

find = $(wildcard $1/*.$2) $(foreach directory,$(wildcard $1/*),$(call find,$(directory),$2))
hash = $(shell $(python) -c "import hashlib; print(hashlib.sha256('$1'.encode('utf-8')).hexdigest())")

ifeq '$(dc)' 'gdc'
-o = -o 
else
-o = -of
endif
-I = -I
-c = -c

$(build)/aith:

%/:
	mkdir -p $@
.PRECIOUS: %/

# hack to check compiler flags
flags := $(build)/flags/$(call hash,$(dc) $(dflags))
$(flags): | $$(dir $$@)
	$(foreach old,$(wildcard $(build)/flags/*),rm $(old))
	touch $@

sources := $(call find,source,d)

ifeq 'false' '$(no_objects)'
objects := $(sources:%.d=$(build)/%.o)
$(objects) : $(build)/%.o : %.d $(sources) $(flags)
	$(dc) $(dflags) $(-o)$@ $< $(-c) $(-I)source


$(build)/aith: $(objects) $(flags) | $$(dir $$)
	$(dc) $(dflags) $(-o)$@ $(objects)
else ifeq 'true' '$(no_objects)'
$(build)/aith : $(sources) $(flags) | $$(dir $$)
	$(dc) $(dflags) $(-o)$@ $(sources)
endif

test := $(call find,test,aith)
test_output := $(test:%.aith=$(build)/%.js)
$(test_output): $(build)/%.js : %.aith runtime/builtin.aith runtime/runtime.js runtime/main.js $(build)/aith | $$(dir $$@)
	$(build)/aith --builtin runtime/builtin.aith runtime/runtime.js $< runtime/main.js -o $@
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
