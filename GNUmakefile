.SECONDEXPANSION:

DC ?= gdc
DFLAGS ?=
DLDFLAGS ?=
DFORMATTER ?= dfmt --inplace --brace_style=otbs --indent_style=tab

ifeq ($(DC),gdc)
OUTPUT_FLAG = -o 
else
OUTPUT_FLAG = -of
endif
BUILD_DIR ?= build/

APP := $(BUILD_DIR)typi

$(APP):

%/:
	mkdir -p $@
.PRECIOUS: %/

FIND = $(wildcard $1/*.$2) $(foreach directory,$(wildcard $1/*),$(call FIND,$(directory),$2))
HASH = $(shell echo $1 | md5sum | cut -d ' ' -f 1)

SOURCES := $(call FIND,source,d)

FORMAT := $(SOURCES:%=$(BUILD_DIR)%.format)


#hack to check compiler flags
LINK_HASH := $(BUILD_DIR)$(call HASH,$(DC) $(DFLAGS) $(DLDFLAGS)).flags
$(LINK_HASH): | $$(dir $$@)
	$(if $(wildcard $(BUILD_DIR)*.flags),rm $(wildcard $(BUILD_DIR)*.flags))
	touch $@

$(APP): $(LINK_HASH) $(SOURCES) | $$(dir $$@)
	$(DC) $(DFLAGS) $(DLDFLAGS) $(OUTPUT_FLAG)$@ $(SOURCES)

UNITTEST := $(call FIND,unittest,typi)
UNITTEST_OUTPUT := $(UNITTEST:%.typi=$(BUILD_DIR)%.js)
UNITTEST_RUN := $(UNITTEST_OUTPUT:%=%.run)
$(UNITTEST_OUTPUT): $(BUILD_DIR)%.js : %.typi unittest/runtime.js $(APP) | $$(dir $$@)
	$(APP) $< $(word 2,$^) -o $@

$(UNITTEST_RUN): %.run : %
	node $<
	touch $@
$(FORMAT): $(BUILD_DIR)%.format : % | $$(dir $$@)
	$(DFORMATTER) $<
	touch $@

build_unittest: $(UNITTEST_OUTPUT)

run_unittest: $(UNITTEST_RUN)

format: $(FORMAT)

.PHONY: unittest format

