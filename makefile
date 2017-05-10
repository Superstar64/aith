.SECONDEXPANSION:

DC ?= ldc2
DFLAGS ?=
DLDFLAGS ?=
DFORMATTER ?= dfmt --inplace --brace_style=otbs --indent_style=tab

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
	$(DC) $(DFLAGS) $(DLDFLAGS) -of$@ $(filter-out $<,$^)

SAMPLES := $(call FIND,samples,typi)
SAMPLES_OUTPUT := $(SAMPLES:%.typi=$(BUILD_DIR)%.js)

$(SAMPLES_OUTPUT): $(BUILD_DIR)%.js : %.typi %.js lib/typi.js $(APP) | $$(dir $$@)
	$(APP) -I samples $(notdir $<) lib/typi.js $(word 2,$^) -o $@

$(FORMAT): $(BUILD_DIR)%.format : % | $$(dir $$@)
	$(DFORMATTER) $<
	touch $@

samples: $(SAMPLES_OUTPUT)

format: $(FORMAT)

.PHONY: samples format

