.SECONDEXPANSION:


#variables to change from commandline

APP = typi
DC ?= ldc2
MKDIR = mkdir
LN = ln -fs
RM = rm -rf

$(APP):

FIND = $(shell find $1 -name "*.$2")
HASH = $(shell echo $1 | md5sum | cut -d ' ' -f 1)

DFLAGS ?=
DLDFLAGS ?=

#hack to check compiler flags
LINK_HASH := .$(call HASH,$(DC) $(DFLAGS) $(DLDFLAGS))

SOURCES := $(call FIND,source,d)

FORMAT := $(SOURCES:%=build/%.format)

SAMPLES := $(call FIND,samples,typi)
SAMPLES_OUTPUT := $(SAMPLES:%.typi=build/%.js)

%/:
	$(MKDIR) -p $@
.PRECIOUS: %/

BUILD_APP := build/$(APP)$(LINK_HASH)

$(APP): $(BUILD_APP)
	$(LN) $< $@
.PHONY: $(APP)

$(BUILD_APP): $(SOURCES) | $$(dir build/%)
	$(DC) $(DFLAGS) $(DLDFLAGS) -of$@ $^

$(SAMPLES_OUTPUT): build/samples/%.js : samples/%.typi samples/%.js lib/typi.js $(BUILD_APP) | $$(dir build/samples/%)
	$(BUILD_APP) -I samples $(notdir $<) lib/typi.js $(word 2,$^) -o $@

$(FORMAT): build/%.format : % | $$(dir build/%)
	dfmt --inplace --brace_style=otbs --indent_style=tab $<
	touch $@

samples: $(SAMPLES_OUTPUT)

format: $(FORMAT)

clean:
	$(RM) -rf build $(APP)

.PHONY: samples format clean

