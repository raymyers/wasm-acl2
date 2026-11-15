# WASM 3.0 in the browser (plan/wasm3-demo). Separate from translate/Makefile:
# no ACL2 target depends on this one. Run inside `nix develop`.

BUILD   := build
JSCL_XC ?= jscl-xc
NODE    ?= node
# The generated 3.0 semantics (not checked in): `make -C translate check-3.0`
# or `make -C translate gen SPEC=3.0` regenerates it.
GEN     ?= ../translate/gen/wasm-3.0
SPECDIR ?= ../translate/tests/spec
LISP    := $(BUILD)/lisp

.PHONY: all check jscl-hello wabt-hello browser-hello extract check-extract clean

all: $(BUILD)/hello.js extract

$(BUILD)/jscl.js: $(JSCL_HOME)/dist/jscl.js
	@mkdir -p $(BUILD)
	cp $< $@ && chmod u+w $@

$(BUILD)/hello.js: hello/hello.lisp hello/build.lisp $(BUILD)/jscl.js
	IN=$< OUT=$@ $(JSCL_XC) --non-interactive --load hello/build.lisp > $(BUILD)/hello.log 2>&1 \
	  || { tail -30 $(BUILD)/hello.log; exit 1; }

# W0 item 1: compile one Lisp file and run it in node.
jscl-hello: $(BUILD)/hello.js
	@out=$$(cd $(BUILD) && $(NODE) hello.js | tail -1); echo "$$out"; \
	  test "$$out" = "hello from JSCL: 3"

# W0 item 1: the same file in headless Chromium and Firefox. SHOT=<png>
# writes the progress screenshot.
browser-hello: $(BUILD)/hello.js
	$(NODE) test/browser-hello.mjs

wabt-hello:
	$(NODE) test/wabt-hello.mjs

# W2: the books, rt/ and the driver helpers -> $(LISP)/ (REPORT, ORDER, NN-*.lisp).
extract:
	sh extract/run.sh $(GEN) $(SPECDIR) $(LISP)

# W2 item 3: two runs are byte-identical, and translate/ is untouched.
check-extract:
	rm -r -f $(BUILD)/lisp-a $(BUILD)/lisp-b
	sh extract/run.sh $(GEN) $(SPECDIR) $(BUILD)/lisp-a > /dev/null
	sh extract/run.sh $(GEN) $(SPECDIR) $(BUILD)/lisp-b > /dev/null
	diff -r -x extract.log $(BUILD)/lisp-a $(BUILD)/lisp-b
	@echo "check-extract: two runs identical ($$(ls $(BUILD)/lisp-a | wc -l | tr -d ' ') files)"
	@test -z "$$(git status --porcelain ../translate)" || { git status --short ../translate; echo "check-extract: translate/ changed"; exit 1; }

check: jscl-hello wabt-hello browser-hello check-extract

clean:
	rm -r -f build
