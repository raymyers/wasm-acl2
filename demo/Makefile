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

.PHONY: all check jscl-hello wabt-hello browser-hello extract check-extract js vectors units host conformance-data conformance conformance-quick clean

all: $(BUILD)/hello.js js

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

# W3: shim + extracted semantics -> $(BUILD)/wasm3.js (num.js and list.js first:
# the number tower and list primitives that the shim initializes). Needs `extract`.
SHIM := shim/acl2.lisp shim/rule.lisp
GLUE := driver/glue.lisp
js: extract $(BUILD)/jscl.js
	IN="$(SHIM) $$(sed 's|^|$(LISP)/|' $(LISP)/ORDER | tr '\n' ' ') $(GLUE)" OUT=$(BUILD)/wasm3-core.js \
	  $(JSCL_XC) --non-interactive --load shim/compile.lisp > $(BUILD)/wasm3.log 2>&1 \
	  || { grep -v '^loading' $(BUILD)/wasm3.log | sed -n '/^Backtrace/q;p' | tail -30; exit 1; }
	@grep 'DEMO-COMPILE\|is undefined' $(BUILD)/wasm3.log | sort | uniq
	cat shim/num.js shim/list.js driver/host.js $(BUILD)/wasm3-core.js > $(BUILD)/wasm3.js
	@ls -l $(BUILD)/wasm3.js | awk '{print "wasm3.js", $$5, "bytes"}'

# W3: a test bundle per ACL2 test book: shim + books (without driver.lisp,
# whose helper names the test books reuse) + the book's checking functions.
BOOKS = $$(grep -v '^driver.lisp$$' $(LISP)/ORDER | sed 's|^|$(LISP)/|' | tr '\n' ' ')
$(BUILD)/test-%.js: js
	IN="$(SHIM) $(BOOKS) $(LISP)/tests/$*.lisp test/vectors-glue.lisp" OUT=$(BUILD)/test-$*-core.js \
	  $(JSCL_XC) --non-interactive --load shim/compile.lisp > $(BUILD)/test-$*.log 2>&1 \
	  || { grep -v '^loading' $(BUILD)/test-$*.log | sed -n '/^Backtrace/q;p' | tail -30; exit 1; }
	@grep 'is undefined' $(BUILD)/test-$*.log | grep -v HOSTCALL-HOOK | sort | uniq || true
	cat shim/num.js shim/list.js $(BUILD)/test-$*-core.js > $@

# W3 item 3: shim unit tests (shim only, expected values printed by ACL2)
$(BUILD)/test-units.js: js
	IN="$(SHIM) test/units-pkg.lisp $(LISP)/tests/units.lisp" OUT=$(BUILD)/test-units-core.js \
	  $(JSCL_XC) --non-interactive --load shim/compile.lisp > $(BUILD)/test-units.log 2>&1 \
	  || { grep -v '^loading' $(BUILD)/test-units.log | sed -n '/^Backtrace/q;p' | tail -30; exit 1; }
	cat shim/num.js shim/list.js $(BUILD)/test-units-core.js > $@
units: $(BUILD)/test-units.js
	$(NODE) test/units.js $(BUILD)

# W3 item 2: numeric (8,724) and SIMD (1,008) vectors, as the ACL2 books check them
vectors: $(BUILD)/test-numerics.js $(BUILD)/test-simd.js
	$(NODE) test/vectors.js $(BUILD) numerics
	$(NODE) test/vectors.js $(BUILD) simd

# W4 item 2: host imports through %HOSTCALL-HOOK (a JS host function)
host: js
	$(NODE) test/host.js $(BUILD)

# W4 item 3: the spec-test-3 subset, command by command against ACL2's
# results-3.0/ (gitignored: `make -C translate spec-data SPEC=3.0` and
# `make -C translate spec SPEC=3.0`, about 11 min). `conformance` is the whole
# subset (about 25 min, most of it call_indirect, which ACL2 does not finish
# either); `conformance-quick` (in `check`) leaves call_indirect out.
CONF_QUICK := i32 i64 f32 f64 memory br_table simd--simd_i32x4_arith simd--simd_lane gc--struct gc--i31 exceptions--try_table
CONF_ALL   := $(CONF_QUICK) call_indirect
conformance-data:
	@for n in $(CONF_ALL); do test -f $(SPECDIR)/results-3.0/$$n.out && test -f $(SPECDIR)/data-3.0/$$n.lsp \
	  || { echo "conformance: $(SPECDIR)/results-3.0/$$n.out or data-3.0/$$n.lsp missing (make -C translate spec-data spec SPEC=3.0)"; exit 1; }; done
conformance: js conformance-data
	$(NODE) test/conformance.js $(BUILD) $(SPECDIR)/data-3.0 $(SPECDIR)/results-3.0 $(CONF_ALL)
conformance-quick: js conformance-data
	$(NODE) test/conformance.js $(BUILD) $(SPECDIR)/data-3.0 $(SPECDIR)/results-3.0 $(CONF_QUICK)

check: jscl-hello wabt-hello browser-hello check-extract vectors units host conformance-quick

clean:
	rm -r -f build
