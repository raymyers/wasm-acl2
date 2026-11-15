# WASM 3.0 in the browser (plan/wasm3-demo). Separate from translate/Makefile:
# no ACL2 target depends on this one. Run inside `nix develop`.

BUILD   := build
JSCL_XC ?= jscl-xc
NODE    ?= node

.PHONY: all check jscl-hello wabt-hello browser-hello clean

all: $(BUILD)/hello.js

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

check: jscl-hello wabt-hello browser-hello

clean:
	rm -r -f build
