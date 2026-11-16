# Deterministic SpecTec -> ACL2 translation of WASM 1.0 (and, in preparation,
# 2.0 and 3.0: plan/wasm3-translation-prep). See ../plan/wasm1-translation/plan.md.
# Independent of the WASM1 tree in ..
#
# Run inside `nix develop ..` (provides ACL2, CERT and nix).
#
# SPEC=1.0|2.0|3.0 selects the spec version (default 1.0): the IL
# il/wasm-<v>.il.sexp, the config config/wasm-<v>.lsp, the output directory
# gen/wasm-<v>/, the book wasm<major>.lisp and the package W<major>T.
# gen/ is checked in for 1.0 only; 2.0 and 3.0 are rebuilt by their gates.
#
#   make il          regenerate il/wasm-<v>.il.sexp via Nix (pinned SpecTec)
#   make check-il    fail if the checked-in IL differs from a fresh regeneration
#   make gen         run the translator: il/ + config/ -> gen/wasm-<v>/
#   make check-gen   fail unless two fresh translator runs agree with gen/wasm-<v>/
#   make vectors     regenerate tests/sem/numeric-vectors.lsp (WASM engine oracle)
#                    (node tests/oracle/gen-simd-vectors.mjs 3.0 > tests/sem-3.0/simd-vectors-3.0.lsp: 3.0 SIMD)
#   make invoke-vectors  regenerate tests/sem/invoke-vectors.lsp (V8 runs the corpus exports)
#   make test        certify the translator, gen/, rt/ and every test book
#   make compare     T9 reports: run the WASM1 tree on the same oracle vectors
#   make spec-data   fetch the conformance data (Nix): 1.0 into tests/spec/data, else tests/spec/data-<v>
#   make spec        T7 report: run spec-test-1 on the generated semantics (slow;
#                    SPEC=3.0: spec-test-3 with the 3.0 driver)
#   make decode SPEC=3.0  decode every spec-test module with the generated parser (slow)
#   make probe SPEC=3.0  probe table for one spec version (plan/wasm3-translation-prep P0)
#   make modes       rewrite gen/wasm-1.0/modes.lsp from certified books (t0-modes checks it)
#   make check       check-il + check-gen + test (1.0)
#   make check-2.0   2.0 gate: regenerate, certify, run the 2.0 numeric and SIMD vectors
#   make check-3.0   3.0 gate: regenerate, certify (logic mode, timed), run the 3.0 tests and the mode manifest

NIX  ?= nix
ACL2 ?= acl2
CERT ?= $(ACL2_SYSTEM_BOOKS)/build/cert.pl
JOBS ?= 4
SPEC ?= 1.0
SPEC_MAJOR := $(firstword $(subst ., ,$(SPEC)))
PKG    := W$(SPEC_MAJOR)T
IL     := il/wasm-$(SPEC).il.sexp
DECLS  := il/wasm-$(SPEC).decls.lsp
CONFIG := config/wasm-$(SPEC).lsp
GEN    := gen/wasm-$(SPEC)
BOOK   := wasm$(SPEC_MAJOR)
TARGET := (assign il2acl2-target (quote (:version "$(SPEC)" :pkg "$(PKG)" :il "$(IL)" :decls "$(DECLS)" :config "$(CONFIG)" :outdir "$(GEN)/" :book "$(BOOK)")))
# Everything the translator writes (one book per source file plus the top
# book $(BOOK).lisp); check-gen compares the whole set.
GEN_PATTERNS := *.lisp *.lsp *.acl2
TEST_BOOKS := $(patsubst %.lisp,%,$(wildcard tests/*.lisp tests/sem/*.lisp))

.PHONY: il check-il gen check-gen test check clean translator vectors compare corpus invoke-vectors spec-data spec probe modes check-2.0 check-3.0 decode

il:
	$(NIX) build ..#wasm$(SPEC_MAJOR)-il --no-link --print-out-paths > .il-out
	install -m 644 "$$(cat .il-out)/wasm-$(SPEC).il.sexp" $(IL)
	install -m 644 "$$(cat .il-out)/wasm-$(SPEC).decls.lsp" $(DECLS)
	rm -f .il-out

check-il:
	$(NIX) build ..#wasm$(SPEC_MAJOR)-il --no-link --print-out-paths > .il-out
	cmp "$$(cat .il-out)/wasm-$(SPEC).il.sexp" $(IL)
	cmp "$$(cat .il-out)/wasm-$(SPEC).decls.lsp" $(DECLS)
	rm -f .il-out
	@echo "IL is up to date and reproducible"

translator:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) il2acl2/emit

# The translator writes into ./gen/wasm-<v>/ relative to translate/.
gen: translator
	mkdir -p $(GEN)
	{ echo '$(TARGET)'; cat il2acl2/run.lsp; } | $(ACL2) > gen.log 2>&1 || (tail -40 gen.log; exit 1)
	@! grep -q "raw-lisp-error" gen.log || { grep -B2 -A4 "raw-lisp-error" gen.log | head -20; echo "gen: a raw Lisp error (e.g. an unreadable config); see gen.log"; exit 1; }
	@echo "$(GEN)/ regenerated (log: gen.log)"

# Regenerate twice from scratch copies and compare both with gen/wasm-<v>/.
check-gen: translator
	@set -e; for n in 1 2; do \
	  d=.check-gen-$$n; rm -rf $$d; mkdir -p $$d/$(GEN); \
	  mkdir -p $$d/il2acl2; \
	  cp -R il config rt package.lsp portcullis.acl2 portcullis.lisp cert.acl2 $$d/; \
	  cp il2acl2/*.lisp il2acl2/*.lsp il2acl2/cert.acl2 $$d/il2acl2/; \
	  (cd $$d && { echo '$(TARGET)'; cat il2acl2/run.lsp; } | $(ACL2) > gen.log 2>&1) || { tail -40 $$d/gen.log; exit 1; }; \
	  test "$$(cd $$d/$(GEN) && ls)" = "$$(cd $(GEN) && ls $(GEN_PATTERNS) 2> /dev/null | grep -v '^modes.lsp$$')" \
	    || { echo "file list of $(GEN)/ differs from a fresh run"; exit 1; }; \
	  for f in $$(cd $$d/$(GEN) && ls); do cmp $$d/$(GEN)/$$f $(GEN)/$$f; done; \
	done; rm -rf .check-gen-1 .check-gen-2
	@echo "$(GEN)/ is up to date and the translator is deterministic"

# Regenerate the numeric oracle vectors (Node/V8 runs the WASM ops).
vectors:
	node tests/oracle/gen-numeric-vectors.mjs > tests/sem/numeric-vectors.lsp

# Rebuild the binary corpus (wat2wasm of ../tests/oracle/*.wat) and V8 export lists.
corpus:
	node tests/oracle/gen-wasm-corpus.mjs

# Regenerate tests/sem/invoke-vectors.lsp (V8 invokes every export of the corpus).
invoke-vectors:
	node tests/oracle/gen-invoke-vectors.mjs

test:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) $(TEST_BOOKS)

# Rewrite gen/wasm-1.0/modes.lsp (the mode manifest that tests/sem/t0-modes
# checks) from freshly certified books. Run after an intended mode change.
modes:
ifeq ($(SPEC),3.0)
	$(CERT) --acl2 $(ACL2) -j $(JOBS) gen/wasm-3.0/wasm3 tests/sem/modes-lib
	cd tests/sem-3.0 && $(ACL2) < modes-write-3.0.lsp > modes-write.log 2>&1 || { tail -30 modes-write.log; exit 1; }
	@grep -o "modes-3.0.lsp: .*" tests/sem-3.0/modes-write.log
else
	$(CERT) --acl2 $(ACL2) -j $(JOBS) gen/wasm-1.0/wasm1 tests/sem/modes-lib
	cd tests/sem && $(ACL2) < modes-write.lsp > modes-write.log 2>&1 || { tail -30 modes-write.log; exit 1; }
	@grep -o "modes.lsp: .*" tests/sem/modes-write.log
endif

# T9 side-by-side reports (include the WASM1 tree; see the .cert.out files).
compare:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) $(patsubst %.lisp,%,$(wildcard compare/*.lisp))
	grep -h -A3 "T9 " compare/*.cert.out

# T7 conformance (not part of check: it takes long). The data is built by the
# flake from the pinned spec source; see tests/oracle/gen-spec-tests.mjs.
# 1.0 data goes to tests/spec/data (the driver's input), other versions to
# tests/spec/data-<v> (converted only; there is no 3.0 driver yet).
SPEC_DATA := tests/spec/data$(if $(filter 1.0,$(SPEC)),,-$(SPEC))
spec-data:
	$(NIX) build ..#wasm$(SPEC_MAJOR)-spec-tests --no-link --print-out-paths > .spec-out
	rm -rf $(SPEC_DATA) && mkdir -p $(SPEC_DATA)
	cp $$(cat .spec-out)/* $(SPEC_DATA)/ && chmod -R u+w $(SPEC_DATA)
	rm -f .spec-out

# Each script runs in its own ACL2 session (SPEC_JOBS at a time, at most
# SPEC_TIMEOUT seconds each); results in tests/spec/results/ (SUMMARY, TOTAL).
SPEC_JOBS ?= 8
SPEC_TIMEOUT ?= 3600
# SPEC=3.0 (wasm3 M4): the 3.0 driver t7-lib-3.0 (instantiation through the
# test-only $instantiate_unchecked), results in tests/spec/results-3.0/; a
# limit per script SPEC_TIMEOUT_3 (3,600 s; an action has its own budget of
# steps and CPU seconds in t7-lib-3.0, so a slow command fails alone).
SPEC_TIMEOUT_3 ?= 3600
spec:
ifeq ($(SPEC),3.0)
	$(CERT) --acl2 $(ACL2) tests/spec/t7-lib-3.0
	cd tests/spec && sh run-all-3.0.sh $(ACL2) $(SPEC_JOBS) $(SPEC_TIMEOUT_3)
else
	$(CERT) --acl2 $(ACL2) tests/spec/t7-lib
	cd tests/spec && sh run-all.sh $(ACL2) $(SPEC_JOBS) $(SPEC_TIMEOUT)
endif

# Decode run (wasm3 M2): every module of the converted spec-test-<major> data
# through the generated binary parser, one ACL2 session per script; results in
# tests/spec/results/decode-<v>/ (TOTALS, MISSES, PER-SCRIPT). Needs
# `make spec-data SPEC=<v>` first. Not part of check.
decode:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) $(GEN)/$(BOOK)
	sh tests/spec/decode/run-decode.sh $(ACL2) $(SPEC) $(SPEC_JOBS) $(SPEC_TIMEOUT)

# Probe (plan/wasm3-translation-prep P0): elaborate spec version SPEC with the
# pinned SpecTec into .probe/<SPEC>/ and print the probe table (schema errors,
# mangling, events, stubs by source file, error kinds). Writes nothing under
# gen/. EXCLUDE is a list of file globs to leave out, e.g. EXCLUDE='X.* 6.*'.
# PROBE_CONFIG defaults to config/wasm-<v>.lsp; PROBE_DROP lists config entry
# kinds to ignore.
EXCLUDE ?=
PROBE_DIR := .probe/$(SPEC)
PROBE_CONFIG ?= $(CONFIG)
PROBE_DROP ?=

probe: translator
	@set -e; d=$(PROBE_DIR); mkdir -p $$d; \
	sp=$$($(NIX) build ..#spectec --no-link --print-out-paths 2> /dev/null); \
	src=$$($(NIX) eval --raw --impure --expr \
	  '(builtins.getFlake (toString ./..)).inputs.wasm-spec.outPath' 2> /dev/null)/specification/wasm-$(SPEC); \
	test -d $$src || { echo "no spec sources for SPEC=$(SPEC)"; exit 1; }; \
	files=; for f in $$src/*.spectec; do keep=1; \
	  for p in $(EXCLUDE); do case $$(basename $$f) in $$p) keep=;; esac; done; \
	  if test -n "$$keep"; then files="$$files $$f"; fi; done; \
	"$$sp/bin/spectec" --ast --all-passes $$files > $$d/wasm-$(SPEC).il.sexp; \
	sh il2acl2/spec-decls.sh $$files > $$d/names.lsp; \
	{ echo '(assign probe-il "'$$d/wasm-$(SPEC).il.sexp'")'; \
	  echo '(assign probe-config "$(PROBE_CONFIG)")'; \
	  echo '(assign probe-version "$(SPEC)")'; \
	  echo '(defconst *probe-names* (quote'; cat $$d/names.lsp; echo '))'; \
	  echo '(assign probe-names *probe-names*)'; \
	  echo '(assign probe-drop (quote ($(PROBE_DROP))))'; \
	  echo '(assign probe-errors "'$$d/errors.lsp'")'; \
	  cat il2acl2/probe.lsp; } > $$d/run.lsp; \
	$(ACL2) < $$d/run.lsp > $$d/acl2.log 2>&1 || { tail -40 $$d/acl2.log; exit 1; }; \
	{ echo "Probe of WASM $(SPEC) (SpecTec $$(cut -c1-7 $$sp/share/spectec/REV))"; \
	  echo "Excluded: $(if $(EXCLUDE),$(EXCLUDE),none)"; \
	  echo "Spec files: $$(echo $$files | wc -w | tr -d ' '), lines: $$(cat $$files | wc -l | tr -d ' ')"; \
	  echo "IL lines: $$(wc -l < $$d/wasm-$(SPEC).il.sexp | tr -d ' '), bytes: $$(wc -c < $$d/wasm-$(SPEC).il.sexp | tr -d ' ')"; \
	  sed -n '/^PROBE-REPORT-BEGIN/,/^PROBE-REPORT-END/p' $$d/acl2.log | sed '1d;$$d'; } > $$d/report.txt; \
	{ echo "; Failing rules of WASM $(SPEC): rule, mode, error kinds, first error detail"; \
	  sed -n '/^PROBE-RULES-BEGIN/,/^PROBE-RULES-END/p' $$d/acl2.log | sed '1d;$$d'; } > $$d/rules.txt; \
	cat $$d/report.txt; echo "(report: $$d/report.txt, rules: $$d/rules.txt, errors: $$d/errors.lsp, log: $$d/acl2.log)"

check: check-il check-gen test

# The 2.0 gate (wasm3 prep P4): regenerate 2.0 from the checked-in IL (gen/wasm-2.0
# is not checked in: it is 20 MB and a deterministic function of IL and
# translator), certify it, and run the 2.0 numeric and SIMD vectors.
check-2.0:
	$(MAKE) check-il SPEC=2.0
	$(MAKE) gen SPEC=2.0
	$(CERT) --acl2 $(ACL2) -j $(JOBS) gen/wasm-2.0/wasm2 tests/sem-2.0/t3-numerics-2.0 tests/sem-2.0/t3-simd-2.0
	@grep -h "T3 numerics (2.0)\|T3 SIMD (2.0)" tests/sem-2.0/*.cert.out

# The 3.0 gate (wasm3 M0): regenerate 3.0 from the checked-in IL (gen/wasm-3.0 is
# not checked in) and certify it, in logic mode with time-limited attempts (config
# :logic, wasm3 M9); t0-modes-3.0 compares the modes with tests/sem-3.0/modes-3.0.lsp. Then the 3.0 numeric, SIMD (with
# relaxed SIMD) and builtin tests (wasm3 M1).
check-3.0:
	$(MAKE) check-il SPEC=3.0
	$(MAKE) gen SPEC=3.0
	$(CERT) --acl2 $(ACL2) -j $(JOBS) gen/wasm-3.0/wasm3 tests/sem-3.0/t3-numerics-3.0 tests/sem-3.0/t3-simd-3.0 tests/sem-3.0/t3-builtins-3.0 tests/sem-3.0/t5-subtyping-3.0 tests/sem-3.0/t6-instr-typing-3.0 tests/sem-3.0/t0-modes-3.0
	@grep -h "T3 numerics (3.0)\|T3 SIMD (3.0)\|T3 builtins (3.0)\|T5 subtyping (3.0)\|T6 instruction typing (3.0)" tests/sem-3.0/*.cert.out
	@echo "gen/wasm-3.0 certified; stubs: $$(sed -n "/^; Stubs/,/^;$$/p" gen/wasm-3.0/wasm3.lisp | grep -c "^;   ")"

clean:
	rm -rf .check-gen-1 .check-gen-2 gen.log
	find . \( -name '*.cert' -o -name '*.cert.out' -o -name '*.port' \
	       -o -name '*.fasl' -o -name '*.lx64fsl' -o -name '*.dx64fsl' \
	       -o -name '*.cert.time' -o -name 'Makefile-tmp' \) -delete
