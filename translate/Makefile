# Deterministic SpecTec -> ACL2 translation of WASM 1.0.
# See ../plan/wasm1-translation/plan.md. Independent of the WASM1 tree in ..
#
# Run inside `nix develop ..` (provides ACL2, CERT and nix).
#
#   make il          regenerate il/wasm-1.0.il.sexp via Nix (pinned SpecTec)
#   make check-il    fail if the checked-in IL differs from a fresh regeneration
#   make gen         run the translator: il/ + il2acl2-config.lsp -> gen/
#   make check-gen   fail unless two fresh translator runs agree with gen/
#   make vectors     regenerate tests/sem/numeric-vectors.lsp (WASM engine oracle)
#   make invoke-vectors  regenerate tests/sem/invoke-vectors.lsp (V8 runs the corpus exports)
#   make test        certify the translator, gen/, rt/ and every test book
#   make compare     T9 reports: run the WASM1 tree on the same oracle vectors
#   make probe SPEC=3.0  probe table for one spec version (plan/wasm3-translation-prep P0)
#   make check       check-il + check-gen + test

NIX  ?= nix
ACL2 ?= acl2
CERT ?= $(ACL2_SYSTEM_BOOKS)/build/cert.pl
JOBS ?= 4
IL   := il/wasm-1.0.il.sexp
GEN_FILES := package.lsp portcullis.acl2 portcullis.lisp cert.acl2 wasm1.lisp
TEST_BOOKS := $(patsubst %.lisp,%,$(wildcard tests/*.lisp tests/sem/*.lisp))

.PHONY: il check-il gen check-gen test check clean translator vectors compare corpus invoke-vectors probe

il:
	$(NIX) build ..#wasm1-il --no-link --print-out-paths > .il-out
	install -m 644 "$$(cat .il-out)/wasm-1.0.il.sexp" $(IL)
	rm -f .il-out

check-il:
	$(NIX) build ..#wasm1-il --no-link --print-out-paths > .il-out
	cmp "$$(cat .il-out)/wasm-1.0.il.sexp" $(IL)
	rm -f .il-out
	@echo "IL is up to date and reproducible"

translator:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) il2acl2/emit

# The translator writes into ./gen/ relative to translate/.
gen: translator
	mkdir -p gen
	$(ACL2) < il2acl2/run.lsp > gen.log 2>&1 || (tail -40 gen.log; exit 1)
	@echo "gen/ regenerated (log: gen.log)"

# Regenerate twice from scratch copies and compare both with gen/.
check-gen: translator
	@set -e; for n in 1 2; do \
	  d=.check-gen-$$n; rm -rf $$d; mkdir -p $$d/gen; \
	  mkdir -p $$d/il2acl2; \
	  cp -R il il2acl2-config.lsp package.lsp portcullis.acl2 portcullis.lisp cert.acl2 $$d/; \
	  cp il2acl2/*.lisp il2acl2/*.lsp il2acl2/cert.acl2 $$d/il2acl2/; \
	  (cd $$d && $(ACL2) < il2acl2/run.lsp > gen.log 2>&1) || { tail -40 $$d/gen.log; exit 1; }; \
	  for f in $(GEN_FILES); do cmp $$d/gen/$$f gen/$$f; done; \
	done; rm -rf .check-gen-1 .check-gen-2
	@echo "gen/ is up to date and the translator is deterministic"

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

# T9 side-by-side reports (include the WASM1 tree; see the .cert.out files).
compare:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) $(patsubst %.lisp,%,$(wildcard compare/*.lisp))
	grep -h -A3 "T9 " compare/*.cert.out

# Probe (plan/wasm3-translation-prep P0): elaborate spec version SPEC with the
# pinned SpecTec into .probe/<SPEC>/ and print the probe table (schema errors,
# mangling, events, stubs by source file, error kinds). Writes nothing under
# gen/. EXCLUDE is a list of file globs to leave out, e.g. EXCLUDE='X.* 6.*'.
# For 2.0/3.0 the 1.0-specific config entries (PROBE_DROP) are ignored.
SPEC ?= 3.0
EXCLUDE ?=
PROBE_DIR := .probe/$(SPEC)
PROBE_CONFIG ?= il2acl2-config.lsp
PROBE_DROP ?= $(if $(filter 1.0,$(SPEC)),,:rel-override :il-patch)

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
	sh il2acl2/probe-names.sh $$files > $$d/names.lsp; \
	{ echo '(assign probe-il "'$$d/wasm-$(SPEC).il.sexp'")'; \
	  echo '(assign probe-config "$(PROBE_CONFIG)")'; \
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

clean:
	rm -rf .check-gen-1 .check-gen-2 gen.log
	find . \( -name '*.cert' -o -name '*.cert.out' -o -name '*.port' \
	       -o -name '*.fasl' -o -name '*.lx64fsl' -o -name '*.dx64fsl' \
	       -o -name '*.cert.time' -o -name 'Makefile-tmp' \) -delete
