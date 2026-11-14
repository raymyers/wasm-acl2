# Deterministic SpecTec -> ACL2 translation of WASM 1.0.
# See ../plan/wasm1-translation/plan.md. Independent of the WASM1 tree in ..
#
# Run inside `nix develop ..` (provides ACL2, CERT and nix).
#
#   make il          regenerate il/wasm-1.0.il.sexp via Nix (pinned SpecTec)
#   make check-il    fail if the checked-in IL differs from a fresh regeneration
#   make gen         run the translator: il/ + il2acl2-config.lsp -> gen/
#   make check-gen   fail unless two fresh translator runs agree with gen/
#   make test        certify the translator, gen/, rt/ and every test book
#   make check       check-il + check-gen + test

NIX  ?= nix
ACL2 ?= acl2
CERT ?= $(ACL2_SYSTEM_BOOKS)/build/cert.pl
JOBS ?= 4
IL   := il/wasm-1.0.il.sexp
GEN_FILES := package.lsp portcullis.acl2 portcullis.lisp cert.acl2 wasm1.lisp
TEST_BOOKS := $(patsubst %.lisp,%,$(wildcard tests/*.lisp tests/sem/*.lisp))

.PHONY: il check-il gen check-gen test check clean translator

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

test:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) $(TEST_BOOKS)

check: check-il check-gen test

clean:
	rm -rf .check-gen-1 .check-gen-2 gen.log
	find . \( -name '*.cert' -o -name '*.cert.out' -o -name '*.port' \
	       -o -name '*.fasl' -o -name '*.lx64fsl' -o -name '*.dx64fsl' \
	       -o -name '*.cert.time' -o -name 'Makefile-tmp' \) -delete
