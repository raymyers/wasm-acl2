# Deterministic SpecTec -> ACL2 translation of WASM 1.0.
# See ../plan/wasm1-translation/plan.md. Independent of the WASM1 tree in ..
#
#   make il                  regenerate il/wasm-1.0.il.sexp via Nix (pinned SpecTec)
#   make check-il            fail if the checked-in IL differs from a fresh regeneration

NIX ?= nix
IL  := il/wasm-1.0.il.sexp

.PHONY: il check-il

il:
	$(NIX) build ..#wasm1-il --no-link --print-out-paths > .il-out
	install -m 644 "$$(cat .il-out)/wasm-1.0.il.sexp" $(IL)
	rm -f .il-out

check-il:
	$(NIX) build ..#wasm1-il --no-link --print-out-paths > .il-out
	cmp "$$(cat .il-out)/wasm-1.0.il.sexp" $(IL)
	rm -f .il-out
	@echo "IL is up to date and reproducible"

# --- ACL2 books (translator + checks) -----------------------------------
ACL2 ?= acl2
CERT ?= $(ACL2_SYSTEM_BOOKS)/build/cert.pl
JOBS ?= 4
TEST_BOOKS := $(patsubst %.lisp,%,$(wildcard tests/*.lisp))

.PHONY: test clean

# Certify the translator and every tests/*.lisp check book.
test:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) $(TEST_BOOKS)

clean:
	find . \( -name '*.cert' -o -name '*.cert.out' -o -name '*.port' \
	       -o -name '*.fasl' -o -name '*.lx64fsl' -o -name '*.dx64fsl' \
	       -o -name '*.cert.time' -o -name 'Makefile-tmp' \) -delete
