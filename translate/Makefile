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
