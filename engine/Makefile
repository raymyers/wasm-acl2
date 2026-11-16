# The verified WebAssembly 3.0 engine (plan/wasm-engine). Run inside
# `nix develop ..`. The specification is ../translate/gen/wasm-3.0, which
# `make -C ../translate check-3.0` (or `gen SPEC=3.0` and a certification)
# builds; this Makefile certifies it if it is not certified yet.
#
#   make check   certify every engine book; fail if a book contains
#                skip-proofs or defaxiom
ACL2 ?= acl2
CERT ?= $(ACL2_SYSTEM_BOOKS)/build/cert.pl
JOBS ?= 4
BOOKS := $(patsubst %.lisp,%,$(wildcard theorem/*.lisp machine/*.lisp rules/*.lisp fast/*.lisp))

.PHONY: check certify no-skips clean

check: certify no-skips

certify:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) portcullis $(BOOKS)

# The certify half of the litmus test (plan L2) counts on this: no engine
# book may contain skip-proofs or defaxiom. Comments are stripped first.
no-skips:
	@if sed 's/;.*//' $(addsuffix .lisp,$(BOOKS)) | grep -n -i "skip-proofs\|defaxiom"; then \
	  echo "engine: a book contains skip-proofs or defaxiom"; exit 1; \
	else echo "engine: no skip-proofs, no defaxiom in $(words $(BOOKS)) book(s)"; fi

clean:
	find . \( -name '*.cert' -o -name '*.cert.out' -o -name '*.port' -o -name '*.fasl' \
	       -o -name '*.cert.time' -o -name 'Makefile-tmp' \) -delete
