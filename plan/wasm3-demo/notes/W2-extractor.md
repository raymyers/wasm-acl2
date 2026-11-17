# The extractor (demo/extract)
- Milestone: W2 (extractor)
- Date: 2026-11-15
- Repo commit: see the W2 commit (built on the W7 tagged gen/wasm-3.0)
- JSCL: 54c8849
- Status: final
- Feeds demo plan: W2, W3, W4
- Incorporated in demo plan: yes (W2)

## Summary
`make -C demo extract` runs `demo/extract/extract.lisp` in ACL2's raw
Lisp after the 3.0 portcullis and writes `demo/build/lisp/`: one file per
book on the include chain of `wasm3.lisp` (rt/ first, 27 files plus
`driver.lisp`), `ORDER`, `REPORT`, and for W3 the test files and data.
Closed event table (0 unknown events), package-qualified printing,
literal rewrite, clause-chain flattening (104 chains) and the stack
rewrite (672 self-recursive defuns into loops, 34 left with their reason). Two runs are
byte-identical and `translate/` stays clean (`make -C demo check-extract`).

## Findings

### Event table (closed; anything else is an error)
| event | rule | reason |
|---|---|---|
| `in-package` | drop | every symbol is printed package-qualified |
| `include-book` | followed (depth first, included book first), then dropped | load order |
| `set-verify-guards-eagerness`, `set-bogus-mutual-recursion-ok`, `program`, `set-state-ok`, `defthm`, `in-theory`, `verify-guards`, `value-triple`, `table`, `local` | drop | prover settings and proof-only events |
| `%TRY-GUARDS-T` | drop | guard verification only |
| `%TRY-LOGIC-T secs ev` | keep `ev` | every alternative of the `make-event` admits the same definition |
| `defun` | keep, `(declare (xargs ...))` stripped | measures mention prover-only functions |
| `mutual-recursion` | `progn` of the defuns | |
| `defmacro` | drop, only for `%TRY-LOGIC`, `%TRY-GUARDS`, `%TRY-LOGIC-T`, `%TRY-GUARDS-T` (event builders) and `%RULE` (the shim defines it, W8) | |
| `encapsulate` | drop, only the `%HOSTCALL-HOOK` signature | the shim defines the hook |
| `defattach f g` | `(ACL2::%DEFATTACH 'f 'g)` | F calls G until the driver attaches another function |
| `memoize` | `(ACL2::%MEMOIZE ...)` | identity for now (performance only) |
| `defconst` | `defparameter` | driver constants (`*s0*`, `*spec-fuel*`, `*data*`) |

Counts on the tagged 3.0 books plus the driver and test files: 1,515
`defun`, 1,298 `%TRY-LOGIC-T`, 1,298 `%TRY-GUARDS-T`, 12
`mutual-recursion`, 5 `defmacro`, 5 `defconst`, 4 `defthm`, 2
`in-theory`, 1 each `encapsulate`, `defattach`, `memoize`. 0 unknown.
`1_0-syntax_profiles` is not on the include chain and is not read.

### Printing
`|PKG|::|NAME|` for every symbol (keywords `:|NAME|`). The CL functions
that JSCL gets wrong for ACL2 are printed in package ACL2, which the shim
defines (closed list `+SHADOWED+`): the numeric functions (`+ - * / 1+ 1-
< <= > >= = /= ash ceiling denominator evenp oddp expt floor
integer-length integerp rationalp numberp logand logbitp logcount logior
lognot logxor max min mod numerator rem truncate round abs zerop plusp
minusp signum`) and `equal`, `append`, `reverse`.

### Rewrites (each the same for every form)
- **Literals**: a ratio becomes `(ACL2::%Q n d)`, an integer beyond 2^53 − 1
  `(ACL2::%BIG "digits")` (JSCL reads `1/2` as a symbol: W0 item 2). A
  number literal inside quoted data is an error (none exist).
- **Clause-chain flattening** (W0 item 3): 104 chains, 1,579 links; the
  flattened test is `(IF %CHAIN NIL (SETQ %CHAIN Xi))` (JSCL's `NOT` is
  a function call, not inlined).
- **Stack rewrite** (W1 (b)): a self-recursive defun whose calls of itself
  are all in tail position, or the last argument of a `CONS` in tail
  position, becomes a `DO` loop (PSETQ of the formals; CONS heads
  collected and put back with `REVAPPEND`). Tail positions through `IF`,
  `LET`, `LET*`, `PROGN`, `AND`, `COND`. A function that may return
  multiple values (body mentions `MV`, or calls such a function: fixpoint
  over all output defuns) keeps all of them: leaves store
  `(MULTIPLE-VALUE-LIST x)`, the loop returns `(VALUES-LIST ...)`, and no
  CONS heads are allowed.
- **Continuations** (added in W4: `br_table.0.wasm`, a `br_table` with a
  long label vector, overflowed node's default stack in
  `GRAM/BINSTR/REPn` and `$FREE_LIST`). Two more tail-position shapes:
  `(LET ((v B)) post)` with the call in `B` and none in `post`, and a
  function call `(g ... B ...)` with the call in exactly one argument `B`.
  Each pushes `(LAMBDA (v) post)` (or `(LAMBDA (v) (g ... v ...))`), closed
  over the current values of the formals (the loop reassigns them), and
  continues with `B` in tail position; the loop's final value goes
  through the pushed continuations, last pushed first. The other arguments
  are evaluated after the call instead of before: the code is pure, but
  `WRT::%RULE` (the W8 recorder) must keep its order, so an argument that
  contains it gives up. Not combined with CONS heads or multiple values.
  A "function" is any head without a macro or special-operator definition
  in the ACL2 image (the books are not loaded there, only their
  packages), plus ACL2's strict arithmetic macros (`+ * - / 1+ 1- < > <=
  >= = /= append logand logior logxor`).
- **Calls inside clause chains** (added in W4: `$SHIFT_LABELIDXS`). In a
  chain, flat (`%CHAIN`) or nested (`%R`), a clause is a path through
  `IF/AND/LET/LET*` to its success value `(LIST e)`, which is never NIL.
  So a clause path that reaches a success value containing the call has
  won the chain: it sets a commit flag (`WRT::%COMMITn`) and continues with
  `e` (`:car` chains) or `(LIST e)` (`:self`) in tail position; a path
  without the call sets the chain variable as before, and the commit flag
  skips the rest of the chain.
- Totals: **672 rewritten** (6 keep multiple values, 180 with
  continuations, 30 through a clause chain), incl. `$ALLOCMEM/ITER2`,
  `RUN-STEPS`, `CHECK-VECTORS`, `GRAM/BINSTR/REPn`, `$FREE_LIST`,
  `$SHIFT_LABELIDXS`. **34 left recursive**, with the reason in `REPORT`:
  18 "call in a binding" (a binding other than the last, or a `LET` with
  several), 6 under `OR`, 3 continuation in a function that may return
  multiple values, 3 `LET` rebinds a formal, 2 in a test, 1 under
  `MV-LET`, 1 CONS head with multiple values. Among them `STEP` (its
  recursion is the nesting of `LABEL_`/`FRAME_`, not the input length).
  Before the W4 additions: 488 rewritten, 218 left.
- A first version rewrote multiple-value functions like any other and kept
  only the first value: `MODULE_OK` failed on every module with a typed
  function body (found by bisecting with `DEMO_STACK_REWRITE=nil`).

### JSCL facts learned on the way
- `LOOP`/`RETURN` and `TAGBODY`/`GO` compile to JS exceptions per
  iteration (`TagNLX`, `BlockNLX`); `DO` without `RETURN` is a plain JS
  `while`. The stack rewrite and the shim use only the latter.

### Report (`demo/build/lisp/REPORT`, every run)
Events per kind, dropped events, rewrites, output forms per book, the
functions called but not defined (package ACL2: 59 names, provided by the
shim; package COMMON-LISP: 52, provided by JSCL; elsewhere:
`W3T::READ-BYTES` (driver glue), `WRT::%HOSTCALL-HOOK` (defined by
`%DEFATTACH` at load), `WRT::%RULE` (shim)), and the self-recursive
functions rewritten or left.

### Named extraction (W2 item 4)
`run.sh` names the pure helpers of `tests/spec/t7-lib-3.0.lisp` (a name
in a `mutual-recursion` brings the whole clique; an unknown name is an
error): `vt-bits lane-bits lanes-nat nat-lanes to-val to-vals
float-bits-ok lanes-ok ref-kind ref-ok val-ok either-ok vals-ok env-store
env-inst chars-of str-bytes find-export registered resolve-imports
*spec-fuel* run-steps final-config exn-result-p instantiate do-action
value-instr-p all-values-p fail-class *s0* *data* parse-file run-cmd
spectest-env` → `driver.lisp`.

### Not done
- Pruning (W2 item 5): not needed (W0 item 3: 3.75 MB).

## Data
`make -C demo extract` (REPORT printed); `make -C demo check-extract`.
