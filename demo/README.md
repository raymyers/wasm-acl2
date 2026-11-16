# WASM 3.0 in the browser, run by its formal semantics

The page runs WebAssembly 3.0 modules with the SpecTec specification's
own reduction rules: the spec is translated to ACL2 (`translate/`), the
ACL2 books are extracted to Common Lisp and compiled to JavaScript by
JSCL, and the result runs in a Web Worker next to the browser's own
`WebAssembly` engine. A stepper shows each reduction step, the WAT line it
belongs to, and the spec rules that justify it.

The plan, decisions and measurements are in
[`plan/wasm3-demo/`](../plan/wasm3-demo/plan.md) (notes: `notes/W*.md`).

## Build and check

Everything runs inside the flake's dev shell (ACL2, SBCL, JSCL, node,
wabt.js, Playwright with headless Chromium and Firefox, pngquant):

```sh
nix develop
make -C translate gen SPEC=3.0      # translate/gen/wasm-3.0 (not checked in)
make -C demo                        # demo/build/: wasm3.js and the page (build/web)
make -C demo check                  # the tests below
```

To view the page locally, serve the built directory (not `web/`, which lacks
`wasm3.js`, `wabt.js` and `jscl.js`):

```sh
make -C demo                                  # once, to populate build/web
python3 -m http.server 8000 -d demo/build/web # from the repo root
# then open http://localhost:8000/
```

Use a server rather than `file://`: the page starts a Web Worker, which
browsers refuse to load from `file://`. `nix build .#wasm3-demo` output
can be served the same way (`python3 -m http.server -d result`).

`nix build .#wasm3-demo` builds the page as a static directory (the site
root) without the dev shell.

`make -C demo check` runs, in order: the toolchain checks (`jscl-hello`,
`wabt-hello`, `browser-hello`), `check-extract` (two extractions are
byte-identical and `translate/` is untouched), `vectors` and `units` (the
shim against ACL2's numeric and SIMD vectors and unit values), `host`
(host imports), `conformance-quick` (spec-test-3 scripts command by
command against ACL2's results), `smoke` (the page in headless Chromium
and Firefox against native `WebAssembly`: Step, Run to end, breakpoints), `lines`
(the WAT line of every step against hand-written lines) and `chains`
(rule chains of every step against hand-written ones). `conformance-quick`
and `conformance` (the whole subset, about 25 minutes) need ACL2's spec
results: `make -C translate spec-data spec SPEC=3.0` (about 11 minutes).

## What is derived from what

| output (`demo/build/`) | made from | by |
|---|---|---|
| `lisp/NN-*.lisp`, `ORDER` | `translate/gen/wasm-3.0/*.lisp` (the 27 books, include order), `translate/rt/*.lisp` | `extract/extract.lisp` in ACL2's raw Lisp (`make extract`) |
| `lisp/driver.lisp` | named functions of `translate/tests/spec/t7-lib-3.0.lisp` (the ACL2 conformance driver) | the extractor |
| `lisp/tests/*.lisp`, `lisp/data/*.json`, `lisp/tests/units-expected.json` | the checking functions and data of `translate/tests/sem*/`; `test/units.lsp` evaluated in ACL2 | the extractor |
| `lisp/REPORT` | every extraction: events per kind, rewrites, names the shim must provide | the extractor |
| `wasm3.js` | `shim/num.js`, `shim/list.js`, `driver/host.js`, then the shim, `lisp/*`, `driver/glue.lisp` compiled by JSCL | `make js` |
| `web/` | `web/*`, `driver/lisp.js`, `jscl.js`, `wasm3.js`, wabt.js | `make web` |

Nothing under `translate/` is copied or edited: the extractor only reads
it, and anything derived goes to `demo/build/` (not checked in).

## The extractor (`extract/`)

A closed table of ACL2 events (anything else is an error), package-
qualified printing, and mechanical rewrites, each the same for every form:
number literals JSCL cannot read (ratios, integers beyond 2^53), clause
chains flattened (the JS parsers' nesting limit), and self-recursion into
loops (JS stacks are small). Each entry has its reason next to it;
[`notes/W2-extractor.md`](../plan/wasm3-demo/notes/W2-extractor.md).

## The shims (`shim/`) and why

The only hand-written code next to the semantics; each part is checked
against ACL2's own output.

| file | what | why |
|---|---|---|
| `num.js` | integers as JS numbers up to 2^53 − 1, BigInt beyond, ratios as normalized BigInt pairs, and every numeric function the books call | JSCL's numbers are JS doubles only; the semantics needs exact i64/v128 integers and rationals (decision D5) |
| `list.js` | `equal`, `len`, `append`, `acl2-count`, ... as JS loops; `acl2-count` memoized by cons identity | JSCL's `equal`/`append` recurse on `cdr` (small browser stacks); the generated size checks count every step's inputs |
| `acl2.lisp` | the ACL2 functions the books call that JSCL lacks or gets wrong; `mv`; the extractor's hooks | the books are ACL2, not plain Common Lisp |
| `rule.lisp` | `%RULE`, the translator's rule tag: identity, or a recorder while the stepper asks for a step's rule chain | W7/W8 |

## The driver (`driver/`)

`glue.lisp` gives JavaScript a small API over the extracted semantics and
the ACL2 conformance driver's own helpers: `LOAD-MODULE`, `INVOKE` (with
fuel), `REGISTER-HOST` (host functions through `%HOSTCALL-HOOK`),
`START-INVOKE`/`STEP-CONFIG`/`FINISH-CONFIG` (Step mode), `STEP-RULES`
(rule chains), `RUN-CMD` (spec scripts). `lisp.js` and `sexp.js` are the
JS side (Lisp values, data files), `host.js` the default host.

## The page (`web/`)

`index.html`, `app.js` (UI), `worker.js` (the semantics in a Worker),
`semantics.js` (values, Step mode, the configuration view), `native.js`
(the same module on `WebAssembly`), `modinfo.js` (WAT or hex to bytes,
export types), `examples.js`. The WAT line and the highlighting are a
display aid computed from the configuration; the rule names come from the
translator's tags.
