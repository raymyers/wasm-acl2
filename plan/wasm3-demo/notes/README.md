# WASM 3.0 browser demo: notes

Findings for [the demo plan](../plan.md). The conventions are the prep's
([plan/wasm3-translation-prep/notes/README.md](../../wasm3-translation-prep/notes/README.md)).
The only difference is that notes are named by demo milestone (`W<k>-<slug>.md`;
`S0` is the planning survey). The header uses `Feeds demo plan:` in place of
`Feeds wasm3 plan:`, and records the JSCL rev when a note depends on it.

**Rule**: if a finding is not in a note here (or in `../plan.md`), it does not
exist. Raw outputs go under `data/<name>/` together with the script that made them.

## Index

| Note | Milestone | Status | Summary |
|---|---|---|---|
| [S0-survey](S0-survey.md) | planning | final | 27 books / 486,141 lines / ~33 MB; JSCL has no bignums or ratios; memory is a 65,536-element list per page |
| [W0-feasibility](W0-feasibility.md) | W0 | final (go) | toolchain in the flake; all 27 books: 3.75 MB JS, 2.3 s compile, 0.1 s load; decoder nesting (1,010) breaks JS parsers, fixed by clause-chain flattening; ratios misread by JSCL; deepest recursion 65,541 ($ALLOCMEM/ITER2, self, mod cons) vs 2,047 frames in a Chromium Worker; option A ≤ 4.04× |
| [W7-rule-tags](W7-rule-tags.md) | W7 | final | `(%RULE "Rel/id" out)` on every rule's success value, `Gram/#k` on productions; macro = identity in ACL2; gates green, manifests unchanged; spec 258/258 (3.0) and 67/67 (1.0) scripts identical per command, 9 timeouts/crashes identical at a doubled TIMEOUT; coverage 218/218 |
| [W1-numbers-stack](W1-numbers-stack.md) | W1 | final | D5 final: numbers by a shim tower (A, ≤ 4.04× plain JSCL), stack by a mechanical self-recursion rewrite in the extractor ((b)), node stack flags as fallback; both conditions hold |
| [W2-extractor](W2-extractor.md) | W2 | final | `make -C demo extract`: closed event table (0 unknown), `\|PKG\|::\|NAME\|` printing, literal rewrite, clause-chain flattening (104 chains), stack rewrite (672 loops, 34 left, reasons in REPORT); two runs identical, translate/ untouched |
| [W3-shim](W3-shim.md) | W3 | final | shim: D5 number tower (num.js), list ops as JS loops (list.js, acl2-count memoized), ACL2 definitions (acl2.lisp), %RULE; under JSCL in node 8,724/8,724 numeric and 1,008/1,008 SIMD vectors (480 relaxed, full profile 480/480), 119/119 unit tests vs ACL2 |
| [W4-semantics-node](W4-semantics-node.md) | W4 | final | all books in node (3.96 MB, 0.13 s load); driver: decode, load-module, invoke with fuel, host imports via %HOSTCALL-HOOK; spec-test-3 subset 7,087/7,087 commands agree with ACL2 (per command; call_indirect on ACL2's prefix); bugs found: stack shapes (br_table), acl2-count cost (memoized); 0.32–3.84 ms/step, 32× slower to 4× faster than ACL2 on the same invokes |
| [W5-browser-page](W5-browser-page.md) | W5 | final | page in a Web Worker next to native WebAssembly (D4), wabt in the page, six examples, fuel and Stop; Step mode with redex, operands, locals, nesting and memory diff; smoke test in headless Chromium and Firefox: all runs equal native, Step counts = Run counts |
| [W6-wat-line](W6-wat-line.md) | W6 | final | Step mode shows wabt's flat print of the binary with the current line (display aid): function from the call that made the FRAME_, position from what is left of the body, blocks/loops/if/try_table through their LABEL_; Next line, breakpoints; 234/234 configurations on hand-written lines (node and both browsers) |
| [W8-rule-names](W8-rule-names.md) | W8 | final | %RULE recorder in the shim, on for one STEP; chain read from the end of the trace through the six Step rules with Step premises (from the IL); 33/33 steps of six programs equal hand-written chains; page shows each step's chain with links to the SpecTec source; 224/224 steps of the W5 examples have a chain; page print host (env) |
| [W9-build](W9-build.md) | W9 | final | `make -C demo all check` green (every demo test, 65 s); `nix build .#wasm3-demo` builds the page from a clean checkout (7.3 MB static directory, smoke passes on it); translate/ untouched, the three ACL2 gates green; demo/README.md; publishing left to the user |
