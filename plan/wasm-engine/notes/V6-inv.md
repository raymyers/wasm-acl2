# V6: the fast machine's invariant, loader and run; T2 with one hypothesis

- Milestone: V6 (plan2.md: `fm-inv`, a step keeps it, absorbing statuses, the run, the loader, stores with no memory or several, T2 with the `call_ref` hypothesis)
- Date: 2026-11-18
- Repo commit: 7a45690 plus this note's commit
- Status: final
- Feeds engine plan: V7 (removes `no-call-ref-run`; what it has to prove is in §7), V8 (`engine-run` is `fm-load-ms` of `ms-of-config`; `config-shape-p` and the three loader lemmas are here; §5, §7), V9 (T2 is the second statement `top.lisp` restates)
- Incorporated in engine plan: yes (plan2.md V6, "Current state")

## Summary

- **V6 is complete.** Two new books, `engine/fast/inv.lisp` (9.1 s) and
  `engine/fast/spec-result.lisp` (2.2 s), certify under
  `make -C engine check`. The gate has 33 books (31 before), no
  `skip-proofs`, no `defaxiom`, no trust tag.

  ```lisp
  (defun fm-inv (fm)                              ; executable, guards verified
    (declare (xargs :stobjs fm))
    (and (fmp fm)
         (fast-inv-store (fm-store fm))
         (machine-ok (fm->ms fm))))

  (defthm fast-step-keeps-fm-inv                  ; 742 prover steps
    (implies (and (fm-inv fm)
                  (not (equal (entry-kind (car (fm-is fm))) :call_ref))
                  (not (equal (fm-status (fast-step fm)) :unsupported)))
             (fm-inv (fast-step fm))))

  (defthm fast-run-is-machine-run                 ; 984
    (implies (and (fm-inv fm)
                  (no-call-ref-run n (fm->ms fm))
                  (not (equal (fm-status (fast-run n fm)) :unsupported)))
             (equal (fm->ms (fast-run n fm))
                    (machine-run n (fm->ms fm)))))

  (defthm fast-result-is-spec-result              ; T2, 2,080
    (implies (and (fm-inv fm)
                  (fast-result-p (fast-run n fm))
                  (natp fuel)
                  (< (fast-clocks n fm) fuel)
                  (no-call-ref-run n (fm->ms fm)))      ; V7 removes this
             (equal (w3t::steps/%fuel fuel (machine-abs (fm->ms fm)))
                    (list (machine-abs (fm->ms (fast-run n fm)))))))
  ```

- **T2 is the statement of plan2.md §1 with one more hypothesis**,
  `(no-call-ref-run n (fm->ms fm))`: the run has no `call_ref` at the
  head of its instructions. The plan asked for exactly this ("carried as
  'the run executes no `call_ref`'"). It has no hypothesis about
  `:unsupported`: a run that ends with a result did not stop
  `:unsupported` on the way, because every status but `:run` is
  absorbing (§3).
- **The invariant is proved, not assumed, for the loader's states**:
  `fm-inv-of-fm-load-ms` and `fm->ms-of-fm-load-ms` for a list state
  with `fm-loadable-p`, and `machine-abs-of-ms-of-config`,
  `machine-ok-of-ms-of-config`, `fm-loadable-p-of-ms-of-config` for a
  configuration with `config-shape-p` (§5). V8 composes them into T3.
- **The risk "the fallback's accepted results do not imply
  `fast-inv-store`" did not happen** (§2): what `fallback-shape-ok`
  accepts is enough. `fast.lisp` did not change, so lockstep and test 3
  were not run again.
- **No machine changed.** No failed checkpoint was a state the machine
  can reach (§6).
- **A store with no memory is outside** (§4): `fast-inv-store` asks for a
  memory. `config-shape-p` says so, and it is the executable hypothesis
  the driver checks. A store with several memories is inside.
- **The slides on the fast machine**: 12 runs, on each the configuration
  has `config-shape-p`, the loaded stobj has `fm-inv` and the run ends
  with a result; 7 of 7 slides identical to V8. They are **not inside T2
  yet**: every call of the module is a `call_ref`
  ([V0-ground](V0-ground.md) §1), so `no-call-ref-run` is false for
  them. The viewer caption says so (§8).
- One name was changed in an old book: the generator `length-lemma` of
  `rules/shape.lisp` is `not-length-lemma` (§6). No proof changed.

## Findings

All prover steps are from the certification output
(`data/v6-inv/measure.txt`, every `defthm` of the two books).

### 1. The books

`fast/inv.lisp` includes `fast/ctrl-kinds` (the fast tower and
`machine/ok`); it does not include the proofs about the specification.
`fast/spec-result.lisp` includes `inv` and `machine/spec-result` (T1).
The two towers had not been loaded together before: see §6 for the one
clash.

| Section of `inv.lisp` | Statements | Largest proof |
|---|---|---|
| 1. The stobj stays well formed | `fmp` of `fm-set`, `mem-write`, `list-to-mem`, `fast-apply-fallback`, `fast-apply-rule`, `fast-try-rules` | 47,005 (`fmp-of-fast-apply-fallback`) |
| 2. A rule leaves a fast store | `fast-try-rules-keeps-inv-store`, from one lemma for any rule | 439,049 (a generated one, §2) |
| 3. The parts of a step | `fmp` and `fast-inv-store` after `fast-enter-step`, `fast-op-step`, `fast-exit-step`, `fast-anyprefix-step`, `fast-step` | 55,661 (`fast-step-keeps-inv-store`) |
| 4. The invariant and a step | `fm-inv`, `machine-ok-of-fast-step`, `fast-step-keeps-fm-inv`, `fm->ms-of-fast-step` | 881 |
| 5. The run | `fast-run-when-not-running`, `fast-run-is-machine-run`, `fast-run-keeps-fm-inv` | 6,803 |
| 6. The loader | `fm->ms-of-fm-load-ms`, `fm-inv-of-fm-load-ms`, the three `ms-of-config` lemmas | 2,972 |

Hints in `inv.lisp`: 7 `:use`, 2 `:cases`, 6 `:induct`, no `"Subgoal"`;
in `spec-result.lisp`: 2 `:use`.

Normal forms. The accessors of the stobj are enabled in the books below
`inv.lisp`, so a term about a field is `(nth k fm)`; the left side of a
rewrite rule is written that way (`(nth *fm-store* (fast-op-step fm))`).
Results of a function of several values are written with `mv-nth`, which
is disabled, with `mv-nth-1-2-3` (it rewrites `mv-nth` to `cadr`,
`caddr`, `cadddr`, and is enabled in `refine-mem.lisp`). Three lemmas of
`refine-op.lisp` that say `cadddr` or `cadr` are restated:
`nth-of-fast-try-rules-stobj`, `fast-hot-step-when-handled`,
`fast-hot-step-when-declined`.

### 2. A rule that fires and is not refused leaves a fast store (V6 item 2)

```lisp
(defthm fast-apply-rule-keeps-inv-store          ; any FN, 440 steps
  (implies (and (fast-inv-store s)
                (mv-nth 0 (fast-apply-rule fn (list :|%;%| s f) redex fm))
                (not (equal (mv-nth 0 (fast-apply-rule fn (list :|%;%| s f) redex fm)) :refuse)))
           (fast-inv-store (cadr (mv-nth 1 (fast-apply-rule fn (list :|%;%| s f) redex fm))))))
```

It holds for every `fn`, a rule or not, the two host rules of `call_ref`
included (they take the fallback). By the four ways `fast-apply-rule`
applies a rule:

| Path | Why the store is a fast store | Lemmas |
|---|---|---|
| the fallback (87 rules, and a memory rule when the store has several memories) | the machine accepts a result only with `fallback-shape-ok`: memory 0 a record with a byte list, every field. Its store with the bytes taken out is a fast store | `fast-apply-fallback-keeps-inv-store` (3,399), one statement for any rule |
| a memory rule that reads (15) | the state is the one given | none: `fast-apply-rule` returns `z` |
| the 4 store rules of the fast path | the store is the one given (`$with_mem` is carried out on the array), or the rule's own configuration with the store given | 4 generated, 133,211 to 439,049 |
| a frame-safe rule (106) | 101 are pure or read rules: `apply-rule` returns the state given (`apply-rule-keeps-state-when-not-state-rule`, 6,035, for any `fn` outside the 30 rules that return a configuration). 5 return a configuration | 5 generated, 513 to 180,753 |

So 9 lemmas are per rule, not 212. The 5 frame-safe rules that return a
configuration are `call_ref-null`, `call_ref-func`, `throw`,
`local.set`, `global.set` (`*frame-safe-state-rules*`, computed). Each
generator prints one line per lemma (`INV-LEMMA`), gives it a step limit,
and its book event fails if a lemma is missing; nothing is recorded as
"not yet".

The store of the 5: unchanged, or one field other than `:mems` replaced
(`:globals`, `:exns`). `fast-inv-store-of-put-field-other` is the fact
used; `mem0-record-p` is not a consequence of `fast-store-ok` (a memory 0
that is not a record is left as it is by `%put-field`), so it is part of
what is carried.

The plan's risk row "the fallback's accepted results do not imply
`fast-inv-store`" did not happen, and `fallback-shape-ok` was not
strengthened.

### 3. A step, the absorbing statuses, the run (V6 items 2 to 4)

- `fmp` and the fast store after `fast-step` need no hypothesis about
  `:unsupported`: a refused rule leaves the fields of the stobj as they
  were. They need `ctrl-kinds-ok` (the place function of a control entry
  is rewritten to `fast-try-rules` for the kinds `:l`, `:h`, `:f`) and
  "the head is not `call_ref`" (`fast-try-op-is-try-rules` excludes that
  place, whose place lemma is V7's).
- `machine-ok` after `fast-step` is `fast-step-refines` followed by C1
  of the list machine (`machine-step-preserves-ok`); for a state that
  does not run the step is the identity. This is where "not
  `:unsupported`" enters: the refinement is not stated for a refused
  step.
- **Absorbing** (item 3): `fast-step-when-not-running` and
  `fast-run-when-not-running`: with a status other than `:run`,
  `fast-step` and `fast-run` return the stobj. That is all five of
  `:unsupported`, `:stuck`, `:done`, `:trap`, `:throw`.
- **The run** (item 4), two inductions on `fast-run`:
  `fast-run-supported-when-not-unsupported` (1,313): if the run does not
  end `:unsupported` then no step of it did (`fast-run-supported`, a
  non-executable predicate along the run); and
  `fast-run-is-machine-run-when-supported` (6,803): equality with
  `machine-run` and `fm-inv` of the last state together.
- `no-call-ref-run n s` is defined on the list machine (executable,
  guard `(natp n)`): at each of the `n` steps of `machine-run` from `s`
  that the machine takes, the head is not `call_ref`.

### 4. Stores with no memory, or several (V6 item 6): decided

- **Several memories: inside.** `fm-loadable-p` asks of the store only
  that memory 0 is a record with a byte list and that the store has all
  its fields (`mem0-shape-ok`, `store-fields-p`). The array holds
  memory 0; the other memories stay in the store. A memory rule then
  takes the exact fallback (`fast-one-memory-p` is false), which §2
  covers.
- **No memory: outside.** `fast-inv-store` has `(consp mems)`
  (`fast-store-ok`, on which every refinement lemma of E7 rests), so the
  loader lemma cannot hold for such a store, and widening the invariant
  would mean stating those lemmas again. The loader does not get a
  refusing status either: `fm-load-ms` is unchanged. The refusal is the
  hypothesis: `config-shape-p` includes `mem0-shape-ok`, it is
  executable with guard `t`, and V8's driver checks it (plan2.md §1: "the
  only hypothesis about the input is its shape, which is executable and
  which the driver checks"). A module without a memory still runs on the
  fast machine as before (its frame-safe rules apply; a fallback rule is
  refused); it has T1 on the list machine and no T3.
- The slides and TeX have one memory.

### 5. The loader (V6 item 5)

```lisp
(defun fm-loadable-p (s)
  (and (machine-ok s) (mem0-shape-ok (ms-store s)) (store-fields-p (ms-store s))))

(defthm fm->ms-of-fm-load-ms                     ; 175
  (implies (fm-loadable-p s) (equal (fm->ms (fm-load-ms s fm)) s)))
(defthm fm-inv-of-fm-load-ms                     ; 365
  (implies (and (fmp fm) (fm-loadable-p s)) (fm-inv (fm-load-ms s fm))))

(defun config-shape-p (c)       ; ((s; f); instrs), s loadable
  (and (true-listp c) (equal (len c) 3) (equal (car c) :|%;%|)
       (true-listp (cadr c)) (equal (len (cadr c)) 3) (equal (car (cadr c)) :|%;%|)
       (true-listp (caddr c))
       (mem0-shape-ok (cadr (cadr c))) (store-fields-p (cadr (cadr c)))))

(defthm machine-ok-of-ms-of-config    (implies (config-shape-p c) (machine-ok (ms-of-config c))))
(defthm machine-abs-of-ms-of-config   (implies (config-shape-p c) (equal (machine-abs (ms-of-config c)) c)))
(defthm fm-loadable-p-of-ms-of-config (implies (config-shape-p c) (fm-loadable-p (ms-of-config c))))
```

`(fmp fm)` is true of the live stobj. The first lemma needs nothing of
the stobj: `list-to-mem` resizes the array and `mem-to-list` reads it
back (`list-to-mem-array` and `put-mem0-bytes-roundtrip` of
`refine.lisp`). `machine-ok` is part of `fm-loadable-p` because `fm->ms`
builds a list of six: the equality with `s` needs `s` to be one.

### 6. What failed on the way, and the one old book that changed

None of these checkpoints is a state of the machine; each is a
definition that should have been closed.

| Attempt | What happened | What was done |
|---|---|---|
| `apply-rule` returns its state for a pure or read rule, by opening `apply-rule` (a `case` over 212 rules) with the rule functions enabled | 125 s in preprocessing, 36 prover steps, interrupted (the step limit does not stop preprocessing, [V0-ground](V0-ground.md)) | the 212 rule functions disabled in the hint: 6,035 steps |
| `step/r-throw` keeps the fast store, with the rule and the type functions open (`expand`, `$unrolldt`, `$as_deftype`, `$unrollrt`) and `fast-inv-store` open | more than 2,000,000 steps (25.8 s); the same theory proved `call_ref-func` in 1,986,712 (21.3 s) | those closed, `fast-inv-store` closed, `fast-inv-store-of-put-field-other` as a rewrite rule: 3,782 and 180,753 |
| the 5 rules combined, `drop-n` enabled | checkpoint `(consp (car (w3t::step/r-call_ref-null ...)))`: `(drop-n 1 (car r))` opened to a case on `(car r)` before `car-drop-n-is-cadr` could rewrite it | `drop-n` disabled in the book |
| `fmp-of-fm-set`, `fast-enter-step-keeps-inv-store` | checkpoints `(fmp (list* s f v is c st (cddr (cddddr fm))))` and `(fast-inv-store (car (update-nth 5 :stuck fm)))`: `update-nth` and `nth` opened | both disabled in the book (enabled in the 9 generated proofs, whose rule bodies use `nth`) |
| `fast-step-keeps-fmp` | more than 2,000,000 steps (31.9 s): `fast-val-p` was rewritten to `value-instr-p` and `val-p` opened | `value-instr-p`, `val-p`, `fast-val-p` disabled |
| `machine-ok-of-fast-step` | `machine-step` opened in place of C1; checkpoint `(val-list-p (nth 2 fm))` | `machine-step` disabled |
| the run, first statement | `(fm->ms (fast-step fm))` was not rewritten with `fm-inv` closed | `fm->ms-of-fast-step`, the step theorem from `fm-inv`; openers `no-call-ref-run-when-running`, `machine-run-when-running` |

**`rules/shape.lisp`.** `fast/memory.lisp` and `rules/shape.lisp` both
defined a program-mode generator `length-lemma`, with different
arguments, so `machine/spec-result` could not be included after
`fast/ctrl-kinds`. The one of `shape.lisp` is now `not-length-lemma`
(two occurrences). It generates the `-FAILS-WHEN-NOT-LENGTH` lemmas; their
names and statements did not change. The books above `shape.lisp`
certified again (34 s for the gate); `shape.lisp` itself 4.5 s as before.
`len-t-is-len` and `take-of-len` are also defined twice, with the same
statement, which ACL2 accepts.

### 7. What V7 and V8 get, and what V7 must prove

- **V7** removes `no-call-ref-run` from T2. The hypothesis enters at
  three lemmas: `fast-step-refines` (`refine-op.lisp`), and
  `fast-op-step-keeps-fmp` and `fast-op-step-keeps-inv-store` here. The
  last two need only that `fast-try-op` at `:call_ref` is
  `fast-try-rules` on that place's rules (the place lemma
  `*places-not-yet*` of `refine-step.lisp`); the store fact of §2
  already covers the four `call_ref` rules. After P1 (the fast machine
  stops `:unsupported` at a host `call_ref`) the two host rules need no
  (U) lemma.
- **V8**: `engine-run n c fm` is `(fast-run n (fm-load-ms (ms-of-config c) fm))`.
  With `(config-shape-p c)` and `(fmp fm)`, §5 gives `fm-inv` of the
  loaded stobj and `(machine-abs (fm->ms ...)) = c`, so T3 is T2 with
  its left side rewritten. `engine-config` is `machine-abs` of `fm->ms`.
- `fast-clocks n fm` is `(machine-clocks n (fm->ms fm))`, not
  executable (`defun-nx`). It is only the bound on the fuel of the
  specification. `engine-clocks n c` of T3 can be
  `(machine-clocks n (ms-of-config c))`, which is executable on the
  list machine.

### 8. The slides on the fast machine

`engine/slides/render.lsp` includes `fast/spec-result` and, on the fast
machine, prints one line per run:
`ENGINE-T2 config-shape <a> fm-inv <b> result <c>`, with `<a>`
`(config-shape-p c)` for the configuration the spec's `$instantiate` or
`$invoke` returned, `<b>` `(fm-inv fm)` after `fm-load-ms`, `<c>`
`(fast-result-p fm)` after `fast-run`.

`make -C engine slides` (the module is inside D5, S0 only; it is not
inside T2, see below): 12 runs, `T T T` on each; 7 of 7 slides identical
to V8; 112 to 428 ms per slide (`data/v6-inv/slides-fast.txt`).

What this shows: the hypotheses of the loader lemmas hold for the
configurations the spec builds for this module, so `fm-inv` there is a
consequence of a theorem and the check of `<b>` agrees with it. What it
does not show: `no-call-ref-run`. It is false for these runs, since the
compiler emits `call_ref` for every call. The caption of the viewer
reads "fast machine: not inside a theorem yet (T2 excludes call_ref
until V7 of plan2.md)".

## Open questions

- A module without a memory has no T3 (§4). If one of the demos needs
  it, the invariant has to allow a store without memories, and the
  lemmas of `refine.lisp` that assume `(consp mems)` have to be stated
  for both cases.
- `fm-inv` builds the list state to test `machine-ok` (it copies the
  memory). It is run once per load, not per step. If V8 wants a cheaper
  check, `machine-ok` reads only four fields and the length.

## Data

`engine/fast/inv.lisp`, `engine/fast/spec-result.lisp`,
`engine/rules/shape.lisp` (the rename), `engine/slides/render.lsp`,
`engine/slides/check.mjs`; `data/v6-inv/`: `measure.sh`, `measure.txt`
(prover steps of every theorem, times, hints, certificates), `gate.txt`
(`make -C engine check`), `slides-fast.txt`.
