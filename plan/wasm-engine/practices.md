# Proof practice for the engine books

The short form of these rules is in the Tech guidelines of
[step2.md](step2.md). This file has the source, the reason and what
each rule changes in `engine/`.

From the ACL2 documentation topic `BEST-PRACTICES` and its subtopics
(`theory-management`, `naming-rewrite-rules`,
`conventional-normal-forms`, `working-with-packages`), read from
`books/doc/practices.lisp` of our ACL2 8.7. The file on the `master`
branch of `acl2/acl2` was compared on 2026-11-17: it differs in one
cross-reference and in no recommendation. All ten subtopics were read;
`file-names` is already followed, and `finite-reasoning` (GL for
bounded values) has no use here while the engine calls the spec's own
numeric functions (plan.md D6). Each rule below names what it changes
in `engine/`.

| Practice (the topic's words, shortened) | In `engine/` today | Rule for this plan |
|---|---|---|
| "`include-book` and `in-theory` events should be `local` where possible"; top-level ones "at the top of the book" | 3 local theory events in 15 books; `ok.lisp`, `clock0.lisp` and `refine-op.lisp` disable definitions non-locally in mid-book | A book has one header: includes, then one theory block. Library includes (`std/lists`, arithmetic) are always `local`; the lemmas a later book needs are restated in `engine/lib/` |
| "Most functions (especially non-recursive) should be disabled by default" | Definitions stay enabled; proofs then carry disable lists of 20 to 30 names (`fast-step-refines`) | Every machine definition is followed by its lemmas and then disabled, in the defining book. A proof enables what it opens |
| "Try to avoid subgoal hints... consider factoring out a subgoal into an auxiliary lemma" | None found; keep it so | No `"Subgoal"` hint. A case that needs one becomes a lemma |
| "The less hints the better. Consider whether `:use` or `:expand` hints may suggest good general-purpose rules" | `refine-op.lisp`: seven `:use` hints with hand-built instances | Before a `:use`, try the fact as a rewrite rule with the right free variables. Recursive spec functions get one `:expand`-style rewrite rule each, stated once (`step-opener`), not an `:expand` per proof |
| "Avoid short proof timeout windows... use step limits instead" | `set-prover-step-limit` in `refine-op.lisp` | Every proof book sets a step limit. No time limits |
| Rule names: `f-of-g`, `-when-hyp`, `-under-equiv`; no `lemma1`, `crock` | Mostly followed (`machine-abs-of-ms`); some not (`car-t-is-car`) | New lemmas follow it; generated lemmas are `<rule>-<property>` |
| "Write lemmas in terms of `(mv-nth n ...)`"; include `tools/mv-nth` | Lemmas use `cadddr` of an `mv` (`fast-try-rules-keeps-bytes`) | New lemmas use `mv-nth`; `mv-nth` disabled. Old ones are converted when their book is next touched |
| A widget library should not change how one reasons about built-ins | `machine.lisp` defines its own `take-n`, `app`, `len-t`, `rev-onto` | Keep them (guard `t` is why they exist), but V1 proves each equal to the built-in under the invariant and normalizes to the built-in, so one list library serves both |
| "A book should use either `defun` or `define`, not both" | `defun`/`defthm` everywhere | Stay with `defun`/`defthm`. No `std/util` conversion |
| "Sets of rules known to loop should be declared incompatible" (`theory-invariant`) | None | When V1 adds an opener and its inverse, a `theory-invariant` goes with them |
| Packages: `package.lsp`, empty `portcullis.lisp`, `cert.acl2` | Followed | No change |
| Certifiable books `.lisp`, scripts `.lsp` | Followed | No change |
| "Avoid introducing new Makefiles", use `cert.pl` | One Makefile that calls `cert.pl` | No change |
| Whitespace, comment and header rules | The header line is in every book since V0 | A new book starts with the line pointing at `LICENSE` |

Three rules of our own, from what the notes record:

- **Generated lemma families end with an exact census.** `frame`,
  `refine` and `refine-step` already fail if the set of rules without
  a lemma is not the recorded one. Every new generated family does the
  same, and the recorded set must be empty when its milestone closes.
- **A generator never runs silently.** The 35-minute run of
  [E6-list-machine](notes/E6-list-machine.md) lost which lemmas had
  proved. Generators print one line per lemma and each lemma has a step
  limit.
- **Constants first, both orientations.** Rewrite rules about a head
  keyword are stated as `(equal (car x) kw)` and `(equal kw (car x))`
  ([E3-theorem](notes/E3-theorem.md)).
