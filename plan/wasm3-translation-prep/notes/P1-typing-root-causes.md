# Root causes of the 3.0 type-validation, subtyping and instruction-typing failures

- Milestone: P1 (re-run the probe and replace the S2 row with real root
  causes for the type-validation and subtyping groups)
- Date: 2026-11-14
- Repo commit: 507f7f9 plus this note's commit
- Status: draft (input to the typing triage, model-choice item 2, and to the
  P4 mode table design)
- Feeds wasm3 plan: gap list, risks, scheme delta (modes)
- Incorporated in wasm3 plan: no

## Summary

The typing failures are mostly a **mode-selection** problem, not missing
constructs. In `:multi` (check variant + split variant, the 1.0 approach for
`Instr_ok`) the 19-relation type group fails 2 of its rules (both G8,
existential index) and `Instr_ok`/`Instrs_ok` 3 (all G5). The baseline's
"every `: OK` judgement is stubbed" came from `:fun`. One rule that *does*
compile, `Heaptype_sub/trans`, is compiled with a single witness: it
counts as translated but is incomplete. "Compiles" is not "complete".

## Findings

### Attempt scores (failing rules, from the P1 probe's attempt log)

| Group | `:fun` | `:check` (failing members only) | `:multi` (all members) |
|---|---|---|---|
| Type validation + subtyping (`Heaptype_ok` ... `Fieldtype_sub`, 19 relations) | 22 | 9 | **2** |
| `Instr_ok`, `Instrs_ok` | 15 | 9 | **3** |

The `:check` attempt demotes only the members that failed in `:fun`. In the
type group 6 of 19 members compiled in `:fun` (`Reftype_ok`, `Fieldtype_ok`,
`Reftype_sub`, `Resulttype_sub`, `Storagetype_sub`, `Fieldtype_sub`) and so
stayed `:fun` in attempt 2. An all-`:check` assignment is not among the
three attempts. The mode table (P4) should try it.

### Why `:fun` fails (mode artifacts, 20 rules)

`:fun` treats the last tuple component as the output. For `C ⊢ x : OK`
that component is the subject `x`. For `C ⊢ x <: y` it is `y`. Rules then fail for
lack of a way to produce the subject: "checker relation with unbound
arguments" (`Valtype_ok/num` calls `Numtype_ok: C ⊢ numtype : OK` with
`numtype` unknown), "unbound variable" (`Heaptype_ok/abs`, `Rectype_ok2/empty`),
"iterated premise without inputs" (`Resulttype_ok`, `Comptype_ok/struct`).
None of these is a missing translator feature.

What the plan's S2 row guessed, checked:

| S2 guess | Result |
|---|---|
| Extra index arguments (`C ⊢ subtype : OK(x, i)`) | Not a cause: `Subtype_ok2` and `Rectype_ok2` compile in `:multi` |
| Existential intermediates (`Heaptype_sub/trans`) | Compiles in `:multi`, but with one witness (below) |
| Premises that look up `C.TYPES[typeidx]` with the index bound late | `:fun` artifact (`Typeuse_ok/typeidx`: `typeidx` is the subject) |

### The 2 real failures in `:multi`: existential index (G8, new)

- `Deftype_sub/super`: `C ⊢ deftype_1 <: deftype_2` if
  `$unrolldt(deftype_1) = SUB final? typeuse* ct` and
  `C ⊢ typeuse*[i] <: deftype_2`. `i` appears only there and in the
  side condition `i < |typeuse*|` that elaboration adds.
- `Heaptype_sub/rec-sub`: `C ⊢ REC i <: typeuse*[j]` if
  `C.RECS[i] = SUB final? typeuse* ct`, so `j` is existential the same way
  (here in the conclusion, under check mode).
- Same shape, outside the D3 scope: `ImmutReachable/ref.struct`,
  `ref.array`, `ref.exn` (`i < |s.STRUCTS[a].FIELDS|`).
- Proposal: a variable bound only by `v < |l|` (with `l` bound) becomes a
  bounded existential: try `v = 0 .. |l|-1`. This is finite, complete, and
  first-order. It is the premise-level analogue of `citer`'s counters (G3).

### `Instr_ok` in `:multi`: only G5

`select-impl`, `array.new_data`, `array.init_data` fail on a disjunction
whose branches bind different variables (`t' = numtype \/ t' = vectype`).
The variable is bound before the disjunction in check mode, so a membership
test suffices. The stack-polymorphic rules (`unreachable`, `br`,
`return_call*`, `throw`, ...) compile in the check variant and are dropped
only from the split variant, as in 1.0. The rules dropped from split
variants are listed in the probe report (50 entries over all attempts, D3 scope).

### Compiled but incomplete: single-witness existentials

`Heaptype_sub/trans` (`C ⊢ ht_1 <: ht_2` if `C ⊢ ht' : OK`,
`C ⊢ ht_1 <: ht'`, `C ⊢ ht' <: ht_2`) compiles in `:multi` as:

```
(let ((%T0 (HEAPTYPE_OK/SPLIT C)))          ; ht' := the first OK heap type
  (and %T0 (let ((HEAPTYPE-PRIME (car %T0)))
             (and <size check> (HEAPTYPE_SUB C HEAPTYPE_1 HEAPTYPE-PRIME)
                  <size check> (HEAPTYPE_SUB C HEAPTYPE-PRIME HEAPTYPE_2)))))
```

(From compiling the group with every member forced to `:multi`; script in
Data.) The split variant of `Heaptype_ok` returns one heap type for `C`, so
the rule tries one candidate `ht'` instead of all of them. It is sound, since a
true result has a derivation, but it is not complete, and the attempt score does
not show it. The size checks make the recursion terminate; they also cut off
any `ht'` larger than the inputs.

Consequences:

- The "failing rules" count is a lower bound on incompleteness. A typing
  relation can lose derivations without any logged error.
- `trans` is the textbook case for an algorithmic reading: WASM's
  declarative subtyping includes it, but the other `Heaptype_sub` rules are
  meant to make it admissible. Dropping it (with that argument written down)
  may be the right translation. This is a triage decision (model-choice item
  2, a Fable task), not a mechanical one.
- The P4 mode table should flag any premise that binds a variable through a
  relation's split variant when the variable is not otherwise determined
  (a "witness choice"). Those are where incompleteness hides.

## Open questions

- Is `trans` admissible in 3.0 subtyping, so that dropping it is complete?
  (Triage.)
- Which other rules bind an existential through a split variant? A list
  requires the P4 flag above. Today no report shows it.
- With an all-`:check` assignment for the `: OK` and `<:` judgements, are the
  `:multi` results kept (2 failing rules), and do callers that need outputs
  (`Instr_ok` needs `Instrtype_ok` only as a check) still compile?

## Data

- `data/probe-P1-2026-11-14/report-3.0-core.txt` (attempt log, partial
  relations), `rules-3.0-core.txt` (failing rule × mode),
  `errors-3.0-core.lsp`.
- `data/probe-P1-2026-11-14/force-multi.lsp`: compiles every form before
  the type group, then the group with every member forced to `:multi`, and
  prints the failing members and `HEAPTYPE_SUB`. Run from `translate/` after
  `make probe SPEC=3.0`: `acl2 < ../plan/wasm3-translation-prep/notes/data/probe-P1-2026-11-14/force-multi.lsp`.
  Result: `BAD ("Deftype_sub" "Heaptype_sub")`, 4 errors.
