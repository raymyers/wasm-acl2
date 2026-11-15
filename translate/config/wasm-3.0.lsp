; il2acl2 configuration for WASM 3.0 (wasm3 M0: checked in with the IL and
; validated against it on every run; config-entry-errors). The counted,
; named exceptions to the generic translation (plan §1 "Rules of the game").
; Keep this list short; each entry says why the IL cannot be translated
; mechanically. History: it began as the 1.0 config without the 1.0-only
; :il-patch (Bmodule) and :rel-override (Module_ok) entries (prep P2);
; ("bytes_" . "inv_bytes_") went in P2 (no bytes_ here); since P3 the
; inverse pairs come from hint(inverse) in the IL (no :inverse entry).
(
 (:def "utf8" :inverse "inv_utf8"
  :reason "Clauses 2-4 define the bytes b_1..b_4 only through an arithmetic equation on ch (the inverse direction); no matching/binding translation exists. Hand-written in rt/builtins.lisp, with its inverse inv_utf8 (used to solve utf8(x) = bytes in Bname; the other inverse pairs come from hint(inverse) in the IL).")

 (:def "utf8single"
  :reason "Like utf8 (S5): each clause defines the bytes of one character only through an arithmetic equation on ch (ch = 2^6*(b_1 - 0xC0) + $cont(b_2), ...), the inverse direction, so there is no matching translation. Hand-written in rt/builtins-3.0.lisp from the same four clauses (no result for a surrogate or above U+10FFFF). 3.0 defines $utf8 through it, but the utf8 override above replaces that definition, so no generated code calls $utf8single today; the override removes the last stub of a numeric def (wasm3 M1).")

 (:builtins "categories"
  :choice ("ND" "R_fmadd" "R_fmin" "R_fmax" "R_idot" "R_idot_add" "R_iq15mulr"
           "R_trunc_u" "R_trunc_s" "R_swizzle" "R_laneselect")
  :host ("hostcall")
  :numeric ("s33_to_u32")
  :reason "Clause-less defs that are not plain numeric builtins (S7): $ND and the $R_* relaxed-SIMD parameters are nondeterminism choices (fixed by the D4 policy, 3.0-numerics.relaxed.spectec); $hostcall is the host-function hook (4.0-execution.configurations). $s33_to_u32 (3.1-numerics.scalar) is declared without hint(builtin) but is a numeric conversion, so it is listed as :numeric.")

 (:split "Step" "ctxt-instrs"
  :strategy :redex
  :reason "The generic split search of val* ++ admininstr* ++ admininstr_1* is exponential when it fails. Strategy: admininstr* ends right after the first non-value; val* is searched from longest to shortest. Completeness vs. the generic search: T8 obligation.")

 (:decreasing "termination order"
  :pairs (("Instr_ok" . 1) ("Instrs_ok" . 1) ("Step" 0 2))
  :reason "Instruction typing recurses into sub-instructions under an EXTENDED context (block/loop/if add a label), so the size of all inputs can grow. The instruction component (index 1) decreases, or stays equal with a smaller stack (frame). Recursive premise calls are ordered lexicographically by (size of component 1, size of all inputs). Step (wasm3 M3): the pair (\"Step\" 0 2) names the instructions of the configuration (:|%;%| state instrs). Every Step rule with a Step premise (ctxt-instrs, ctxt-label, ctxt-handler, ctxt-frame) steps a proper part of the instruction list, so this component decreases in every derivation and no derivation is cut. Without it the check compared the size of the whole configuration, store included: measured 5.39 ms per step with one 64 KiB page in the store against 0.014 ms without (notes M3-execution).")

 (:memoize "search memo" :recursive nil
  :rels ("Instr_ok" "Instrs_ok")
  :reason "Performance only (memoization is semantically the identity). Instrs_ok/seq splits instr_1* instr_2* at every point and recurses on both halves, so REJECTING an ill-typed sequence explores exponentially many derivations (17 instructions: ~60 s). Memoizing the typing functions on hons-copied arguments makes the search polynomial (sub-sequences x stacks). 3.0 adds :recursive nil: memoize wraps the compiled function instead of recompiling its body (the memoized function R/%M recurses only through its entry R, which calls the memoized R/%M, so recursive calls are still memoized); with the default the four memoize events of 2_3-validation_instructions took 22 s at every include of that book (12 books include it), measured in wasm3 M0.")

 (:sized "||BX||"
  :pairs (("Bsection_" . "len") ("Bcode" . "len"))
  :reason "The source premise `len = ||BX||` (byte length of what BX matched) elaborates to `len = 0` in the IL, which would reject every non-empty section. In these grammars the item after `len` is parsed from exactly `len` bytes instead, and the `len = 0` premise is dropped.")
 (:witness "single-witness premises"
  :rels ("Instr_ok" "Instrs_ok" "Ref_ok" "Externaddr_ok")
  :reason "The output variant R/SPLIT of these relations drops rules whose output is not computable from the inputs, and some premise takes a value from it and then constrains it, so that premise tries ONE witness (the translator reports any other such premise as an error, `witness choice`; that is how Heaptype_sub/trans is dropped instead of compiled with one arbitrary heaptype'). PROVISIONAL, carried over from WASM 1.0 and not yet argued for 3.0: the premises are Instr_ok/block, loop, if, try_table and Instrs_ok/seq, sub (they take an instruction type from Instr_ok/SPLIT or Instrs_ok/SPLIT, which drop the stack-polymorphic rules and, in 3.0, the subsumption and frame rules), and Ref_ok/sub, Externaddr_ok/sub (they take the type from the relation's own output variant, which drops only `sub`, and then check subtyping; complete if the other rules give one type and subtyping is transitive). Whether one witness is enough for instruction typing under 3.0 subsumption is the go/no-go of wasm3 M6.")

 (:fuel "type validation and subtyping"
  :rels ("Heaptype_ok")
  :reason "The rec group of Heaptype_ok (19 relations: type validation and subtyping) terminates by a depth bound, (%TFUEL) in rt/prelude.lisp, instead of the generated check that every recursive premise has smaller inputs. That check cut valid derivations: a rule that passes its arguments unchanged to another relation of the group (Valtype_sub/ref to Reftype_sub), one that replaces a type index by the defined type (Heaptype_sub/typeidx-l), one that recurses under a larger context (Deftype_ok). Measured: 9 of 22 type cases right with the size check (wasm3 notes, review-checker-blind-spots). A derivation deeper than the bound is not found; a failing search through a cyclic context ends at the bound.")

 (:program "certification mode"
  :reason "Every generated event is admitted in :program mode (the book default `(program)`), not through %TRY-LOGIC/%TRY-GUARDS. Not a translation exception: it bounds certification time. With the logic attempts, one guard proof in 5_2-binary_types ran more than 15 CPU minutes (prep P5-conformance), and the prover step limits do not bound wall time. Execution is the same in both modes. Removed in wasm3 M9 (logic mode and proofs), which needs per-event time limits first.")

 (:il-patch "Belem"
  :old (list (iter (case "REF.FUNC" (var "y")) list (dom "y" (var "y*"))))
  :new (iter (list (case "REF.FUNC" (var "y"))) list (dom "y" (var "y*")))
  :reason "Elaboration of the source `ELEM rt (REF.FUNC y)* ...` (flags 0-3): the element list has type expr* = (instr*)*, and SpecTec coerces the whole instr* `(REF.FUNC y)*` into a one-element list, [(REF.FUNC y)*]: ONE expression holding every ref.func. The binary format (prose) and flags 4-7 give one expression per element, [REF.FUNC y]*. Unpatched, a decoded segment with n functions has 1 element of n instructions, which Elem_ok rejects and instantiation would get wrong. The patch writes the iteration of the singleton list (all 4 rules; 2.0's IL has the same shape). Found in wasm3 M2.")
)
