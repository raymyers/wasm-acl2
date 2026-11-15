; PROVISIONAL (wasm3 prep P2): the WASM 1.0 config without its 1.0-only
; :il-patch (Bmodule) and :rel-override (Module_ok) entries, i.e. what the
; P0/P1 probes used. Several remaining entries name 1.0 ids that do not exist
; in 3.0 (W5); config validation (P2) and P3 replace them.
; Removed by P2 config validation: ("bytes_" . "inv_bytes_") (no bytes_ here).
; P3: inverse pairs now come from hint(inverse) in the IL (no :inverse entry).
; il2acl2 configuration: the counted, named exceptions to the generic
; translation (plan §1 "Rules of the game"). Keep this list short; each entry
; says why the IL cannot be translated mechanically.
(
 (:def "utf8" :inverse "inv_utf8"
  :reason "Clauses 2-4 define the bytes b_1..b_4 only through an arithmetic equation on ch (the inverse direction); no matching/binding translation exists. Hand-written in rt/builtins.lisp, with its inverse inv_utf8 (used to solve utf8(x) = bytes in Bname; the other inverse pairs come from hint(inverse) in the IL).")

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
  :pairs (("Instr_ok" . 1) ("Instrs_ok" . 1))
  :reason "Instruction typing recurses into sub-instructions under an EXTENDED context (block/loop/if add a label), so the size of all inputs can grow. The instruction component (index 1) decreases, or stays equal with a smaller stack (frame). Recursive premise calls are ordered lexicographically by (size of component 1, size of all inputs).")

 (:memoize "search memo"
  :rels ("Instr_ok" "Instrs_ok")
  :reason "Performance only (memoization is semantically the identity). Instrs_ok/seq splits instr_1* instr_2* at every point and recurses on both halves, so REJECTING an ill-typed sequence explores exponentially many derivations (17 instructions: ~60 s). Memoizing the typing functions on hons-copied arguments makes the search polynomial (sub-sequences x stacks).")

 (:sized "||BX||"
  :pairs (("Bsection_" . "len") ("Bcode" . "len"))
  :reason "The source premise `len = ||BX||` (byte length of what BX matched) elaborates to `len = 0` in the IL, which would reject every non-empty section. In these grammars the item after `len` is parsed from exactly `len` bytes instead, and the `len = 0` premise is dropped.")
 (:witness "single-witness premises"
  :rels ("Instr_ok" "Instrs_ok" "Ref_ok" "Externaddr_ok")
  :reason "The output variant R/SPLIT of these relations drops rules whose output is not computable from the inputs, and some premise takes a value from it and then constrains it, so that premise tries ONE witness (the translator reports any other such premise as an error, `witness choice`; that is how Heaptype_sub/trans is dropped instead of compiled with one arbitrary heaptype'). PROVISIONAL, carried over from WASM 1.0 and not yet argued for 3.0: the premises are Instr_ok/block, loop, if, try_table and Instrs_ok/seq, sub (they take an instruction type from Instr_ok/SPLIT or Instrs_ok/SPLIT, which drop the stack-polymorphic rules and, in 3.0, the subsumption and frame rules), and Ref_ok/sub, Externaddr_ok/sub (they take the type from the relation's own output variant, which drops only `sub`, and then check subtyping; complete if the other rules give one type and subtyping is transitive). Whether one witness is enough for instruction typing under 3.0 subsumption is the go/no-go of wasm3 M6.")

)
