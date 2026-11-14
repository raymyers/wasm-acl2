; PROVISIONAL (wasm3 prep P2): the WASM 1.0 config without its 1.0-only
; :il-patch (Bmodule) and :rel-override (Module_ok) entries, i.e. what the
; P0/P1 probes used. Several remaining entries name 1.0 ids that do not exist
; in 2.0 (W5); config validation (P2) and P3 replace them.
; Removed by P2 config validation: ("bytes_" . "inv_bytes_") (no bytes_ here).
; P3: inverse pairs now come from hint(inverse) in the IL (no :inverse entry).
; il2acl2 configuration: the counted, named exceptions to the generic
; translation (plan §1 "Rules of the game"). Keep this list short; each entry
; says why the IL cannot be translated mechanically.
(
 (:def "utf8" :inverse "inv_utf8"
  :reason "Clauses 2-4 define the bytes b_1..b_4 only through an arithmetic equation on ch (the inverse direction); no matching/binding translation exists. Hand-written in rt/builtins.lisp, with its inverse inv_utf8 (used to solve utf8(x) = bytes in Bname; the other inverse pairs come from hint(inverse) in the IL).")

 (:builtins "categories"
  :numeric ("s33_to_u32")
  :reason "$s33_to_u32 is declared without hint(builtin) but is a numeric conversion (S7), so it is listed as :numeric.")

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
 (:modes "declared modes"
  :pairs (("Instr_ok" . :multi) ("Instrs_ok" . :multi))
  :reason "Instruction typing is :multi, as WASM 1.0 infers it (the check variant keeps the stack-polymorphic rules, the split variant computes output stacks); the 2.0 inference does not find it (wasm3 prep P4). Replace by the mode table (W1).")

 (:il-patch "Binstr"
  :old
    (prod
      (exp "b'" (var "byte"))
      (exp "b" (var "byte"))
      (seq
        (seq (num 0xFD))
        (seq (attr (case "%" (tup (num (nat 12)))) (var "Bu32")))
        (seq (iter (attr (var "b") (var "Bbyte")) (listn (num (nat 16)))))
      )
      (case
        "VCONST"
        (tup
          (case "V128" (tup))
          (case "%" (tup (proj (uncase (var "b'") "%") 0)))
        )
      )
      (if
        (cmp
          eq
          bool
          (call
            "ibytes_"
            (exp (num (nat 128)))
            (exp (case "%" (tup (proj (uncase (var "b'") "%") 0))))
          )
          (list (var "b"))
        )
      )
    )
  :new
    (prod
      (exp "b*" (iter (var "byte") list))
      (seq
        (seq (num 0xFD))
        (seq (attr (case "%" (tup (num (nat 12)))) (var "Bu32")))
        (seq (iter (attr (var "b") (var "Bbyte")) (listn (num (nat 16))) (dom "b" (var "b*")))))
      (case "VCONST"
        (tup (case "V128" (tup))
             (call "inv_ibytes_" (exp (num (nat 128)))
                   (exp (iter (var "b") (listn (num (nat 16))) (dom "b" (var "b*"))))))))
  :reason "Elaboration bug in the WASM 2.0 source (A-binary.spectec: `0xFD 12:Bu32 (b:Bbyte)^16 => VCONST V128 b' -- if $ibytes_(128, b') = b`): b and b' are elaborated as single bytes, the ^16 iteration binds no list, and the premise compares with the one-element list [b], so no v128.const decodes. Patched to the 3.0 source's form, `VCONST V128 $inv_ibytes_(128, b^16)`.")

 (:il-patch "Binstr"
  :old
    (prod
      (exp "l" (var "labelidx"))
      (seq
        (seq (num 0xFD))
        (seq (attr (case "%" (tup (num (nat 13)))) (var "Bu32")))
        (seq
          (iter
            (attr
              (case "%" (tup (proj (uncase (var "l") "%") 0)))
              (var "Blaneidx")
            )
            (listn (num (nat 16)))
          )
        )
      )
      (case
        "VSHUFFLE"
        (tup
          (case "%X%" (tup (case "I8" (tup)) (case "%" (tup (num (nat 16))))))
          (list (case "%" (tup (proj (uncase (var "l") "%") 0))))
        )
      )
    )
  :new
    (prod
      (exp "l*" (iter (var "labelidx") list))
      (seq
        (seq (num 0xFD))
        (seq (attr (case "%" (tup (num (nat 13)))) (var "Bu32")))
        (seq (iter (attr (case "%" (tup (proj (uncase (var "l") "%") 0))) (var "Blaneidx"))
                   (listn (num (nat 16))) (dom "l" (var "l*")))))
      (case "VSHUFFLE"
        (tup (case "%X%" (tup (case "I8" (tup)) (case "%" (tup (num (nat 16))))))
             (iter (case "%" (tup (proj (uncase (var "l") "%") 0))) (listn (num (nat 16))) (dom "l" (var "l*"))))))
  :reason "Same elaboration bug for i8x16.shuffle (`0xFD 13:Bu32 (l:Blaneidx)^16 => VSHUFFLE (I8 X 16) l^16`): l is a single lane index and the iteration binds no list. Patched to bind l* through the iteration, as the 3.0 source does.")

)
