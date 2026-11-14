; il2acl2 configuration: the counted, named exceptions to the generic
; translation (plan §1 "Rules of the game"). Keep this list short; each entry
; says why the IL cannot be translated mechanically.
(
 (:def "utf8"
  :reason "Clauses 2-4 define the bytes b_1..b_4 only through an arithmetic equation on ch (the inverse direction); no matching/binding translation exists. Hand-written in rt/builtins.lisp.")

 (:split "Step" "ctxt-instrs"
  :strategy :redex
  :reason "The generic split search of val* ++ admininstr* ++ admininstr_1* is exponential when it fails. Strategy: admininstr* ends right after the first non-value; val* is searched from longest to shortest. Completeness vs. the generic search: T8 obligation.")

 (:inverse "hint(inverse)"
  :pairs (("signed_" . "inv_signed_") ("ibytes_" . "inv_ibytes_")
          ("fbytes_" . "inv_fbytes_") ("bytes_" . "inv_bytes_")
          ("utf8" . "inv_utf8"))
  :reason "SpecTec hint(inverse ...) annotations in 3-numerics.spectec; spectec --ast does not print hints. Used to solve f(a.., x) = v for x (load rules; Bname). inv_utf8 is the hand-written partner of the utf8 override.")

 (:il-patch "Bmodule"
  :old (seq (attr (case "%" (tup (num (nat 1)))) (var "Bu32")))
  :new (seq (num 0x01) (num 0x00) (num 0x00) (num 0x00))
  :reason "Bug in the SpecTec WASM 1.0 source (A-binary.spectec: `0x00 0x61 0x73 0x6D 1:Bu32`): the binary-format version is the fixed 4 bytes 0x01 0x00 0x00 0x00, not a LEB128 u32 (which encodes 1 as the single byte 0x01). Taken literally, no real .wasm file parses.")

 (:sized "||BX||"
  :pairs (("Bsection_" . "len") ("Bcode" . "len"))
  :reason "The source premise `len = ||BX||` (byte length of what BX matched) elaborates to `len = 0` in the IL, which would reject every non-empty section. In these grammars the item after `len` is parsed from exactly `len` bytes instead, and the `len = 0` premise is dropped.")
)
