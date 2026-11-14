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
          ("fbytes_" . "inv_fbytes_") ("bytes_" . "inv_bytes_"))
  :reason "SpecTec hint(inverse ...) annotations in 3-numerics.spectec; spectec --ast does not print hints. Used to solve f(a.., x) = v for x (load rules).")
)
