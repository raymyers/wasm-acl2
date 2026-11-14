; il2acl2 configuration: the counted, named exceptions to the generic
; translation (plan §1 "Rules of the game"). Keep this list short; each entry
; says why the IL cannot be translated mechanically.
(
 (:def "utf8"
  :reason "Clauses 2-4 define the bytes b_1..b_4 only through an arithmetic equation on ch (the inverse direction); no matching/binding translation exists. Hand-written in rt/builtins.lisp.")
)
