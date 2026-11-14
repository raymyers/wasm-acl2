; T1 exit check: the checked-in IL parses, passes the schema and
; dependency-order check, and mangles injectively. Certification fails
; otherwise.
(in-package "IL2ACL2")
(include-book "../il2acl2/top")

(make-event
 (mv-let (erp summary state)
   (il-check "../il/wasm-1.0.il.sexp" state)
   (cond (erp (mv erp nil state))
         ((not (equal (cadr (member :forms summary)) 318))
          (mv (msg "Expected 318 top-level forms, got ~x0" summary) nil state))
         (t (prog2$ (cw "~%T1 IL summary:~%~x0~%" summary)
                    (mv nil '(value-triple :t1-il-ok) state))))))

; Negative tests: the checker rejects malformed or out-of-order IL.
(make-event
 (if (and (check-il-forms '((def "f" nat (clause (frob 1)))) nil nil)
          (check-il-forms '((typ "a" (inst (alias (var "nope"))))) nil nil)
          (check-il-forms '((typ "a" (inst (alias nat)))
                            (typ "a" (inst (alias nat)))) nil nil)
          (check-il-forms '((def "g" nat (clause (call "h")))
                            (def "h" nat (clause (num (nat 0))))) nil nil)
          (null (check-il-forms
                 '((def "id" (typ "X") (exp "x" (var "X")) (var "X")
                     (clause (typ "X") (exp "x" (var "X"))
                             (typ (var "X")) (exp (var "x")) (var "x"))))
                 nil nil)))
     '(value-triple :t1-negative-ok)
   (er hard 't1 "schema negative tests failed")))

; Mangling examples (plan §2.1).
(make-event
 (let ((m (mangle-ids '("n" "N" "t" "x'*" "val_1") '("n" "N" "t" "x'*" "val_1")
                      nil *reserved-var-names*)))
   (if (and (equal m '(("n" . "N") ("N" . "N^U") ("t" . "T^R")
                       ("x'*" . "X-PRIME-STAR") ("val_1" . "VAL_1")))
            (equal (atom-tag "CONST") "CONST")
            (equal (atom-tag "LABEL_%{%}%") "LABEL_%{%}%")
            (equal (atom-tag "MEMORY.GROW") "MEMORY.GROW"))
       '(value-triple :t1-mangle-ok)
     (er hard 't1 "mangle examples failed: ~x0" m))))
