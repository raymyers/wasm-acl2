; il2acl2: SpecTec IL -> ACL2 translator (plan/wasm1-translation).
(in-package "IL2ACL2")
(include-book "mangle")
(program)
(set-state-ok t)

; The definitions and the hint forms of an IL file: (mv erp defs hints state).
(defun read-il (filename state)
  (mv-let (erp forms state) (read-il-file filename state)
    (if erp (mv erp nil nil state)
      (mv-let (defs hints) (split-hints forms)
        (mv nil defs hints state)))))

; Read FILENAME and run the T1 checks. Returns (mv erp summary state), where
; erp is non-nil iff the IL fails the schema / dependency-order check (hint
; forms included) or the mangling is not injective. :forms counts the
; definitions only; :hints the hint forms.
(defun il-check (filename state)
  (mv-let (erp forms hints state)
    (read-il filename state)
    (if erp
        (mv erp nil state)
      (let* ((errs (append (check-il-forms forms nil nil)
                           (check-hints hints (all-def-names forms) nil)))
             (table (mangle-table forms)))
        (mv-let (collisions renamed atom-collisions)
          (mangle-report table)
          (mv (and (or errs collisions)
                   (msg "IL check failed:~|schema/order errors: ~x0~|mangle collisions: ~x1"
                        errs collisions))
              (list :forms (len forms)
                    :hints (len hints)
                    :heads (count-heads forms nil)
                    :names (list :typ (len (cdr (assoc :typ table)))
                                 :def (len (cdr (assoc :def table)))
                                 :rel (len (cdr (assoc :rel table)))
                                 :rule (len (cdr (assoc :rule table)))
                                 :gram (len (cdr (assoc :gram table)))
                                 :var (len (cdr (assoc :var table)))
                                 :atom (len (cdr (assoc :atom table))))
                    :renamed renamed
                    :atom-collisions atom-collisions)
              state))))))
