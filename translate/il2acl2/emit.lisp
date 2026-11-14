; Emitter: compile the whole IL and write translate/gen/ (plan §1, §3).
;
; Two phases, because the W1T package's imports depend on the generated
; names (every ACL2 export whose name we define or bind is left out):
;   phase 1 (package IL2ACL2): compile, write gen/package.lsp + portcullis
;   -- the run script then ld's gen/package.lsp --
;   phase 2 (current package W1T): intern names, print gen/wasm1.lisp
; Both phases are deterministic functions of the IL and the config.
(in-package "IL2ACL2")
(include-book "top")
(include-book "compile")
(program)
(set-state-ok t)

; --- Generated-name markers --------------------------------------------

(defun collect-gsyms (x acc)
  (cond ((gsym-p x) (if (member-equal (cdr x) acc) acc (cons (cdr x) acc)))
        ((consp x) (collect-gsyms (cdr x) (collect-gsyms (car x) acc)))
        (t acc)))

(defun convert-gsyms (x)
  (cond ((gsym-p x) (intern$ (cdr x) "W1T"))
        ((consp x) (cons (convert-gsyms (car x)) (convert-gsyms (cdr x))))
        (t x)))

; Every symbol in generated code must be a W1T, ACL2, or keyword symbol.
(defun foreign-symbols (x acc)
  (cond ((and (symbolp x) x (not (eq x t))
              (not (member-equal (symbol-package-name x) (list "W1T" "ACL2" "KEYWORD" "COMMON-LISP"))))
         (if (member-eq x acc) acc (cons x acc)))
        ((consp x) (foreign-symbols (cdr x) (foreign-symbols (car x) acc)))
        (t acc)))

(defun wrap-try-logic (evs)
  (if (endp evs) nil
    (cons (list (intern$ "%TRY-LOGIC" "W1T") (car evs)) (wrap-try-logic (cdr evs)))))

(defun clashing-exports (syms names)
  (cond ((endp syms) nil)
        ((member-equal (symbol-name (car syms)) names)
         (cons (car syms) (clashing-exports (cdr syms) names)))
        (t (clashing-exports (cdr syms) names))))

(defun sort-strings (l) (acl2::merge-sort-lexorder l))

; --- Output ------------------------------------------------------------

(defun princ-lines (lines channel state)
  (if (endp lines) state
    (let* ((state (princ$ (car lines) channel state))
           (state (newline channel state)))
      (princ-lines (cdr lines) channel state))))

(defun print-forms (forms channel state)
  (if (endp forms) state
    (mv-let (col state)
      (acl2::fmt1! "~x0~%" (list (cons #\0 (car forms))) 0 channel state nil)
      (declare (ignore col))
      (let ((state (newline channel state)))
        (print-forms (cdr forms) channel state)))))

(defun write-file (filename lines forms state)
  (mv-let (channel state)
    (open-output-channel filename :character state)
    (if (null channel)
        (mv (msg "Cannot write ~s0" filename) state)
      (let* ((state (princ-lines lines channel state))
             (state (print-forms forms channel state))
             (state (close-output-channel channel state)))
        (mv nil state)))))

; Header items are formatted as single-line strings, so the header is
; plain comment lines regardless of printer settings.
(defun comment-lines (prefix items)
  (if (endp items) nil
    (cons (concatenate 'string prefix (car items))
          (comment-lines prefix (cdr items)))))

(defun builtin-strings (bs)
  (if (endp bs) nil
    (cons (concatenate 'string (car (car bs)) "/" (nat-str (cdr (car bs))))
          (builtin-strings (cdr bs)))))

(defun config-strings (config)
  (if (endp config) nil
    (cons (concatenate 'string (symbol-name (car (car config))) " " (second (car config))
                       ": " (or (cadr (member :reason (car config))) ""))
          (config-strings (cdr config)))))

(defun join-words (l)
  (cond ((endp l) "")
        ((endp (cdr l)) (car l))
        (t (concatenate 'string (car l) " " (join-words (cdr l))))))

; --- Phase 1 -----------------------------------------------------------

(defun config-overrides (config)
  ;; config: list of entries (:def "id" :reason "...")
  (cond ((endp config) nil)
        ((eq (car (car config)) :def)
         (cons (second (car config)) (config-overrides (cdr config))))
        (t (config-overrides (cdr config)))))

(defun skipped-summary (sk)
  (if (endp sk) nil
    (cons (if (is (car sk) "REC")
              (concatenate (quote string) "rec " (join-words (strip-cdrs (def-names (car sk)))))
            (concatenate (quote string) (string-downcase (head (car sk))) " " (second (car sk))))
          (skipped-summary (cdr sk)))))

; Returns (mv erp state); stores the compiled results in state global W1T-GEN.
(defun gen-phase1 (il-file config-file outdir state)
  (mv-let (erp summary state) (il-check il-file state)
    (declare (ignore summary))
    (if erp (mv erp state)
      (mv-let (erp forms state) (read-il-file il-file state)
        (declare (ignore erp))
        (mv-let (erp cfg state) (read-il-file config-file state)
          (if erp (mv erp state)
            (let* ((config (car cfg))
                   (cx (list (cons :tbl (mangle-table forms))
                             (cons :overrides (config-overrides config)))))
              (mv-let (events builtins skipped cx) (cforms forms cx)
                (let* ((names (collect-gsyms events
                                             (strip-cars builtins)))
                       (clash (clashing-exports *acl2-exports* names))
                       (state (f-put-global 'w1t-gen
                                            (list :events events :builtins builtins
                                                  :skipped skipped
                                                  :stubs (reverse (cx-get :stubs cx))
                                                  :errs (reverse (cx-get :errs cx))
                                                  :config config)
                                            state)))
                  (mv-let (erp state)
                    (write-file
                     (concatenate 'string outdir "package.lsp")
                     (list "; GENERATED by translate/il2acl2 -- do not edit."
                           "; W1T: the package of the generated WASM 1.0 semantics. It imports"
                           "; *acl2-exports* minus every export whose name the generated code"
                           "; defines or binds."
                           "(in-package \"ACL2\")")
                     (list (list 'defpkg "W1T"
                                 (list 'set-difference-eq '*acl2-exports*
                                       (list 'quote (acl2::merge-sort-symbol< clash)))))
                     state)
                    (if erp (mv erp state)
                      (mv-let (erp state)
                        (write-file (concatenate 'string outdir "portcullis.acl2")
                                    (list "; GENERATED -- do not edit." "(ld \"package.lsp\")")
                                    nil state)
                        (if erp (mv erp state)
                          (mv-let (erp state)
                            (write-file (concatenate 'string outdir "portcullis.lisp")
                                        (list "; GENERATED -- do not edit."
                                              "; Empty book whose portcullis defines the W1T package."
                                              "(in-package \"ACL2\")")
                                        nil state)
                            (if erp (mv erp state)
                              (write-file (concatenate 'string outdir "cert.acl2")
                                          (list "; GENERATED -- do not edit."
                                                "(include-book \"portcullis\")")
                                          nil state))))))))))))))))

; --- Phase 2 -----------------------------------------------------------

(defun gen-phase2 (outdir state)
  (let* ((g (@ w1t-gen))
         (events (cadr (member :events g)))
         (builtins (cadr (member :builtins g)))
         (skipped (cadr (member :skipped g)))
         (stubs (cadr (member :stubs g)))
         (config (cadr (member :config g)))
         (header
          (append
           (list "; GENERATED by translate/il2acl2 from translate/il/wasm-1.0.il.sexp"
                 "; (SpecTec rev: see translate/il/SPECTEC_REV). Do not edit: fix the translator,"
                 "; translate/il2acl2-config.lsp, or translate/rt/ instead."
                 ";"
                 "; Contents, in IL order: a recognizer NAME-P for every syntax definition"
                 "; and a function $NAME for every SpecTec function definition."
                 "; Relations and grammars are not translated yet (plan T4-T7)."
                 ";"
                 "; Builtins and overrides (hand-written in translate/rt/builtins.lisp),"
                 "; as (name . arity):")
           (comment-lines ";   " (builtin-strings builtins))
           (list ";" "; Config overrides:")
           (comment-lines ";   " (config-strings config))
           (list ";" "; Stubs (an unsupported construct; body signals an error):")
           (comment-lines ";   " stubs)
           (list ";" "; Not translated yet:")
           (comment-lines ";   " (skipped-summary skipped))
           (list ""
                 "(in-package \"W1T\")"
                 ""
                 "(include-book \"../rt/builtins\")"
                 ""
                 "(set-verify-guards-eagerness 0)"
                 ""))))
    (let* ((forms (wrap-try-logic (convert-gsyms events)))
           (bad (foreign-symbols forms nil)))
      (if bad
          (mv (msg "Translator symbols leaked into generated code: ~x0" bad) state)
        (write-file (concatenate 'string outdir "wasm1.lisp") header forms state)))))
