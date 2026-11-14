; Emitter: compile the whole IL and write translate/gen/ (plan §1, §3).
;
; Two phases, because the W1T package's imports depend on the generated
; names (every ACL2 export whose name we define or bind is left out):
;   phase 1 (package IL2ACL2): compile, write <outdir>/package.lsp + portcullis
;   -- the run script then ld's <outdir>/package.lsp --
;   phase 2 (current package: the target's, e.g. W1T): print <outdir>/<book>.lisp
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

; Config override code (:%w1t-override . forms) is written with translator-package
; symbols; they become W1T symbols here. Elsewhere such symbols are an error.
(defun override-syms (x pkg)
  (cond ((and (symbolp x) x (equal (symbol-package-name x) "IL2ACL2")) (intern$ (symbol-name x) pkg))
        ((consp x) (cons (override-syms (car x) pkg) (override-syms (cdr x) pkg)))
        (t x)))

(defun convert-gsyms (x pkg)
  (cond ((gsym-p x) (intern$ (cdr x) pkg))
        ((and (consp x) (eq (car x) :%w1t-override)) (override-syms (cdr x) pkg))
        ((consp x) (cons (convert-gsyms (car x) pkg) (convert-gsyms (cdr x) pkg)))
        (t x)))

; Every symbol in generated code must be a W1T, ACL2, or keyword symbol.
(defun foreign-symbols (x pkg acc)
  (cond ((and (symbolp x) x (not (eq x t))
              (not (member-equal (symbol-package-name x) (list pkg "ACL2" "KEYWORD" "COMMON-LISP"))))
         (if (member-eq x acc) acc (cons x acc)))
        ((consp x) (foreign-symbols (cdr x) pkg (foreign-symbols (car x) pkg acc)))
        (t acc)))

(defun event-first-name (ev)
  (cond ((and (consp ev) (eq (car ev) :%w1t-override)) (event-first-name (cdr ev))) ((and (consp ev) (eq (car ev) 'defun)) (cadr ev))
        ((and (consp ev) (eq (car ev) 'mutual-recursion)) (cadr (cadr ev)))
        (t nil)))

; each event: (%TRY-LOGIC ev) then (%TRY-GUARDS name)
(defun wrap-try-logic (evs pkg)
  (cond ((endp evs) nil)
        ;; config :memoize events go out as they are
        ((and (consp (car evs)) (eq (car (car evs)) (quote acl2::memoize)))
         (cons (car evs) (wrap-try-logic (cdr evs) pkg)))
        (t (list* (list (intern$ "%TRY-LOGIC" pkg) (car evs))
           (list (intern$ "%TRY-GUARDS" pkg) (event-first-name (car evs)))
           (wrap-try-logic (cdr evs) pkg)))))

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

(defun partial-strings (ps)
  ;; ("Rel" total (dropped ...) mode) -> "Rel (mode) k/total: dropped ..."
  (if (endp ps) nil
    (let ((p (car ps)))
      (cons (concatenate (quote string) (first p) " (" (string-downcase (symbol-name (fourth p))) ") "
                         (nat-str (- (second p) (len (third p))))
                         "/" (nat-str (second p)) ": " (join-words (third p)))
            (partial-strings (cdr ps))))))

; --- Phase 1 -----------------------------------------------------------

(defun config-entries (config kind)
  (cond ((endp config) nil)
        ((eq (car (car config)) kind) (cons (car config) (config-entries (cdr config) kind)))
        (t (config-entries (cdr config) kind))))

(defun split-rules (es)
  ;; (:split "Rel" "rule" ...) -> ("Rel" . "rule")
  (if (endp es) nil
    (cons (cons (second (car es)) (third (car es))) (split-rules (cdr es)))))

(defun inverse-pairs (es)
  ;; (:inverse :pairs (("f" . "inv_f") ...) ...)
  (if (endp es) nil
    (append (cadr (member :pairs (car es))) (inverse-pairs (cdr es)))))

(defun decreasing-pairs (es)
  ;; (:decreasing :pairs (("Rel" . k) ...))
  (if (endp es) nil
    (append (cadr (member :pairs (car es))) (decreasing-pairs (cdr es)))))

(defun sized-pairs (es)
  ;; (:sized :pairs (("Bsection_" . "len") ...))
  (if (endp es) nil
    (append (cadr (member :pairs (car es))) (sized-pairs (cdr es)))))

(defun gram-defs (forms)
  ;; alist grammar id -> its GRAM form (for inlining parametric grammars)
  (cond ((endp forms) nil)
        ((is (car forms) "REC") (append (gram-defs (cdr (car forms))) (gram-defs (cdr forms))))
        ((is (car forms) "GRAM") (cons (cons (second (car forms)) (car forms)) (gram-defs (cdr forms))))
        (t (gram-defs (cdr forms)))))

; Config (:il-patch "Def" :old X :new Y ...): replace every subtree equal to
; X by Y inside the top-level definition named "Def". For bugs in the
; SpecTec source that a faithful translation would reproduce.
(defun subst-tree (new old x)
  (cond ((equal x old) new)
        ((atom x) x)
        (t (cons (subst-tree new old (car x)) (subst-tree new old (cdr x))))))

(defun apply-patch (forms id old new)
  (cond ((endp forms) nil)
        ((and (consp (car forms)) (equal (second (car forms)) id))
         (cons (subst-tree new old (car forms)) (apply-patch (cdr forms) id old new)))
        ((is (car forms) "REC")
         (cons (cons (car (car forms)) (apply-patch (cdr (car forms)) id old new))
               (apply-patch (cdr forms) id old new)))
        (t (cons (car forms) (apply-patch (cdr forms) id old new)))))

(defun apply-patches (forms ps)
  (if (endp ps) forms
    (let ((p (car ps)))
      (apply-patches (apply-patch forms (second p) (cadr (member :old p)) (cadr (member :new p)))
                     (cdr ps)))))

(defun memo-rels (es)
  ;; (:memoize "label" :rels ("Rel" ...) ...)
  (if (endp es) nil (append (cadr (member :rels (car es))) (memo-rels (cdr es)))))

(defun rel-override-alist (es)
  ;; (:rel-override "Rel" :defuns (...) ...) -> ("Rel" . defuns)
  (if (endp es) nil
    (cons (cons (second (car es)) (cadr (member :defuns (car es)))) (rel-override-alist (cdr es)))))

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

; --- Config validation (wasm3 prep P2, W5) -----------------------------
;
; Every config entry must name something that exists in the IL, so a stale
; or misspelled entry is a hard error instead of silently doing nothing.
; An :inverse partner may be absent from the IL only when the function
; itself is a :def override (the hand-written override supplies both).

(defun occurs-in (x tree)
  (or (equal x tree)
      (and (consp tree) (or (occurs-in x (car tree)) (occurs-in x (cdr tree))))))

(defun il-form-named (id forms)
  (cond ((endp forms) nil)
        ((is (car forms) "REC")
         (or (il-form-named id (cdr (car forms))) (il-form-named id (cdr forms))))
        ((and (consp (car forms)) (equal (second (car forms)) id)) (car forms))
        (t (il-form-named id (cdr forms)))))

(defun tbl-has (ns id tbl) (and (stringp id) (assoc-equal id (cdr (assoc-eq ns tbl))) t))

(defun rel-arity (id forms)
  (let ((x (il-form-named id forms)))
    (if (is x "REL") (mv-let (n rules) (rel-parts x) (declare (ignore rules)) n) 0)))

(defun cfg-err (e what) (list (car e) (second e) what))

(defun check-names (e ns ids tbl what)
  (cond ((endp ids) nil)
        ((tbl-has ns (car ids) tbl) (check-names e ns (cdr ids) tbl what))
        (t (cons (cfg-err e (concatenate 'string what " " (if (stringp (car ids)) (car ids) "?")
                                         " not in the IL"))
                 (check-names e ns (cdr ids) tbl what)))))

(defun check-inverse-pairs (e ps overrides tbl)
  (if (endp ps) nil
    (let ((f (car (car ps))) (g (cdr (car ps))))
      (append (if (tbl-has :def f tbl) nil
                (list (cfg-err e (concatenate 'string "def " f " not in the IL"))))
              (if (or (tbl-has :def g tbl) (member-equal f overrides)) nil
                (list (cfg-err e (concatenate 'string "inverse " g " not in the IL and " f
                                              " is not a :def override"))))
              (check-inverse-pairs e (cdr ps) overrides tbl)))))

(defun check-decreasing (e ps forms tbl)
  (if (endp ps) nil
    (append (cond ((not (tbl-has :rel (car (car ps)) tbl))
                   (list (cfg-err e (concatenate 'string "relation " (car (car ps)) " not in the IL"))))
                  ((not (and (natp (cdr (car ps))) (< (cdr (car ps)) (rel-arity (car (car ps)) forms))))
                   (list (cfg-err e (concatenate 'string "component index out of range for " (car (car ps))))))
                  (t nil))
            (check-decreasing e (cdr ps) forms tbl))))

(defun check-sized (e ps forms tbl)
  (if (endp ps) nil
    (append (cond ((not (tbl-has :gram (car (car ps)) tbl))
                   (list (cfg-err e (concatenate 'string "grammar " (car (car ps)) " not in the IL"))))
                  ((not (occurs-in (cdr (car ps)) (il-form-named (car (car ps)) forms)))
                   (list (cfg-err e (concatenate 'string "variable " (cdr (car ps)) " not in grammar "
                                                 (car (car ps))))))
                  (t nil))
            (check-sized e (cdr ps) forms tbl))))

(defun config-entry-errors (e forms tbl overrides)
  (case (car e)
    (:def (check-names e :def (list (second e)) tbl "def"))
    (:rel-override (check-names e :rel (list (second e)) tbl "relation"))
    (:memoize (check-names e :rel (cadr (member :rels e)) tbl "relation"))
    (:split (if (member-equal (cons (second e) (third e)) (rule-pairs forms)) nil
              (list (cfg-err e (concatenate 'string "rule " (second e) "/" (third e) " not in the IL")))))
    (:inverse (check-inverse-pairs e (cadr (member :pairs e)) overrides tbl))
    (:decreasing (check-decreasing e (cadr (member :pairs e)) forms tbl))
    (:sized (check-sized e (cadr (member :pairs e)) forms tbl))
    (:il-patch (let ((x (il-form-named (second e) forms)))
                 (cond ((null x) (list (cfg-err e (concatenate 'string (second e) " not in the IL"))))
                       ((not (occurs-in (cadr (member :old e)) x))
                        (list (cfg-err e ":old does not occur in the form (fixed upstream?)")))
                       (t nil))))
    (otherwise (list (cfg-err e "unknown config entry kind")))))

(defun config-errors-1 (config forms tbl overrides)
  (if (endp config) nil
    (append (config-entry-errors (car config) forms tbl overrides)
            (config-errors-1 (cdr config) forms tbl overrides))))

; list of (kind label message); nil when every entry matches the IL
(defun config-errors (config forms tbl)
  (config-errors-1 config forms tbl (config-overrides config)))

; A target (wasm3 prep P2) names one spec version's inputs and outputs:
;   (:version "1.0" :pkg "W1T" :il "il/wasm-1.0.il.sexp"
;    :config "config/wasm-1.0.lsp" :outdir "gen/wasm-1.0/" :book "wasm1")
; Paths are relative to translate/; outdir is two levels below it.
(defun tgt (k target) (cadr (member k target)))

; Returns (mv erp state); stores the compiled results in state global
; IL2ACL2-GEN for phase 2.
(defun gen-phase1 (target state)
  (let ((il-file (tgt :il target)) (config-file (tgt :config target))
        (outdir (tgt :outdir target)) (pkg (tgt :pkg target)))
  (mv-let (erp summary state) (il-check il-file state)
    (declare (ignore summary))
    (if erp (mv erp state)
      (mv-let (erp forms state) (read-il-file il-file state)
        (declare (ignore erp))
        (mv-let (erp cfg state) (read-il-file config-file state)
          (if erp (mv erp state)
           (let ((cerrs (config-errors (car cfg) forms (mangle-table forms))))
            (if cerrs
                (mv (msg "Config entries that do not match the IL (~s0):~|~x1" config-file cerrs) state)
            (let* ((config (car cfg))
                   (forms (apply-patches forms (config-entries config :il-patch)))
                   (cx (list (cons :tbl (mangle-table forms))
                             (cons :overrides (config-overrides config))
                             (cons :split-rules (split-rules (config-entries config :split)))
                             (cons :inverses (inverse-pairs (config-entries config :inverse)))
                             (cons :sized (sized-pairs (config-entries config :sized)))
                             (cons :decreasing (decreasing-pairs (config-entries config :decreasing)))
                             (cons :rel-overrides (rel-override-alist (config-entries config :rel-override)))
                             (cons :memo (memo-rels (config-entries config :memoize)))
                             (cons :gram-defs (gram-defs forms)))))
              (mv-let (events builtins skipped cx) (cforms forms cx)
                (let* ((names (prog2$ (cw "~%il2acl2: ~x0 events, ~x1 builtins/overrides, ~x2 forms not translated, stubs: ~x3~%unsupported constructs (~x4):~%~x5~%"
                               (len events) (len builtins) (len skipped)
                               (reverse (cx-get :stubs cx)) (len (cx-get :errs cx))
                               (reverse (cx-get :errs cx)))
                                     (collect-gsyms events
                                             (strip-cars builtins))))
                       (clash (clashing-exports *acl2-exports* names))
                       (state (f-put-global 'il2acl2-gen
                                            (list :events events :builtins builtins
                                                  :skipped skipped
                                                  :stubs (reverse (cx-get :stubs cx))
                                                  :incomplete (reverse (cx-get :incomplete cx))
                                                  :partial (cx-get :partial cx)
                                                  :errs (reverse (cx-get :errs cx))
                                                  :config config
                                                  :target target)
                                            state)))
                  (mv-let (erp state)
                    (write-file
                     (concatenate 'string outdir "package.lsp")
                     (list "; GENERATED by translate/il2acl2 -- do not edit."
                           (concatenate 'string "; " pkg ": the package of the generated WASM "
                                        (tgt :version target) " semantics. It imports")
                           "; *acl2-exports* minus every export whose name the generated code"
                           "; defines or binds."
                           "(in-package \"ACL2\")")
                     (list (list 'defpkg pkg
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
                                              (concatenate 'string "; Empty book whose portcullis defines the "
                                                           pkg " package.")
                                              "(in-package \"ACL2\")")
                                        nil state)
                            (if erp (mv erp state)
                              (write-file (concatenate 'string outdir "cert.acl2")
                                          (list "; GENERATED -- do not edit."
                                                "(include-book \"portcullis\")")
                                          nil state)))))))))))))))))))

; --- Phase 2 -----------------------------------------------------------

; Runs with the target's package current (symbols print unqualified).
(defun gen-phase2 (state)
  (let* ((g (@ il2acl2-gen))
         (events (cadr (member :events g)))
         (builtins (cadr (member :builtins g)))
         (skipped (cadr (member :skipped g)))
         (stubs (cadr (member :stubs g)))
         (incomplete (cadr (member :incomplete g)))
         (partial (cadr (member :partial g)))
         (config (cadr (member :config g)))
         (target (cadr (member :target g)))
         (pkg (tgt :pkg target))
         (header
          (append
           (list (concatenate 'string "; GENERATED by translate/il2acl2 from translate/" (tgt :il target))
                 "; (SpecTec rev: see translate/il/SPECTEC_REV). Do not edit: fix the translator,"
                 (concatenate 'string "; translate/" (tgt :config target) ", or translate/rt/ instead.")
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
           (if partial
               (append (list ";" "; Rules not translated (each relation is emitted without them; sound"
                             "; but incomplete), as relation translated/total: dropped rules:")
                       (comment-lines ";   " (partial-strings partial)))
             nil)
           (list ";" "; Rules dropped from the R/SPLIT variants of multi-mode relations (their"
                 "; output is not computable from the inputs; the R check variants keep them):")
           (comment-lines ";   " incomplete)
           (list ";" "; Not translated yet:")
           (comment-lines ";   " (skipped-summary skipped))
           (list ""
                 (concatenate 'string "(in-package \"" pkg "\")")
                 ""
                 "(include-book \"../../rt/builtins\")"
                 ""
                 "(set-verify-guards-eagerness 0)"
                 "(set-bogus-mutual-recursion-ok t) ; stubbed members of a rec group"
                 ""))))
    (let* ((forms (wrap-try-logic (convert-gsyms events pkg) pkg))
           (bad (foreign-symbols forms pkg nil)))
      (if bad
          (mv (msg "Translator symbols leaked into generated code: ~x0" bad) state)
        (write-file (concatenate 'string (tgt :outdir target) (tgt :book target) ".lisp")
                    header forms state)))))
