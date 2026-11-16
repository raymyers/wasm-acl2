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
(include-book "specialize")
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
              (not (member-equal (symbol-package-name x) (list pkg "WRT" "ACL2" "KEYWORD" "COMMON-LISP"))))
         (if (member-eq x acc) acc (cons x acc)))
        ((consp x) (foreign-symbols (cdr x) pkg (foreign-symbols (car x) pkg acc)))
        (t acc)))

(defun event-first-name (ev)
  (cond ((and (consp ev) (eq (car ev) :%w1t-override)) (event-first-name (cdr ev))) ((and (consp ev) (eq (car ev) 'defun)) (cadr ev))
        ((and (consp ev) (eq (car ev) 'mutual-recursion)) (cadr (cadr ev)))
        (t nil)))

; each event: (%TRY-LOGIC ev) then (%TRY-GUARDS name); with PROGRAM (config
; :program, wasm3 M0) the event as it is, under the book's (program) default
(defun wrap-try-logic (evs pkg program)
  ;; PROGRAM: nil (the default attempts), t (config :program: the events as
  ;; they are) or a number of seconds (config :logic: timed attempts, wasm3 M9)
  (cond ((endp evs) nil)
        ((eq program t) evs)
        ;; config :memoize events go out as they are
        ((and (consp (car evs)) (eq (car (car evs)) (quote acl2::memoize)))
         (cons (car evs) (wrap-try-logic (cdr evs) pkg program)))
        ;; config :termination lemmas go out as they are
        ((and (consp (car evs)) (eq (car (car evs)) (quote acl2::defthm)))
         (cons (car evs) (wrap-try-logic (cdr evs) pkg program)))
        ((natp program)
         (list* (list (intern$ "%TRY-LOGIC-T" pkg) program (car evs))
                (list (intern$ "%TRY-GUARDS-T" pkg) program (event-first-name (car evs)))
                (wrap-try-logic (cdr evs) pkg program)))
        (t (list* (list (intern$ "%TRY-LOGIC" pkg) (car evs))
           (list (intern$ "%TRY-GUARDS" pkg) (event-first-name (car evs)))
           (wrap-try-logic (cdr evs) pkg program)))))

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

; Inverse pairs (wasm3 prep P3): from the IL's hint(inverse $g) on def f,
; then from :def overrides that declare :inverse (a hand-written partner),
; then from any :inverse config entries. ("f" . "g") in that order.
(defun hint-entry-inverses (id entries)
  (cond ((endp entries) nil)
        ((and (equal (sym-name (car (car entries))) "INVERSE")
              (< 1 (length (second (car entries))))
              (eql (char (second (car entries)) 0) #\$))
         (cons (cons id (subseq (second (car entries)) 1 (length (second (car entries)))))
               (hint-entry-inverses id (cdr entries))))
        (t (hint-entry-inverses id (cdr entries)))))

(defun hint-inverse-pairs (hints)
  (cond ((endp hints) nil)
        ((equal (sym-name (second (car hints))) "DEF")
         (append (hint-entry-inverses (third (car hints)) (cdddr (car hints)))
                 (hint-inverse-pairs (cdr hints))))
        (t (hint-inverse-pairs (cdr hints)))))

(defun override-inverse-pairs (config)
  ;; (:def "f" :inverse "g" ...) -> ("f" . "g")
  (cond ((endp config) nil)
        ((and (eq (car (car config)) :def) (stringp (cadr (member :inverse (car config)))))
         (cons (cons (second (car config)) (cadr (member :inverse (car config))))
               (override-inverse-pairs (cdr config))))
        (t (override-inverse-pairs (cdr config)))))

(defun all-inverse-pairs (hints config)
  (append (hint-inverse-pairs hints) (override-inverse-pairs config)
          (inverse-pairs (config-entries config :inverse))))

(defun decreasing-pairs (es)
  ;; (:decreasing :pairs (("Rel" . k) ...))
  (if (endp es) nil
    (append (cadr (member :pairs (car es))) (decreasing-pairs (cdr es)))))

(defun sized-pairs (es)
  ;; (:sized :pairs (("Bsection_" . "len") ...))
  (if (endp es) nil
    (append (cadr (member :pairs (car es))) (sized-pairs (cdr es)))))

(defun typ-defs (forms)
  ;; alist syntax id -> its TYP form (finite types for existential search, G5)
  (cond ((endp forms) nil)
        ((is (car forms) "REC") (append (typ-defs (cdr (car forms))) (typ-defs (cdr forms))))
        ((is (car forms) "TYP") (cons (cons (second (car forms)) (car forms)) (typ-defs (cdr forms))))
        (t (typ-defs (cdr forms)))))

(defun rel-defs (forms)
  ;; alist relation id -> its REL form (output variants on demand, wasm3 M5)
  (cond ((endp forms) nil)
        ((is (car forms) "REC") (append (rel-defs (cdr (car forms))) (rel-defs (cdr forms))))
        ((is (car forms) "REL") (cons (cons (second (car forms)) (car forms)) (rel-defs (cdr forms))))
        (t (rel-defs (cdr forms)))))

(defun opt-result-defs (forms)
  ;; ids of the defs whose result type is an option X? (partial defs, e.g. the
  ;; inverse $inv_isize: an inverse binding takes the element, wasm3 M4)
  (cond ((endp forms) nil)
        ((is (car forms) "REC") (append (opt-result-defs (cdr (car forms))) (opt-result-defs (cdr forms))))
        ((and (is (car forms) "DEF")
              (mv-let (ps more) (def-parts (car forms))
                (declare (ignore ps))
                (and (consp more) (is (car more) "ITER") (true-listp (car more))
                     (atom-is (third (car more)) "OPT"))))
         (cons (second (car forms)) (opt-result-defs (cdr forms))))
        (t (opt-result-defs (cdr forms)))))

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

; Config (:il-variant "f" :name "g" :drop-premises ("R" ...)): a copy of def
; f named g whose clauses lack the premises on the relations R (a rule
; premise, or an iteration of one). Placed right after f; f is unchanged.
; wasm3 M4: instantiate_unchecked, $instantiate without Module_ok (a stub
; until M7) and Externaddr_ok (which needs Module_ok's import types), the
; test-only path of decision D6.
(defun prem-on-p (x names)
  (and (consp x)
       (or (and (is x "RULE") (member-equal (second x) names))
           (and (is x "ITER") (consp (cdr x)) (prem-on-p (second x) names)))))

(defun drop-prems (items names)
  (cond ((atom items) items)
        ((prem-on-p (car items) names) (drop-prems (cdr items) names))
        (t (cons (car items) (drop-prems (cdr items) names)))))

(defun drop-prems-clauses (items names)
  (cond ((atom items) items)
        ((is (car items) "CLAUSE") (cons (drop-prems (car items) names) (drop-prems-clauses (cdr items) names)))
        (t (cons (car items) (drop-prems-clauses (cdr items) names)))))

(defun apply-variant (forms id name names)
  (cond ((endp forms) nil)
        ((and (is (car forms) "DEF") (equal (second (car forms)) id))
         (list* (car forms)
                (list* (car (car forms)) name (drop-prems-clauses (cddr (car forms)) names))
                (cdr forms)))
        (t (cons (car forms) (apply-variant (cdr forms) id name names)))))

(defun apply-variants (forms vs)
  (if (endp vs) forms
    (let ((v (car vs)))
      (apply-variants (apply-variant forms (second v) (cadr (member :name v)) (cadr (member :drop-premises v)))
                      (cdr vs)))))

(defun memo-rels (es)
  ;; (:memoize "label" :rels ("Rel" ...) ...)
  (if (endp es) nil (append (cadr (member :rels (car es))) (memo-rels (cdr es)))))

(defun given-entry-alist (es)
  ;; (:given-entry "Rel" :given ("v" ...) :defuns (...)) -> ("Rel" (v ...) . defuns)
  (if (endp es) nil
    (cons (cons (second (car es)) (cons (cadr (member :given (car es))) (cadr (member :defuns (car es)))))
          (given-entry-alist (cdr es)))))

(defun keep-variant-pairs (es)
  ;; (:keep-variant "Rel" :out i ...) -> (("Rel" . i) ...)
  (if (endp es) nil
    (cons (cons (second (car es)) (cadr (member :out (car es)))) (keep-variant-pairs (cdr es)))))

(defun memo-no-inline (es)
  ;; t if a :memoize entry says :recursive nil (memoize wraps the compiled
  ;; function instead of recompiling its body; the recursion of the
  ;; memoized R/%M goes through its entry R, so it is still memoized)
  (cond ((endp es) nil)
        ((and (member :recursive (car es)) (null (cadr (member :recursive (car es))))) t)
        (t (memo-no-inline (cdr es)))))

(defun size-rank-defs (es)
  ;; (:size-rank "label" :defs ("id" ...))
  (if (endp es) nil (append (cadr (member :defs (car es))) (size-rank-defs (cdr es)))))

(defun termination-alist (es)
  ;; (:termination "def" :measure m :lemmas (...)) -> ("def" :measure m :lemmas (...))
  (if (endp es) nil
    (cons (cons (second (car es)) (cddr (car es))) (termination-alist (cdr es)))))

(defun rel-override-alist (es)
  ;; (:rel-override "Rel" :defuns (...) ...) -> ("Rel" . defuns)
  (if (endp es) nil
    (cons (cons (second (car es)) (cadr (member :defuns (car es)))) (rel-override-alist (cdr es)))))

(defun override-mode-pairs (es)
  ;; (:rel-override "Rel" :mode m ...) -> (("Rel" . m) ...): the mode of an
  ;; overridden member of a rec group (wasm3 M6)
  (cond ((endp es) nil)
        ((member :mode (car es)) (cons (cons (second (car es)) (cadr (member :mode (car es)))) (override-mode-pairs (cdr es))))
        (t (override-mode-pairs (cdr es)))))

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

; --- Builtin classification (wasm3 prep P3, S7) --------------------------
;
; Every clause-less def is classified: :numeric (a hand-written function in
; rt/), :choice (a nondeterminism parameter, D4), :host (a host hook such as
; $hostcall) or :notation (only used in notation; ignored). Membership in a
; category comes from the config entry
;   (:builtins "categories" :choice (...) :host (...) :notation (...)
;              :numeric (...) :reason ...)
; and otherwise from hint(builtin), which means :numeric. A clause-less def
; in no category is a hard error.

(defun has-clause-p (xs) (and (consp xs) (or (is (car xs) "CLAUSE") (has-clause-p (cdr xs)))))

(defun clauseless-defs (forms)
  ;; ids of the clause-less defs, in IL order (REC groups opened)
  (cond ((endp forms) nil)
        ((is (car forms) "REC") (append (clauseless-defs (cdr (car forms))) (clauseless-defs (cdr forms))))
        ((and (is (car forms) "DEF") (not (has-clause-p (cddr (car forms)))))
         (cons (second (car forms)) (clauseless-defs (cdr forms))))
        (t (clauseless-defs (cdr forms)))))

(defun symbol-names-of (l)
  (if (endp l) nil (cons (sym-name (car l)) (symbol-names-of (cdr l)))))

(defun hint-builtin-ids (hints)
  (cond ((endp hints) nil)
        ((and (equal (sym-name (second (car hints))) "DEF")
              (member-equal "BUILTIN" (symbol-names-of (strip-cars (cdddr (car hints))))))
         (cons (third (car hints)) (hint-builtin-ids (cdr hints))))
        (t (hint-builtin-ids (cdr hints)))))

(defun builtin-category (id hinted bcfg)
  (cond ((member-equal id (cadr (member :choice bcfg))) :choice)
        ((member-equal id (cadr (member :host bcfg))) :host)
        ((member-equal id (cadr (member :notation bcfg))) :notation)
        ((member-equal id (cadr (member :numeric bcfg))) :numeric)
        ((member-equal id hinted) :numeric)
        (t nil)))

; ((id . category) ...) for every clause-less def, category nil if unknown
(defun classify-builtins-1 (ids hinted bcfg)
  (if (endp ids) nil
    (cons (cons (car ids) (builtin-category (car ids) hinted bcfg))
          (classify-builtins-1 (cdr ids) hinted bcfg))))

(defun classify-builtins (forms hints config)
  (classify-builtins-1 (clauseless-defs forms) (hint-builtin-ids hints)
                       (car (config-entries config :builtins))))

(defun ids-of-category (cls cat)
  (cond ((endp cls) nil)
        ((eq (cdr (car cls)) cat) (cons (car (car cls)) (ids-of-category (cdr cls) cat)))
        (t (ids-of-category (cdr cls) cat))))

; Names defined by rt/ (DEFUN / DEFMACRO anywhere in its top-level forms)
(defun defined-names (x acc)
  (cond ((atom x) acc)
        ((and (member-equal (sym-name (car x)) '("DEFUN" "DEFMACRO" "DEFUND" "DEFTHM" "DEFCONST")) (consp (cdr x))
              (sym-name (cadr x)))
         (cons (sym-name (cadr x)) acc))
        (t (defined-names (cdr x) (defined-names (car x) acc)))))

(defun rt-defined-names (files acc state)
  ;; (mv erp names state); a missing rt/ file is an error, not an empty list
  (if (endp files) (mv nil acc state)
    (mv-let (erp forms state) (read-il-file (car files) state)
      (if erp (mv (msg "Cannot read ~s0 (the builtin check needs rt/)" (car files)) nil state)
        (rt-defined-names (cdr files) (defined-names forms acc) state)))))

(defun missing-in-rt (ids rt-names tbl)
  ;; numeric builtins whose mangled name rt/ does not define
  (cond ((endp ids) nil)
        ((member-equal (cdr (assoc-equal (car ids) (cdr (assoc-eq :def tbl)))) rt-names)
         (missing-in-rt (cdr ids) rt-names tbl))
        (t (cons (car ids) (missing-in-rt (cdr ids) rt-names tbl)))))

(defun unclassified-builtins (cls)
  (cond ((endp cls) nil)
        ((null (cdr (car cls)))
         (cons (list :builtin (car (car cls))
                     "clause-less def without hint(builtin) and not in a :builtins category")
               (unclassified-builtins (cdr cls))))
        (t (unclassified-builtins (cdr cls)))))

(defconst *rt-files* '("rt/prelude.lisp" "rt/builtins.lisp"))

; A spec version may add builtins of its own in rt/builtins-<v>.lisp (wasm3 M1:
; rt/builtins-3.0.lisp, which includes rt/builtins). It is read for that
; version only, and its first generated part includes it, so the names of
; the other versions' packages and their generated code do not change.
; (mv files first-include state)
(defun rt-files-for (version state)
  (let ((f (concatenate 'string "rt/builtins-" version ".lisp")))
    (mv-let (channel state) (open-input-channel f :object state)
      (if (null channel) (mv *rt-files* "../../rt/builtins" state)
        (let ((state (close-input-channel channel state)))
          (mv (append *rt-files* (list f))
              (concatenate 'string "../../rt/builtins-" version) state))))))

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
                  ((not (let ((k (if (consp (cdr (car ps))) (cadr (car ps)) (cdr (car ps)))))
                          (and (natp k) (< k (rel-arity (car (car ps)) forms))
                               (or (atom (cdr (car ps))) (nat-listp (cddr (car ps)))))))
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

(defun declared-mode-pairs (es)
  ;; (:modes "label" :pairs (("Rel" . :check) ...) ...)
  (if (endp es) nil
    (append (cadr (member :pairs (car es))) (declared-mode-pairs (cdr es)))))

(defun check-mode-pairs (e ps tbl)
  (cond ((endp ps) nil)
        ((not (tbl-has :rel (car (car ps)) tbl))
         (cons (cfg-err e (concatenate 'string "relation " (car (car ps)) " not in the IL"))
               (check-mode-pairs e (cdr ps) tbl)))
        ((and (consp (cdr (car ps))) (eq (car (cdr (car ps))) :given)
              (string-listp (cdr (cdr (car ps)))))
         (check-mode-pairs e (cdr ps) tbl))
        ((not (member-eq (cdr (car ps)) '(:fun :fun2 :check :multi)))
         (cons (cfg-err e (concatenate 'string "mode of " (car (car ps)) " is not :fun, :fun2, :check or :multi"))
               (check-mode-pairs e (cdr ps) tbl)))
        (t (check-mode-pairs e (cdr ps) tbl))))

(defun config-entry-errors (e forms tbl overrides)
  (case (car e)
    (:def (check-names e :def (list (second e)) tbl "def"))
    (:rel-override (check-names e :rel (list (second e)) tbl "relation"))
    (:memoize (check-names e :rel (cadr (member :rels e)) tbl "relation"))
    (:witness (check-names e :rel (cadr (member :rels e)) tbl "relation"))
    (:fuel (check-names e :rel (cadr (member :rels e)) tbl "relation"))
    (:size-rank (check-names e :def (cadr (member :defs e)) tbl "def"))
    (:termination (append (check-names e :def (list (second e)) tbl "def")
                          (if (member :measure e) nil (list (cfg-err e ":measure missing")))))
    (:program (if (stringp (second e)) nil (list (cfg-err e "label missing"))))
    (:logic (if (natp (cadr (member :seconds e))) nil (list (cfg-err e ":seconds missing"))))
    (:split (if (member-equal (cons (second e) (third e)) (rule-pairs forms)) nil
              (list (cfg-err e (concatenate 'string "rule " (second e) "/" (third e) " not in the IL")))))
    (:inverse (check-inverse-pairs e (cadr (member :pairs e)) overrides tbl))
    (:decreasing (check-decreasing e (cadr (member :pairs e)) forms tbl))
    (:sized (check-sized e (cadr (member :pairs e)) forms tbl))
    (:modes (check-mode-pairs e (cadr (member :pairs e)) tbl))
    (:builtins (let ((ids (append (cadr (member :choice e)) (cadr (member :host e))
                                  (cadr (member :notation e)) (cadr (member :numeric e))))
                     (cl (clauseless-defs forms)))
                 (append (check-names e :def ids tbl "def")
                         (if (set-difference-equal (intersection-equal ids (strip-cars (cdr (assoc-eq :def tbl)))) cl)
                             (list (cfg-err e "a listed def has clauses (not a builtin)"))
                           nil))))
    (:given-entry (cond ((not (tbl-has :rel (second e) tbl)) (list (cfg-err e "relation not in the IL")))
                        ((not (and (consp (cadr (member :given e))) (string-listp (cadr (member :given e)))))
                         (list (cfg-err e ":given must name rule variables")))
                        (t nil)))
    (:keep-variant (cond ((not (tbl-has :rel (second e) tbl)) (list (cfg-err e "relation not in the IL")))
                         ((not (natp (cadr (member :out e)))) (list (cfg-err e ":out missing")))
                         (t nil)))
    (:il-variant (let ((x (il-form-named (second e) forms)))
                   (cond ((not (and x (is x "DEF"))) (list (cfg-err e (concatenate 'string "def " (second e) " not in the IL"))))
                         ((not (stringp (cadr (member :name e)))) (list (cfg-err e ":name missing")))
                         ((il-form-named (cadr (member :name e)) forms) (list (cfg-err e ":name is already defined")))
                         (t nil))))
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

; --- Parts: one generated book per source file (wasm3 prep P2, W7) --------
;
; decls (il/wasm-<v>.decls.lsp, from il2acl2/spec-decls.sh) maps each
; declaration (kind id file) to its .spectec file. A form's events go to the
; part of its file; parts are consecutive runs of IL order: a form whose file
; comes after that of a later form joins the earlier part (suffix-min), so each
; part only needs the parts before it.

(defun decl-kind (x)
  (cond ((is x "TYP") "syntax") ((is x "DEF") "def") ((is x "REL") "relation")
        ((is x "GRAM") "grammar") (t nil)))

(defun form-decl-key (x)
  (let ((y (if (is x "REC") (cadr x) x))) (cons (decl-kind y) (second y))))

(defun decl-file (key decls)
  (cond ((endp decls) nil)
        ((and (equal (first (car decls)) (car key)) (equal (second (car decls)) (cdr key)))
         (third (car decls)))
        (t (decl-file key (cdr decls)))))

(defun decl-files (decls acc)
  ;; distinct files in order of first appearance
  (cond ((endp decls) (reverse acc))
        ((member-equal (third (car decls)) acc) (decl-files (cdr decls) acc))
        (t (decl-files (cdr decls) (cons (third (car decls)) acc)))))

(defun index-of (x l n)
  (cond ((endp l) nil) ((equal x (car l)) n) (t (index-of x (cdr l) (1+ n)))))

(defun form-file-indices (xs decls files)
  ;; per form: index of its file in files, or nil when not in decls
  (if (endp xs) nil
    (let ((f (decl-file (form-decl-key (car xs)) decls)))
      (cons (and f (index-of f files 0)) (form-file-indices (cdr xs) decls files)))))

(defun suffix-min (is last)
  ;; label_k = min(index_k, label_{k+1}); unknown forms take the next label;
  ;; the result is non-decreasing, and equals the indices when they already are
  (if (endp is) nil
    (let* ((rest (suffix-min (cdr is) last))
           (next (if (consp rest) (car rest) last)))
      (cons (if (car is) (min (car is) next) next) rest))))

; (mv parts builtins skipped cx), parts = ((file . events) ...) in IL order;
; the events of all parts, appended, are exactly those of cforms.
(defun cforms-parts (xs labels files parts builtins skipped cx)
  (if (endp xs) (mv (reverse parts) builtins skipped cx)
    (mv-let (e b s cx) (cform (car xs) cx)
      (let* ((file (nth (car labels) files))
             (parts (cond ((and parts (equal (car (car parts)) file))
                           (cons (cons file (append (cdr (car parts)) e)) (cdr parts)))
                          (e (cons (cons file e) parts))
                          (t parts))))
        (cforms-parts (cdr xs) (cdr labels) files parts (append builtins b) (append skipped s) cx)))))

(defun part-book (file)
  ;; book name of a part: the file name with `.` replaced by `_`
  (coerce (substitute #\_ #\. (coerce file 'list)) 'string))

(defun part-events (parts)
  (if (endp parts) nil (append (cdr (car parts)) (part-events (cdr parts)))))

(defun part-names (parts)
  (if (endp parts) nil (cons (part-book (car (car parts))) (part-names (cdr parts)))))

; A target (wasm3 prep P2) names one spec version's inputs and outputs:
;   (:version "1.0" :pkg "W1T" :il "il/wasm-1.0.il.sexp"
;    :config "config/wasm-1.0.lsp" :outdir "gen/wasm-1.0/" :book "wasm1")
; Paths are relative to translate/; outdir is two levels below it.
(defun tgt (k target) (cadr (member k target)))

; Returns (mv erp state); stores the compiled results in state global
; IL2ACL2-GEN for phase 2.
(defun wrt-symbols (names)
  ;; the rt/ names as WRT symbols (those that are ACL2 symbols are already
  ;; imported through *acl2-exports* or deliberately left out)
  (cond ((endp names) nil)
        ((equal (symbol-package-name (intern$ (car names) "WRT")) "WRT")
         (cons (intern$ (car names) "WRT") (wrt-symbols (cdr names))))
        (t (wrt-symbols (cdr names)))))

(defun gen-phase1-1 (target decls rt-names state)
  (let ((il-file (tgt :il target)) (config-file (tgt :config target))
        (outdir (tgt :outdir target)) (pkg (tgt :pkg target)))
  (mv-let (erp summary state) (il-check il-file state)
    (declare (ignore summary))
    (if erp (mv erp state)
      (mv-let (erp forms hints state) (read-il il-file state)
        (declare (ignore erp))
        (mv-let (erp cfg state) (read-il-file config-file state)
          (if erp (mv erp state)
           (let ((cerrs (append (config-errors (car cfg) forms (mangle-table forms))
                                (unclassified-builtins (classify-builtins forms hints (car cfg))))))
            (if cerrs
                (mv (msg "Config entries that do not match the IL, or unclassified builtins (~s0):~|~x1" config-file cerrs) state)
            (let* ((config (car cfg))
                   (forms (apply-variants (apply-patches forms (config-entries config :il-patch))
                                         (config-entries config :il-variant)))
                   (spec (mv-list 3 (specialize-fn-args forms)))
                   (forms (first spec))
                   (cx (list (cons :tbl (mangle-table forms))
                             (cons :overrides (config-overrides config))
                             (cons :split-rules (split-rules (config-entries config :split)))
                             (cons :inverses (all-inverse-pairs hints config))
                             (cons :sized (sized-pairs (config-entries config :sized)))
                             (cons :decreasing (decreasing-pairs (config-entries config :decreasing)))
                             (cons :rel-overrides (rel-override-alist (config-entries config :rel-override)))
                             (cons :memo (memo-rels (config-entries config :memoize)))
                             (cons :memo-no-inline (memo-no-inline (config-entries config :memoize)))
                             (cons :declared-modes (append (declared-mode-pairs (config-entries config :modes))
                                                          (override-mode-pairs (config-entries config :rel-override))))
                             (cons :witness-ok (memo-rels (config-entries config :witness)))
                             (cons :fuel-rels (memo-rels (config-entries config :fuel)))
                             (cons :size-rank-defs (size-rank-defs (config-entries config :size-rank)))
                             (cons :terminations (termination-alist (config-entries config :termination)))
                             (cons :rt-names rt-names)
                             (cons :keep-variants (keep-variant-pairs (config-entries config :keep-variant)))
                             (cons :given-entries (given-entry-alist (config-entries config :given-entry)))
                             (cons :typ-defs (typ-defs forms))
                             (cons :rel-defs (rel-defs forms))
                             (cons :gram-defs (gram-defs forms))
                             (cons :opt-defs (opt-result-defs forms)))))
              (mv-let (parts builtins skipped cx)
                (let ((files (or (decl-files decls nil) (list "all"))))
                  (cforms-parts forms (suffix-min (form-file-indices forms decls files) (1- (len files)))
                                files nil nil nil cx))
                (let* ((events (part-events parts))
                       (names (prog2$ (cw "~%il2acl2: ~x0 events, ~x1 builtins/overrides, ~x2 forms not translated, stubs: ~x3~%unsupported constructs (~x4):~%~x5~%"
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
                                                  :incomplete (final-incomplete (reverse (cx-get :incomplete cx)) nil cx)
                                                  :enum-variants (enum-names (cx-get :all-variants cx) cx)
                                                  :enum-dropped (remove-duplicates-equal (cx-get :all-dropped cx))
                                                  :kept-variants (cx-get :kept-names cx)
                                                  :kept-dropped (remove-duplicates-equal (cx-get :kept-dropped cx))
                                                  :partial (cx-get :partial cx)
                                                  :errs (reverse (cx-get :errs cx))
                                                  :config config
                                                  :target target
                                                  :parts parts
                                                  :specialized (second spec)
                                                  :ho-dropped (third spec)
                                                  :builtin-classes (classify-builtins forms hints config)
                                                  :rt-missing (missing-in-rt (ids-of-category (classify-builtins forms hints config) :numeric)
                                                                             rt-names (cx-get :tbl cx)))
                                            state)))
                  (mv-let (erp state)
                    (write-file
                     (concatenate 'string outdir "package.lsp")
                     (list "; GENERATED by translate/il2acl2 -- do not edit."
                           (concatenate 'string "; " pkg ": the package of the generated WASM "
                                        (tgt :version target) " semantics. It imports")
                           "; *acl2-exports* minus every export whose name the generated code"
                           "; defines or binds, plus the names rt/ defines (package WRT)."
                           "(in-package \"ACL2\")")
                     (list (list 'defpkg pkg
                                 (list 'append
                                 (list 'set-difference-eq '*acl2-exports*
                                       (list 'quote (acl2::merge-sort-symbol< clash)))
                                 (list 'quote (acl2::merge-sort-symbol< (remove-duplicates-eq (wrt-symbols rt-names)))))))
                     state)
                    (if erp (mv erp state)
                      (mv-let (erp state)
                        (write-file (concatenate 'string outdir "portcullis.acl2")
                                    (list "; GENERATED -- do not edit." "(ld \"../../package.lsp\") ; IL2ACL2 and WRT" "(ld \"package.lsp\")")
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

(defun certify-mode (config)
  ;; t for config :program, the seconds of config :logic, else nil
  (cond ((config-entries config :program) t)
        ((config-entries config :logic) (nfix (cadr (member :seconds (car (config-entries config :logic))))))
        (t nil)))

(defun write-parts (parts prev target program state)
  ;; each part: (in-package), include the previous part (the runtime for the
  ;; first), the defaults that are local to a book, then its events
  (if (endp parts) (mv nil state)
    (let* ((pkg (tgt :pkg target))
           (book (part-book (car (car parts))))
           (forms (wrap-try-logic (convert-gsyms (cdr (car parts)) pkg) pkg program)))
      (mv-let (erp state)
        (write-file (concatenate 'string (tgt :outdir target) book ".lisp")
                    (list (concatenate 'string "; GENERATED by translate/il2acl2 from translate/" (tgt :il target)
                                       ": the forms of " (car (car parts)) ".spectec.")
                          (concatenate 'string "; Do not edit. The header of " (tgt :book target)
                                       ".lisp lists builtins, overrides, stubs and dropped rules.")
                          ""
                          (concatenate 'string "(in-package \"" pkg "\")")
                          ""
                          (concatenate 'string "(include-book \"" prev "\")")
                          ""
                          (if (eq program t) "(program) ; config :program" "(set-verify-guards-eagerness 0)")
                          "(set-bogus-mutual-recursion-ok t) ; stubbed members of a rec group"
                          "")
                    forms state)
        (if erp (mv erp state)
          (write-parts (cdr parts) book target program state))))))

; --- Phase 2 -----------------------------------------------------------

; Runs with the target's package current (symbols print unqualified).
(defun gen-phase2 (state)
  (let* ((g (@ il2acl2-gen))
         (events (cadr (member :events g)))
         (builtins (cadr (member :builtins g)))
         (skipped (cadr (member :skipped g)))
         (stubs (cadr (member :stubs g)))
         (incomplete (cadr (member :incomplete g)))
         (enum-variants (cadr (member :enum-variants g)))
         (enum-dropped (cadr (member :enum-dropped g)))
         (kept-variants (cadr (member :kept-variants g)))
         (kept-dropped (cadr (member :kept-dropped g)))
         (partial (cadr (member :partial g)))
         (config (cadr (member :config g)))
         (target (cadr (member :target g)))
         (parts (cadr (member :parts g)))
         (classes (cadr (member :builtin-classes g)))
         (rt-missing (cadr (member :rt-missing g)))
         (specialized (cadr (member :specialized g)))
         (ho-dropped (cadr (member :ho-dropped g)))
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
           (if ho-dropped
               (append (list ";" "; Defs with function parameters, replaced by specializations (G1):")
                       (comment-lines ";   " (list (join-words ho-dropped)))
                       (list (concatenate 'string "; Specializations (" (nat-str (len specialized)) "):"))
                       (comment-lines ";   " (list (join-words specialized))))
             nil)
           (if (or (ids-of-category classes :choice) (ids-of-category classes :host)
                   (ids-of-category classes :notation))
               (append (list ";" "; Builtins that are not numeric functions (config :builtins):")
                       (comment-lines ";   choice (nondeterminism parameter): "
                                      (list (join-words (ids-of-category classes :choice))))
                       (comment-lines ";   host hook: " (list (join-words (ids-of-category classes :host))))
                       (comment-lines ";   notation (unused): "
                                      (list (join-words (ids-of-category classes :notation)))))
             nil)
           (if rt-missing
               (append (list ";" "; Numeric builtins with no definition in rt/ yet (emitted as stubs until added):")
                       (comment-lines ";   " (list (join-words rt-missing))))
             nil)
           (list ";" "; Config overrides:")
           (comment-lines ";   " (config-strings config))
           (list ";" "; Stubs (an unsupported construct; body signals an error):")
           (comment-lines ";   " stubs)
           (if partial
               (append (list ";" "; Rules not translated (each relation is emitted without them; sound"
                             "; but incomplete), as relation translated/total: dropped rules:")
                       (comment-lines ";   " (partial-strings partial)))
             nil)
           (if kept-variants
               (append (list ";" "; Kept output variants (config :keep-variant, wasm3 M6), for hand-written"
                             "; code; they leave out the rules whose output is not computable:")
                       (comment-lines ";   " (list (join-words kept-variants)))
                       (list "; Rules left out of them:")
                       (comment-lines ";   " (list (join-words kept-dropped))))
             nil)
           (if enum-variants
               (append (list ";" "; Enumeration variants (wasm3 M5): R/ENUM<i> returns every output i that a"
                             "; rule of R gives for the inputs; a premise of the same rec group that"
                             "; needs that output searches the list (Heaptype_sub/trans: heaptype'):")
                       (comment-lines ";   " (list (join-words enum-variants)))
                       (list "; Rules not in an enumeration variant (their output is not computable from"
                             "; the inputs, or they would enumerate the relation on the same inputs):")
                       (comment-lines ";   " (list (join-words enum-dropped))))
             nil)
           (list ";" "; Rules dropped from the R/SPLIT variants of multi-mode relations (their"
                 "; output is not computable from the inputs; the R check variants keep them):")
           (comment-lines ";   " incomplete)
           (list ";" "; Not translated yet:")
           (comment-lines ";   " (skipped-summary skipped))
           (list ";" "; Parts (one book per source file, in IL order; each includes the one before):")
           (comment-lines ";   " (part-names parts))
           (list ""
                 (concatenate 'string "(in-package \"" pkg "\")")
                 ""
                 (concatenate 'string "(include-book \"" (car (last (part-names parts))) "\")")
                 ""))))
    (let* ((bad (foreign-symbols (convert-gsyms events pkg) pkg nil)))
      (if bad
          (mv (msg "Translator symbols leaked into generated code: ~x0" bad) state)
        (mv-let (rt-files rt-book state) (rt-files-for (tgt :version target) state)
         (declare (ignore rt-files))
        (mv-let (erp state) (write-parts parts rt-book target (certify-mode config) state)
          (if erp (mv erp state)
            (write-file (concatenate 'string (tgt :outdir target) (tgt :book target) ".lisp")
                        header nil state))))))))

(defun gen-phase1 (target state)
  ;; the declarations map is optional: without it everything is one part
  (mv-let (erp decls state)
    (if (tgt :decls target) (read-il-file (tgt :decls target) state) (mv nil nil state))
    (if erp (mv erp state)
      (mv-let (rt-files rt-book state) (rt-files-for (tgt :version target) state)
       (declare (ignore rt-book))
      (mv-let (erp rt-names state) (rt-defined-names rt-files nil state)
       (if erp (mv erp state)
        (gen-phase1-1 target (car decls) rt-names state)))))))
