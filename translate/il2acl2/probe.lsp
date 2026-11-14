; il2acl2 probe (plan/wasm3-translation-prep P0): run the schema check, the
; mangler and translator phase 1 on any IL, and print the probe table.
; Nothing under gen/ is written. Driven by `make probe SPEC=<v>`, which
; prepends a file that assigns these state globals:
;   probe-il      IL file           probe-config  config file
;   probe-names   (kind id file) list from probe-names.sh
;   probe-drop    config entry kinds to ignore, e.g. (:rel-override :il-patch)
;   probe-errors  where to write every logged translator error
; The report goes to standard output between PROBE-REPORT-BEGIN/END. It has
; no timings, so it is a deterministic function of the IL and the config.
(set-ld-error-action (quote (:exit 1)) state)
(ld "package.lsp")
(include-book "il2acl2/emit")
(in-package "IL2ACL2")
(set-state-ok t)
(program)
(set-fmt-soft-right-margin 100000 state)
(set-fmt-hard-right-margin 100000 state)

(defun probe-drop-kinds (config kinds)
  (cond ((endp config) nil)
        ((member-eq (car (car config)) kinds) (probe-drop-kinds (cdr config) kinds))
        (t (cons (car config) (probe-drop-kinds (cdr config) kinds)))))

(defun probe-count-defuns (evs n)
  (cond ((endp evs) n)
        ((and (consp (car evs)) (eq (car (car evs)) 'mutual-recursion))
         (probe-count-defuns (cdr evs) (+ n (len (cdr (car evs))))))
        (t (probe-count-defuns (cdr evs) (1+ n)))))

; alist key -> count, keys in order of first appearance
(defun probe-tally (keys acc)
  (if (endp keys) acc
    (probe-tally (cdr keys)
                 (put-assoc-equal (car keys) (1+ (or (cdr (assoc-equal (car keys) acc)) 0)) acc))))

; alist key -> values, keys in order of first appearance, values in order
(defun probe-group (pairs acc)
  (if (endp pairs) acc
    (let* ((k (car (car pairs))) (old (cdr (assoc-equal k acc))))
      (probe-group (cdr pairs) (put-assoc-equal k (append old (list (cdr (car pairs)))) acc)))))

(defun probe-schema-keys (errs)
  ;; schema errors (:err ctx what x) -> (what . head-of-x)
  (if (endp errs) nil
    (let ((e (car errs)))
      (cons (cons (third e) (if (and (consp (fourth e)) (symbolp (car (fourth e))))
                                (symbol-name (car (fourth e)))
                              :other))
            (probe-schema-keys (cdr errs))))))

(defun probe-schema-ctx (errs)
  (if (endp errs) nil
    (cons (cons (third (car errs)) (second (car errs))) (probe-schema-ctx (cdr errs)))))

; mangled name -> (kind . IL id), for the function namespaces that stub
(defun probe-rassoc (v alist)
  (cond ((endp alist) nil)
        ((equal (cdr (car alist)) v) (car (car alist)))
        (t (probe-rassoc v (cdr alist)))))

(defun probe-origin (name tbl kinds)
  (if (endp kinds) (cons "?" name)
    (let ((id (probe-rassoc name (cdr (assoc (car (car kinds)) tbl)))))
      (if id (cons (cdr (car kinds)) id)
        (probe-origin name tbl (cdr kinds))))))

(defun probe-file-of (origin names)
  ;; names: list of (kind id file)
  (cond ((endp names) "?")
        ((and (equal (first (car names)) (car origin))
              (equal (second (car names)) (cdr origin)))
         (third (car names)))
        (t (probe-file-of origin (cdr names)))))

(defun probe-stub-files (stubs tbl names)
  ;; ((file . stub) ...)
  (if (endp stubs) nil
    (cons (cons (probe-file-of (probe-origin (car stubs) tbl
                                             '((:rel . "relation") (:def . "def")
                                               (:gram . "grammar") (:typ . "syntax")))
                               names)
                (car stubs))
          (probe-stub-files (cdr stubs) tbl names))))

(defun probe-pick (keys groups)
  (if (endp keys) nil
    (cons (assoc-equal (car keys) groups) (probe-pick (cdr keys) groups))))

(defun probe-sort-groups (groups)
  ;; by file name (the spec files have numeric prefixes)
  (if (endp groups) nil
    (let ((sorted (acl2::merge-sort-lexorder (strip-cars groups))))
      (probe-pick sorted groups))))

(defun probe-print-groups (groups)
  (if (endp groups) nil
    (prog2$ (cw "  ~s0: ~x1: ~s2~%" (car (car groups)) (len (cdr (car groups))) (join-words (cdr (car groups))))
            (probe-print-groups (cdr groups)))))

; most frequent first; ties keep their order of first appearance
(defun probe-insert (x l)
  (cond ((endp l) (list x))
        ((> (cdr x) (cdr (car l))) (cons x l))
        (t (cons (car l) (probe-insert x (cdr l))))))

(defun probe-by-count (tally acc)
  (if (endp tally) acc
    (probe-by-count (cdr tally) (probe-insert (car tally) acc))))

(defun probe-print-tally (tally)
  (if (endp tally) nil
    (prog2$ (cw "  ~x0: ~x1~%" (cdr (car tally)) (car (car tally)))
            (probe-print-tally (cdr tally)))))

(defun probe-print-tally-sorted (tally)
  (probe-print-tally (probe-by-count tally nil)))

; "Rel/rule" -> ("Rel" . "rule")
(defun probe-rule-pairs (ids)
  (if (endp ids) nil
    (let* ((s (car ids)) (i (search "/" s)))
      (cons (if (and i (< (1+ i) (length s))) (cons (subseq s 0 i) (subseq s (1+ i) (length s))) (cons (if i (subseq s 0 i) s) "(unnamed)"))
            (probe-rule-pairs (cdr ids))))))

(defun probe-err-kinds (errs)
  (if (endp errs) nil
    (cons (second (car errs)) (probe-err-kinds (cdr errs)))))

(defun probe-err-fns (errs)
  (if (endp errs) nil
    (cons (first (car errs)) (probe-err-fns (cdr errs)))))

; --- IL statistics (plan §1.1) --------------------------------------------

(defun probe-flat (forms)
  ;; top-level forms with REC groups opened
  (cond ((endp forms) nil)
        ((is (car forms) "REC") (append (cdr (car forms)) (probe-flat (cdr forms))))
        (t (cons (car forms) (probe-flat (cdr forms))))))

(defun probe-of-kind (xs k)
  (cond ((endp xs) nil)
        ((is (car xs) k) (cons (car xs) (probe-of-kind (cdr xs) k)))
        (t (probe-of-kind (cdr xs) k))))

(defun probe-has-head (xs k)
  (and (consp xs) (or (is (car xs) k) (probe-has-head (cdr xs) k))))

(defun probe-clauseless (defs)
  (cond ((endp defs) nil)
        ((probe-has-head (cddr (car defs)) "CLAUSE") (probe-clauseless (cdr defs)))
        (t (cons (second (car defs)) (probe-clauseless (cdr defs))))))

(defun probe-param-of-kind (ps k)
  (and (consp ps) (or (and (param-p (car ps)) (is (car ps) k)) (probe-param-of-kind (cdr ps) k))))

(defun probe-defs-with-param (defs k)
  (cond ((endp defs) nil)
        ((mv-let (ps more) (def-parts (car defs)) (declare (ignore more)) (probe-param-of-kind ps k))
         (cons (second (car defs)) (probe-defs-with-param (cdr defs) k)))
        (t (probe-defs-with-param (cdr defs) k))))

(defun probe-rule-count (r)
  (len (probe-of-kind (cddr r) "RULE")))

(defun probe-rel-rules (rels)
  ;; ((name . nrules) ...)
  (if (endp rels) nil
    (cons (cons (second (car rels)) (probe-rule-count (car rels))) (probe-rel-rules (cdr rels)))))

(defun probe-sum-cdrs (l) (if (endp l) 0 (+ (cdr (car l)) (probe-sum-cdrs (cdr l)))))

(defun probe-zero-rules (rr)
  (cond ((endp rr) nil)
        ((eql (cdr (car rr)) 0) (cons (car rr) (probe-zero-rules (cdr rr))))
        (t (probe-zero-rules (cdr rr)))))

(defun probe-take (n l) (if (or (zp n) (endp l)) nil (cons (car l) (probe-take (1- n) (cdr l)))))

(defun probe-max-rec (forms best)
  ;; largest REC group: (size . first-member-id)
  (cond ((endp forms) best)
        ((and (is (car forms) "REC") (> (len (cdr (car forms))) (car best)))
         (probe-max-rec (cdr forms) (cons (len (cdr (car forms))) (second (cadr (car forms))))))
        (t (probe-max-rec (cdr forms) best))))

(defun probe-prefix-count (ids c)
  (cond ((endp ids) 0)
        ((and (stringp (car ids)) (< 0 (length (car ids))) (eql (char (car ids) 0) c))
         (1+ (probe-prefix-count (cdr ids) c)))
        (t (probe-prefix-count (cdr ids) c))))

(defun probe-print-il-stats (forms)
  (let* ((flat (probe-flat forms))
         (defs (probe-of-kind flat "DEF"))
         (rels (probe-of-kind flat "REL"))
         (grams (strip-seconds (probe-of-kind flat "GRAM")))
         (clauseless (probe-clauseless defs))
         (hodefs (probe-defs-with-param defs "DEF"))
         (tdefs (probe-defs-with-param defs "TYP"))
         (rr (probe-rel-rules rels))
         (rec (probe-max-rec forms (cons 0 nil))))
    (progn$
     (cw "Rules: ~x0, in ~x1 relations; relations with no rules: ~x2~%"
         (probe-sum-cdrs rr) (len rels) (strip-cars (probe-zero-rules rr)))
     (cw "Relations with the most rules: ~x0~%" (probe-take 8 (probe-by-count rr nil)))
     (cw "Clause-less defs: ~x0~%" (len clauseless))
     (cw "Defs taking def (function) parameters: ~x0: ~s1~%" (len hodefs) (join-words hodefs))
     (cw "Defs taking type parameters: ~x0~%" (len tdefs))
     (cw "Largest rec group: ~x0 members (first: ~s1)~%" (car rec) (or (cdr rec) "-"))
     (cw "Grammars: ~x0, binary B*: ~x1, text T*: ~x2~%"
         (len grams) (probe-prefix-count grams #\B) (probe-prefix-count grams #\T)))))

(defun probe-name-counts (tbl)
  (list :typ (len (cdr (assoc :typ tbl))) :def (len (cdr (assoc :def tbl)))
        :rel (len (cdr (assoc :rel tbl))) :rule (len (cdr (assoc :rule tbl)))
        :gram (len (cdr (assoc :gram tbl))) :var (len (cdr (assoc :var tbl)))
        :atom (len (cdr (assoc :atom tbl)))))

(defun probe-print-lines (l)
  (if (endp l) nil (prog2$ (cw "  ~x0~%" (car l)) (probe-print-lines (cdr l)))))

(defun probe-partial-dropped (ps)
  (if (endp ps) 0 (+ (len (third (car ps))) (probe-partial-dropped (cdr ps)))))

(defun probe-print-partial (ps)
  (if (endp ps) nil
    (let ((p (car ps)))
      (prog2$ (cw "  ~s0 (~x4): ~x1/~x2 translated; dropped: ~s3~%" (first p)
                  (- (second p) (len (third p))) (second p) (join-words (third p)) (fourth p))
              (probe-print-partial (cdr ps))))))

; failing rules: ((rule mode) . errors), in order of first error
(defun probe-rule-errs (errs acc)
  (if (endp errs) acc
    (let* ((ctx (cdddr (car errs))) (r (member :rule ctx)))
      (probe-rule-errs (cdr errs)
                       (if r
                           (let* ((k (list (cadr r) (cadr (member :mode ctx))))
                                  (old (cdr (assoc-equal k acc))))
                             (put-assoc-equal k (append old (list (car errs))) acc))
                         acc)))))

(defun probe-print-rule-errs (l)
  ;; rule  mode  kinds  first error detail
  (if (endp l) nil
    (let ((es (cdr (car l))))
      (prog2$ (cw "~s0 ~x1 ~x2 ~x3~%" (first (car (car l))) (second (car (car l)))
                  (probe-tally (probe-err-kinds es) nil) (third (car es)))
              (probe-print-rule-errs (cdr l))))))

(defun probe-run (il-file config-file names drop errors-file rt-names state)
  (mv-let (erp forms hints state) (read-il il-file state)
    (if erp (mv erp state)
      (mv-let (erp cfg state) (read-il-file config-file state)
        (if erp (mv erp state)
          (let* ((schema-errs (check-il-forms forms nil nil))
                 (tbl (mangle-table forms)))
            (mv-let (collisions renamed atom-collisions) (mangle-report tbl)
              (let* ((config (probe-drop-kinds (car cfg) drop))
                     (forms (apply-patches forms (config-entries config :il-patch)))
                     (spec (mv-list 3 (specialize-fn-args forms)))
                     (forms (first spec))
                     (cx (list (cons :tbl tbl)
                               (cons :overrides (config-overrides config))
                               (cons :split-rules (split-rules (config-entries config :split)))
                               (cons :inverses (all-inverse-pairs hints config))
                               (cons :sized (sized-pairs (config-entries config :sized)))
                               (cons :decreasing (decreasing-pairs (config-entries config :decreasing)))
                               (cons :rel-overrides (rel-override-alist (config-entries config :rel-override)))
                               (cons :memo (memo-rels (config-entries config :memoize)))
                               (cons :gram-defs (gram-defs forms)))))
                (mv-let (events builtins skipped cx) (time$ (cforms forms cx))
                  (let* ((stubs (reverse (cx-get :stubs cx)))
                         (errs (reverse (cx-get :errs cx)))
                         (incomplete (reverse (cx-get :incomplete cx)))
                         (groups (probe-sort-groups (probe-group (probe-stub-files stubs tbl names) nil))))
                    (prog2$
                     (progn$
                      (cw "~%PROBE-REPORT-BEGIN~%")
                      (cw "IL forms (top level): ~x0, hint forms: ~x1~%" (len forms) (len hints))
                      (cw "IL forms by kind (rec members counted): ~x0~%" (count-heads forms nil))
                      (cw "IL names: ~x0~%" (probe-name-counts tbl))
                      (probe-print-il-stats forms)
                      (cw "Config entries used: ~x0 (ignored kinds: ~x1)~%" (len config) drop)
                      (cw "Config entries that do not match the IL: ~x0~%" (len (config-errors config forms tbl)))
                      (probe-print-lines (config-errors config forms tbl))
                      (cw "~%Schema errors: ~x0~%" (len schema-errs))
                      (probe-print-tally-sorted (probe-tally (probe-schema-keys schema-errs) nil))
                      (if schema-errs (cw "  in: ~x0~%" (probe-group (probe-schema-ctx schema-errs) nil)) nil)
                      (cw "~%Mangling: collisions ~x0, renamed ~x1, atom collisions ~x2~%"
                          (len collisions) (len renamed) (len atom-collisions))
                      (cw "~%Phase 1: events ~x0, defuns ~x1, builtins/overrides ~x2, forms skipped ~x3~%"
                          (len events) (probe-count-defuns events 0) (len builtins) (len skipped))
                      (let ((cls (classify-builtins forms hints config)))
                        (cw "~%Builtins (clause-less defs): ~x0; numeric ~x1 (no definition in rt/: ~x2), choice ~x3, host ~x4, notation ~x5, unclassified ~x6~%  missing in rt/: ~s7~%"
                            (len cls) (len (ids-of-category cls :numeric))
                            (len (missing-in-rt (ids-of-category cls :numeric) rt-names tbl))
                            (len (ids-of-category cls :choice)) (len (ids-of-category cls :host))
                            (len (ids-of-category cls :notation)) (len (ids-of-category cls nil))
                            (join-words (missing-in-rt (ids-of-category cls :numeric) rt-names tbl))))
                      (cw "~%Specialized defs with function parameters (G1): ~x0 dropped, ~x1 specializations~%" (len (third spec)) (len (second spec)))
                      (cw "~%Stubs: ~x0~%" (len stubs))
                      (cw "Stubs by source file:~%")
                      (probe-print-groups groups)
                      (cw "~%Relations emitted without some rules (per-rule stubs): ~x0, rules dropped: ~x1~%"
                          (len (cx-get :partial cx)) (probe-partial-dropped (cx-get :partial cx)))
                      (probe-print-partial (cx-get :partial cx))
                      (cw "~%Relation groups where no mode compiles every rule: ~x0~%" (len (cx-get :attempt-log cx)))
                      (cw "  (members, (failing rules . relation-level errors) for attempts 0 :fun, 1 :check, 2 :multi, best and emitted attempt):~%")
                      (probe-print-lines (cx-get :attempt-log cx))
                      (cw "~%Logged errors: ~x0, in ~x1 functions~%" (len errs) (len (probe-tally (probe-err-fns errs) nil)))
                      (cw "Errors by kind:~%")
                      (probe-print-tally-sorted (probe-tally (probe-err-kinds errs) nil))
                      (cw "~%Rules dropped from split variants (all attempts, including discarded ones): ~x0~%" (len incomplete))
                      (probe-print-groups (probe-group (probe-rule-pairs incomplete) nil))
                      (cw "PROBE-REPORT-END~%")
                      (cw "PROBE-RULES-BEGIN~%")
                      (probe-print-rule-errs (probe-rule-errs errs nil))
                      (cw "PROBE-RULES-END~%"))
                     (write-file errors-file
                                 (list "; Every error logged by translator phase 1 (make probe)."
                                       "; One per line: (function kind detail [:rule \"Rel/id\" :pos k] [:mode m]).")
                                 errs state))))))))))))
(mv-let (rt-erp rt-names state) (rt-defined-names *rt-files* nil state)
 (declare (ignore rt-erp))
  (mv-let (erp state)
    (probe-run (@ acl2::probe-il) (@ acl2::probe-config) (@ acl2::probe-names)
               (@ acl2::probe-drop) (@ acl2::probe-errors) rt-names state)
    (if erp
        (prog2$ (cw "~%probe FAILED:~%~@0~%" erp) (mv (good-bye 1) nil state))
      (mv nil :probe-ok state))))
(good-bye 0)
