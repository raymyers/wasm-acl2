; Name mangling: SpecTec identifiers -> ACL2 symbol names (plan §2.1).
;
; The mapping is a fixed, injective function of the identifier and of the set
; of identifiers in the same namespace (only to resolve case-folding
; collisions). Rules:
;
;  base(id): upcase letters; keep digits, `_` and `.`; map
;      '  -> -PRIME    *  -> -STAR    ?  -> -OPT    +  -> -PLUS
;    `-` is kept only in rule names (SpecTec rule ids contain it; other ids
;    cannot), anything else becomes -X<hex>-.
;  case-fold collisions: when several ids in a namespace share a base, the
;    all-lowercase one (if any) keeps the base and every other one gets
;    ^<mask>, the mask spelling the case of each letter (U/L).
;    e.g. types "n" -> N, "N" -> N^U.  Carets never occur in SpecTec ids, so
;    the result stays injective.
;  reserved variable names (T, NIL, STATE, ...) get the suffix ^R.
;
; Namespaces and affixes:
;   :typ  NAME-P (recognizer)      :def  $NAME        :rel  NAME
;   :rule REL/RULE                 :gram GRAM/NAME    :var  NAME
;   :atom (constructor tag, keyword): the mixop with every % removed when
;         that leaves a plain [A-Z0-9_.]+ name, otherwise the mixop verbatim.
(in-package "IL2ACL2")
(include-book "schema")
(program)

(defun hex-digit (n) (char "0123456789ABCDEF" n))

(defun mangle-chars (cs allow-dash)
  (if (endp cs)
      nil
    (let ((c (car cs)) (rest (mangle-chars (cdr cs) allow-dash)))
      (cond ((or (and (char<= #\a c) (char<= c #\z))
                 (and (char<= #\A c) (char<= c #\Z)))
             (cons (char-upcase c) rest))
            ((or (and (char<= #\0 c) (char<= c #\9))
                 (eql c #\_) (eql c #\.))
             (cons c rest))
            ((eql c #\') (append (coerce "-PRIME" 'list) rest))
            ((eql c #\*) (append (coerce "-STAR" 'list) rest))
            ((eql c #\?) (append (coerce "-OPT" 'list) rest))
            ((eql c #\+) (append (coerce "-PLUS" 'list) rest))
            ((and allow-dash (eql c #\-)) (cons c rest))
            (t (let ((n (char-code c)))
                 (append (list #\- #\X (hex-digit (floor n 16)) (hex-digit (mod n 16)) #\-)
                         rest)))))))

(defun base-name (id allow-dash)
  (coerce (mangle-chars (coerce id 'list) allow-dash) 'string))

(defun case-mask (cs)
  (cond ((endp cs) nil)
        ((and (char<= #\a (car cs)) (char<= (car cs) #\z)) (cons #\L (case-mask (cdr cs))))
        ((and (char<= #\A (car cs)) (char<= (car cs) #\Z)) (cons #\U (case-mask (cdr cs))))
        (t (case-mask (cdr cs)))))

(defun no-upper-p (cs)
  (or (endp cs)
      (and (not (and (char<= #\A (car cs)) (char<= (car cs) #\Z)))
           (no-upper-p (cdr cs)))))

(defconst *reserved-var-names*
  '("T" "NIL" "STATE" "&REST" "&OPTIONAL" "&KEY" "&BODY" "&WHOLE"))

(defun ids-with-base (ids base allow-dash)
  (cond ((endp ids) nil)
        ((equal (base-name (car ids) allow-dash) base)
         (cons (car ids) (ids-with-base (cdr ids) base allow-dash)))
        (t (ids-with-base (cdr ids) base allow-dash))))

; ids: duplicate-free list of strings in one namespace.
; Returns an alist id -> mangled base (before namespace affixes).
(defun mangle-ids (ids all allow-dash reserved)
  (if (endp ids)
      nil
    (let* ((id (car ids))
           (base (base-name id allow-dash))
           (group (ids-with-base all base allow-dash))
           (name (if (or (endp (cdr group)) (no-upper-p (coerce id 'list)))
                     base
                   (concatenate 'string base "^"
                                (coerce (case-mask (coerce id 'list)) 'string))))
           (name (if (member-equal name reserved)
                     (concatenate 'string name "^R")
                   name)))
      (cons (cons id name) (mangle-ids (cdr ids) all allow-dash reserved)))))

(defun plain-tag-chars-p (cs)
  (or (endp cs)
      (and (or (and (char<= #\A (car cs)) (char<= (car cs) #\Z))
               (and (char<= #\0 (car cs)) (char<= (car cs) #\9))
               (eql (car cs) #\_) (eql (car cs) #\.))
           (plain-tag-chars-p (cdr cs)))))

(defun atom-tag (mixop)
  (let ((stripped (remove #\% (coerce mixop 'list))))
    (if (and (consp stripped) (plain-tag-chars-p stripped))
        (coerce stripped 'string)
      mixop)))

(defun atom-tags (mixops)
  (if (endp mixops)
      nil
    (cons (cons (car mixops) (atom-tag (car mixops)))
          (atom-tags (cdr mixops)))))

; --- Collecting identifiers per namespace -------------------------------

(defun collect-notes (acc kind)
  (cond ((endp acc) nil)
        ((eq (car (car acc)) kind)
         (cons (second (car acc)) (collect-notes (cdr acc) kind)))
        (t (collect-notes (cdr acc) kind))))

(defun remove-if-not-ns (pairs ns)
  (cond ((endp pairs) nil)
        ((eq (car (car pairs)) ns) (cons (car pairs) (remove-if-not-ns (cdr pairs) ns)))
        (t (remove-if-not-ns (cdr pairs) ns))))

(defun defs-of (forms ns)
  ;; ids of top-level definitions in namespace ns, in IL order
  (cond ((endp forms) nil)
        (t (append (strip-cdrs (remove-if-not-ns (def-names (car forms)) ns))
                   (defs-of (cdr forms) ns)))))

(defun rule-ids (rules)
  (if (endp rules)
      nil
    (cons (second (car rules)) (rule-ids (cdr rules)))))

(defun rel-rules (x)
  ;; (rel id params... mixop typ rules...)
  (let* ((rest (cddr x))
         (ps (take-while-params rest)))
    (nthcdr (+ 2 (len ps)) rest)))

(defun pair-with (x l)
  (if (endp l) nil (cons (cons x (car l)) (pair-with x (cdr l)))))

(defun rule-pairs (forms)
  ;; list of (rel-id . rule-id) for every relation rule, in IL order
  (cond ((endp forms) nil)
        ((is (car forms) "REC")
         (append (rule-pairs (cdr (car forms))) (rule-pairs (cdr forms))))
        ((is (car forms) "REL")
         (append (pair-with (second (car forms)) (rule-ids (rel-rules (car forms))))
                 (rule-pairs (cdr forms))))
        (t (rule-pairs (cdr forms)))))

; --- The mangle table --------------------------------------------------

(defun prefix-all (alist pre suf)
  (if (endp alist)
      nil
    (cons (cons (car (car alist))
                (concatenate 'string pre (cdr (car alist)) suf))
          (prefix-all (cdr alist) pre suf))))

(defun mangle-rules (pairs relmap all-rule-ids rule-map)
  (declare (ignore all-rule-ids))
  (if (endp pairs)
      nil
    (let ((rel (car (car pairs))) (rule (cdr (car pairs))))
      (cons (cons (car pairs)
                  (concatenate 'string (cdr (assoc-equal rel relmap)) "/"
                               (cdr (assoc-equal rule rule-map))))
            (mangle-rules (cdr pairs) relmap nil rule-map)))))

; Returns an alist ns -> (alist id -> symbol-name string).
(defun mangle-table (forms)
  (let* ((acc (chk-defs forms nil))
         (vars (remove-duplicates-equal (collect-notes acc :var)))
         (atoms (remove-duplicates-equal (collect-notes acc :atom)))
         (typs (defs-of forms :typ))
         (defs (defs-of forms :def))
         (rels (defs-of forms :rel))
         (grams (defs-of forms :gram))
         (pairs (rule-pairs forms))
         (rule-ids (remove-duplicates-equal (strip-cdrs pairs)))
         (relmap (mangle-ids rels rels nil nil))
         (rule-map (mangle-ids rule-ids rule-ids t nil)))
    (list (cons :typ (prefix-all (mangle-ids typs typs nil nil) "" "-P"))
          (cons :def (prefix-all (mangle-ids defs defs nil nil) "$" ""))
          (cons :rel relmap)
          (cons :rule (mangle-rules pairs relmap nil rule-map))
          (cons :gram (prefix-all (mangle-ids grams grams nil nil) "GRAM/" ""))
          (cons :var (mangle-ids vars vars nil *reserved-var-names*))
          (cons :atom (atom-tags atoms)))))

; --- Reports -----------------------------------------------------------

(defun remove-if-not-val (alist v)
  (cond ((endp alist) nil)
        ((equal (cdr (car alist)) v) (cons (car alist) (remove-if-not-val (cdr alist) v)))
        (t (remove-if-not-val (cdr alist) v))))

(defun dup-values (alist seen)
  ;; values occurring more than once, with their keys
  (cond ((endp alist) nil)
        (t (let* ((v (cdr (car alist)))
                  (keys (strip-cars (remove-if-not-val alist v))))
             (if (or (member-equal v seen) (endp (cdr keys)))
                 (dup-values (cdr alist) (cons v seen))
               (cons (cons v keys) (dup-values (cdr alist) (cons v seen))))))))

(defun has-caret (s) (and (member #\^ (coerce s 'list)) t))

(defun renamed-entries (alist)
  ;; entries whose name needed a collision/reserved suffix
  (cond ((endp alist) nil)
        ((has-caret (cdr (car alist)))
         (cons (car alist) (renamed-entries (cdr alist))))
        (t (renamed-entries (cdr alist)))))

; Function symbols must be distinct across all function namespaces.
(defun function-names (table)
  (append (cdr (assoc :typ table)) (cdr (assoc :def table))
          (cdr (assoc :rel table)) (cdr (assoc :rule table))
          (cdr (assoc :gram table))))

; Returns (mv collisions renamed atom-collisions):
;   collisions      : function or variable names that are NOT unique (must be nil)
;   renamed         : ids that got a ^ suffix (informational, emitted as a table)
;   atom-collisions : distinct mixops sharing a tag (checked per variant in T2)
(defun mangle-report (table)
  (mv (append (dup-values (function-names table) nil)
              (dup-values (cdr (assoc :var table)) nil))
      (append (renamed-entries (function-names table))
              (renamed-entries (cdr (assoc :var table))))
      (dup-values (cdr (assoc :atom table)) nil)))
