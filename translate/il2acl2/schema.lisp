; IL S-expression schema, mirroring spectec/src/backend-ast/print.ml at the
; pinned SpecTec rev. Any form this does not recognize is an error, so a
; SpecTec upgrade that changes the IL fails loudly here (plan §T1).
;
; The walkers thread an accumulator ACC of entries:
;   (:err CTX WHAT X)   schema violation (CTX = enclosing top-level id)
;   (:ref NS NAME)      reference to a global NS in (:typ :def :rel :gram)
; and a list B of locally bound (NS . NAME) pairs (type/def/grammar params),
; so references to parameters are not reported as global references.
(in-package "IL2ACL2")
(include-book "read")
(program)

(defun sym-name (x) (and (symbolp x) x (symbol-name x)))

(defun name-in (x names) (and (member-equal (sym-name x) names) t))

(defun nodep (x name n)
  (and (is x name) (true-listp x) (= (len x) (1+ n))))

(defun err (ctx what x acc) (cons (list :err ctx what x) acc))

; Identifier occurrences, for name mangling: (:var NAME) / (:atom MIXOP).
(defun note (kind name acc) (cons (list kind name) acc))

(defun ref (ns name b acc)
  (if (member-equal (cons ns name) b)
      acc
    (cons (list :ref ns name) acc)))

(defconst *numtyps* '("NAT" "INT" "RAT" "REAL"))
(defconst *unops* '("NOT" "PLUS" "MINUS" "PLUSMINUS" "MINUSPLUS"))
(defconst *binops* '("AND" "OR" "IMPL" "EQUIV" "ADD" "SUB" "MUL" "DIV" "MOD" "POW"))
(defconst *cmpops* '("EQ" "NE" "LT" "GT" "LE" "GE"))

(defun optyp-p (x) (or (atom-is x "BOOL") (name-in x *numtyps*)))

(defun numlit-p (x)
  (cond ((nodep x "NAT" 1) (natp (second x)))
        ((nodep x "INT" 1) (integerp (second x)))
        ((nodep x "RAT" 1) (rationalp (second x)))
        (t nil)))  ; (real r) cannot be read by ACL2; none occur in WASM 1.0

; Grammar literal: (num 0xNN) reads as a symbol named "0XNN". Binary
; grammars use bytes (two digits); text grammars (WASM 3.0 `6.*`) use
; Unicode code points up to 0x10FFFF (up to six digits).
(defun hex-digits-p (cs)
  (or (endp cs)
      (and (or (and (char<= #\0 (car cs)) (char<= (car cs) #\9))
               (and (char<= #\A (car cs)) (char<= (car cs) #\F)))
           (hex-digits-p (cdr cs)))))

(defun hexcode-p (x)
  (let ((s (sym-name x)))
    (and (stringp s) (<= 4 (length s)) (<= (length s) 8)
         (equal (subseq s 0 2) "0X")
         (hex-digits-p (coerce (subseq s 2 (length s)) 'list)))))

; Parameters (binders) vs arguments, distinguished by shape.
(defun param-p (x)
  (and (true-listp x)
       (stringp (second x))
       (or (and (is x "EXP") (= (len x) 3))
           (and (is x "TYP") (= (len x) 2))
           (and (or (is x "DEF") (is x "GRAM")) (>= (len x) 3)))))

(defun arg-p (x)
  (and (true-listp x) (= (len x) 2)
       (or (and (or (is x "EXP") (is x "TYP") (is x "GRAM"))
                (not (stringp (second x))))
           (and (is x "DEF") (stringp (second x))))))

(defun take-while-params (l)
  (if (and (consp l) (param-p (car l)))
      (cons (car l) (take-while-params (cdr l)))
    nil))

(defun take-while-args (l)
  (if (and (consp l) (arg-p (car l)))
      (cons (car l) (take-while-args (cdr l)))
    nil))

(defun binders (params)
  (cond ((endp params) nil)
        ((is (car params) "TYP") (cons (cons :typ (second (car params)))
                                       (binders (cdr params))))
        ((is (car params) "DEF") (cons (cons :def (second (car params)))
                                       (binders (cdr params))))
        ((is (car params) "GRAM") (cons (cons :gram (second (car params)))
                                        (binders (cdr params))))
        (t (binders (cdr params)))))

(defun all-heads (l name)
  (or (endp l) (and (is (car l) name) (all-heads (cdr l) name))))

(mutual-recursion

 (defun chk-iter (x ctx b acc)
   (cond ((name-in x '("OPT" "LIST" "LIST1")) acc)
         ((nodep x "LISTN" 1) (chk-exp (second x) ctx b acc))
         ((and (nodep x "LISTN" 2) (stringp (third x)))
          (chk-exp (second x) ctx b (note :var (third x) acc)))
         (t (err ctx "iter" x acc))))

 (defun chk-typ (x ctx b acc)
   (cond ((name-in x '("BOOL" "NAT" "INT" "RAT" "REAL" "TEXT")) acc)
         ((and (is x "VAR") (true-listp x) (stringp (second x)))
          (chk-args (cddr x) ctx b (ref :typ (second x) b acc)))
         ((and (is x "TUP") (true-listp x)) (chk-binds (cdr x) ctx b acc))
         ((nodep x "ITER" 2)
          (chk-iter (third x) ctx b (chk-typ (second x) ctx b acc)))
         (t (err ctx "typ" x acc))))

 (defun chk-binds (l ctx b acc)
   (cond ((endp l) acc)
         ((and (nodep (car l) "BIND" 2) (stringp (second (car l))))
          (chk-binds (cdr l) ctx b (chk-typ (third (car l)) ctx b
                                             (note :var (second (car l)) acc))))
         (t (err ctx "bind" (car l) acc))))

 (defun chk-exps (l ctx b acc)
   (if (endp l)
       acc
     (chk-exps (cdr l) ctx b (chk-exp (car l) ctx b acc))))

 (defun chk-doms (l ctx b acc)
   (cond ((endp l) acc)
         ((and (nodep (car l) "DOM" 2) (stringp (second (car l))))
          (chk-doms (cdr l) ctx b (chk-exp (third (car l)) ctx b
                                            (note :var (second (car l)) acc))))
         (t (err ctx "dom" (car l) acc))))

 (defun chk-expfields (l ctx b acc)
   (cond ((endp l) acc)
         ((and (nodep (car l) "FIELD" 2) (stringp (second (car l))))
          (chk-expfields (cdr l) ctx b (chk-exp (third (car l)) ctx b
                                                 (note :atom (second (car l)) acc))))
         (t (err ctx "expfield" (car l) acc))))

 (defun chk-exp (x ctx b acc)
   (cond
    ((nodep x "VAR" 1) (if (stringp (second x)) (note :var (second x) acc)
                         (err ctx "var" x acc)))
    ((nodep x "BOOL" 1) (if (name-in (second x) '("TRUE" "FALSE")) acc
                          (err ctx "bool" x acc)))
    ((nodep x "NUM" 1) (if (numlit-p (second x)) acc (err ctx "num" x acc)))
    ((nodep x "TEXT" 1) (if (stringp (second x)) acc (err ctx "text" x acc)))
    ((nodep x "UN" 3)
     (if (and (name-in (second x) *unops*) (optyp-p (third x)))
         (chk-exp (fourth x) ctx b acc)
       (err ctx "un" x acc)))
    ((or (nodep x "BIN" 4) (nodep x "CMP" 4))
     (if (and (name-in (second x) (if (is x "BIN") *binops* *cmpops*))
              (optyp-p (third x)))
         (chk-exps (cdddr x) ctx b acc)
       (err ctx "bin/cmp" x acc)))
    ((or (nodep x "IDX" 2) (nodep x "COMP" 2) (nodep x "MEM" 2)
         (nodep x "CAT" 2) (nodep x "SLICE" 3) (nodep x "LEN" 1)
         (nodep x "UNOPT" 1) (nodep x "LIFT" 1)
         (and (is x "TUP") (true-listp x))
         (and (is x "LIST") (true-listp x))
         (and (is x "OPT") (true-listp x) (<= (len x) 2)))
     (chk-exps (cdr x) ctx b acc))
    ((or (nodep x "UPD" 3) (nodep x "EXT" 3))
     (chk-exp (fourth x) ctx b
              (chk-path (third x) ctx b (chk-exp (second x) ctx b acc))))
    ((and (is x "STRUCT") (true-listp x)) (chk-expfields (cdr x) ctx b acc))
    ((nodep x "DOT" 2)
     (if (stringp (third x)) (chk-exp (second x) ctx b (note :atom (third x) acc))
       (err ctx "dot" x acc)))
    ((and (is x "CALL") (true-listp x) (stringp (second x)))
     (chk-args (cddr x) ctx b (ref :def (second x) b acc)))
    ((and (is x "ITER") (true-listp x) (>= (len x) 3))
     (chk-doms (cdddr x) ctx b
               (chk-iter (third x) ctx b (chk-exp (second x) ctx b acc))))
    ((nodep x "PROJ" 2)
     (if (natp (third x)) (chk-exp (second x) ctx b acc)
       (err ctx "proj" x acc)))
    ((nodep x "CASE" 2)
     (if (stringp (second x)) (chk-exp (third x) ctx b (note :atom (second x) acc))
       (err ctx "case" x acc)))
    ((nodep x "UNCASE" 2)
     (if (stringp (third x)) (chk-exp (second x) ctx b (note :atom (third x) acc))
       (err ctx "uncase" x acc)))
    ((nodep x "CVT" 3)
     (if (and (name-in (second x) *numtyps*) (name-in (third x) *numtyps*))
         (chk-exp (fourth x) ctx b acc)
       (err ctx "cvt" x acc)))
    ((nodep x "SUB" 3)
     (chk-exp (fourth x) ctx b
              (chk-typ (third x) ctx b (chk-typ (second x) ctx b acc))))
    (t (err ctx "exp" x acc))))

 (defun chk-path (x ctx b acc)
   (cond ((atom-is x "ROOT") acc)
         ((nodep x "IDX" 2)
          (chk-exp (third x) ctx b (chk-path (second x) ctx b acc)))
         ((nodep x "SLICE" 3)
          (chk-exps (cddr x) ctx b (chk-path (second x) ctx b acc)))
         ((and (nodep x "DOT" 2) (stringp (third x)))
          (chk-path (second x) ctx b (note :atom (third x) acc)))
         (t (err ctx "path" x acc))))

 (defun chk-syms (l ctx b acc)
   (if (endp l)
       acc
     (chk-syms (cdr l) ctx b (chk-sym (car l) ctx b acc))))

 (defun chk-sym (x ctx b acc)
   (cond ((atom-is x "EPS") acc)
         ((and (is x "VAR") (true-listp x) (stringp (second x)))
          (chk-args (cddr x) ctx b (ref :gram (second x) b acc)))
         ((nodep x "NUM" 1) (if (hexcode-p (second x)) acc
                              (err ctx "sym num" x acc)))
         ((nodep x "TEXT" 1) (if (stringp (second x)) acc
                               (err ctx "sym text" x acc)))
         ((or (and (is x "SEQ") (true-listp x))
              (and (is x "ALT") (true-listp x))
              (nodep x "RANGE" 2))
          (chk-syms (cdr x) ctx b acc))
         ((and (is x "ITER") (true-listp x) (>= (len x) 3))
          (chk-doms (cdddr x) ctx b
                    (chk-iter (third x) ctx b (chk-sym (second x) ctx b acc))))
         ((nodep x "ATTR" 2)
          (chk-sym (third x) ctx b (chk-exp (second x) ctx b acc)))
         (t (err ctx "sym" x acc))))

 (defun chk-arg (x ctx b acc)
   (cond ((is x "EXP") (chk-exp (second x) ctx b acc))
         ((is x "TYP") (chk-typ (second x) ctx b acc))
         ((is x "DEF") (ref :def (second x) b acc))
         ((is x "GRAM") (chk-sym (second x) ctx b acc))
         (t (err ctx "arg" x acc))))

 (defun chk-args (l ctx b acc)
   (cond ((endp l) acc)
         ((arg-p (car l)) (chk-args (cdr l) ctx b (chk-arg (car l) ctx b acc)))
         (t (err ctx "arg" (car l) acc))))

 (defun chk-param (x ctx b acc)
   (cond ((is x "EXP") (chk-typ (third x) ctx b (note :var (second x) acc)))
         ((is x "TYP") acc)
         ((or (is x "DEF") (is x "GRAM"))
          ;; (def id params... typ)
          (let* ((rest (cddr x))
                 (ps (take-while-params rest))
                 (more (nthcdr (len ps) rest))
                 (b2 (append (binders ps) b)))
            (if (= (len more) 1)
                (chk-typ (car more) ctx b2 (chk-params ps ctx b2 acc))
              (err ctx "def/gram param" x acc))))
         (t (err ctx "param" x acc))))

 (defun chk-params (l ctx b acc)
   (if (endp l)
       acc
     (chk-params (cdr l) ctx b (chk-param (car l) ctx b acc))))

 (defun chk-prem (x ctx b acc)
   (cond ((atom-is x "ELSE") acc)
         ((nodep x "IF" 1) (chk-exp (second x) ctx b acc))
         ((nodep x "LET" 2) (chk-exps (cdr x) ctx b acc))
         ((and (is x "RULE") (true-listp x) (>= (len x) 4)
               (stringp (second x)))
          ;; (rule id args... mixop exp)
          (let* ((rest (cddr x))
                 (n (len rest))
                 (args (take (- n 2) rest))
                 (mixop (nth (- n 2) rest))
                 (e (nth (- n 1) rest)))
            (if (stringp mixop)
                (chk-exp e ctx b
                         (chk-args args ctx b (ref :rel (second x) b acc)))
              (err ctx "rule premise" x acc))))
         ((and (is x "ITER") (true-listp x) (>= (len x) 3))
          (chk-doms (cdddr x) ctx b
                    (chk-iter (third x) ctx b (chk-prem (second x) ctx b acc))))
         (t (err ctx "prem" x acc))))

 (defun chk-prems (l ctx b acc)
   (if (endp l)
       acc
     (chk-prems (cdr l) ctx b (chk-prem (car l) ctx b acc))))

 ;; (field mixop typ params... prems...) / (case mixop typ params... prems...)
 (defun chk-typcases (l kind ctx b acc)
   (cond ((endp l) acc)
         ((and (is (car l) kind) (true-listp (car l)) (>= (len (car l)) 3)
               (stringp (second (car l))))
          (let* ((rest (cdddr (car l)))
                 (ps (take-while-params rest))
                 (prs (nthcdr (len ps) rest))
                 (b2 (append (binders ps) b)))
            (chk-typcases (cdr l) kind ctx b
                          (chk-prems prs ctx b2
                                     (chk-params ps ctx b2
                                                 (chk-typ (third (car l)) ctx b2
                                                          (note :atom (second (car l)) acc)))))))
         (t (err ctx kind (car l) acc))))

 (defun chk-deftyp (x ctx b acc)
   (cond ((nodep x "ALIAS" 1) (chk-typ (second x) ctx b acc))
         ((and (is x "STRUCT") (true-listp x)) (chk-typcases (cdr x) "FIELD" ctx b acc))
         ((and (is x "VARIANT") (true-listp x)) (chk-typcases (cdr x) "CASE" ctx b acc))
         (t (err ctx "deftyp" x acc))))

 ;; (inst params... args... deftyp)
 (defun chk-insts (l ctx b acc)
   (cond ((endp l) acc)
         ((and (is (car l) "INST") (true-listp (car l)))
          (let* ((rest (cdr (car l)))
                 (ps (take-while-params rest))
                 (rest (nthcdr (len ps) rest))
                 (as (take-while-args rest))
                 (more (nthcdr (len as) rest))
                 (b2 (append (binders ps) b)))
            (if (= (len more) 1)
                (chk-insts (cdr l) ctx b
                           (chk-deftyp (car more) ctx b2
                                       (chk-args as ctx b2
                                                 (chk-params ps ctx b2 acc))))
              (err ctx "inst" (car l) acc))))
         (t (err ctx "inst" (car l) acc))))

 ;; (rule id params... mixop exp prems...)
 (defun chk-rules (l ctx b acc)
   (cond ((endp l) acc)
         ((and (is (car l) "RULE") (true-listp (car l)) (stringp (second (car l))))
          (let* ((rest (cddr (car l)))
                 (ps (take-while-params rest))
                 (more (nthcdr (len ps) rest))
                 (b2 (append (binders ps) b)))
            (if (and (>= (len more) 2) (stringp (car more)))
                (chk-rules (cdr l) ctx b
                           (chk-prems (cddr more) ctx b2
                                      (chk-exp (cadr more) ctx b2
                                               (chk-params ps ctx b2 acc))))
              (err ctx "rule" (car l) acc))))
         (t (err ctx "rule" (car l) acc))))

 ;; (clause params... args... exp prems...)
 (defun chk-clauses (l ctx b acc)
   (cond ((endp l) acc)
         ((and (is (car l) "CLAUSE") (true-listp (car l)))
          (let* ((rest (cdr (car l)))
                 (ps (take-while-params rest))
                 (rest (nthcdr (len ps) rest))
                 (as (take-while-args rest))
                 (more (nthcdr (len as) rest))
                 (b2 (append (binders ps) b)))
            (if (consp more)
                (chk-clauses (cdr l) ctx b
                             (chk-prems (cdr more) ctx b2
                                        (chk-exp (car more) ctx b2
                                                 (chk-args as ctx b2
                                                           (chk-params ps ctx b2 acc)))))
              (err ctx "clause" (car l) acc))))
         (t (err ctx "clause" (car l) acc))))

 ;; (prod params... sym exp prems...)
 (defun chk-prods (l ctx b acc)
   (cond ((endp l) acc)
         ((and (is (car l) "PROD") (true-listp (car l)))
          (let* ((rest (cdr (car l)))
                 (ps (take-while-params rest))
                 (more (nthcdr (len ps) rest))
                 (b2 (append (binders ps) b)))
            (if (>= (len more) 2)
                (chk-prods (cdr l) ctx b
                           (chk-prems (cddr more) ctx b2
                                      (chk-exp (cadr more) ctx b2
                                               (chk-sym (car more) ctx b2
                                                        (chk-params ps ctx b2 acc)))))
              (err ctx "prod" (car l) acc))))
         (t (err ctx "prod" (car l) acc))))

 (defun chk-def (x acc)
   (cond
    ((and (is x "REC") (true-listp x)) (chk-defs (cdr x) acc))
    ((and (or (is x "TYP") (is x "REL") (is x "DEF") (is x "GRAM"))
          (true-listp x) (stringp (second x)))
     (let* ((ctx (second x))
            (rest (cddr x))
            (ps (take-while-params rest))
            (more (nthcdr (len ps) rest))
            (b (binders ps))
            (acc (chk-params ps ctx b acc)))
       (cond
        ((is x "TYP")
         (if (all-heads more "INST")
             (chk-insts more ctx b acc)
           (err ctx "typ def" x acc)))
        ((is x "REL")
         ;; mixop typ rules...
         (if (and (>= (len more) 2) (stringp (car more)))
             (chk-rules (cddr more) ctx b (chk-typ (cadr more) ctx b acc))
           (err ctx "rel def" x acc)))
        ((is x "DEF")
         ;; typ clauses...
         (if (consp more)
             (chk-clauses (cdr more) ctx b (chk-typ (car more) ctx b acc))
           (err ctx "def def" x acc)))
        (t
         (if (consp more)
             (chk-prods (cdr more) ctx b (chk-typ (car more) ctx b acc))
           (err ctx "gram def" x acc))))))
    (t (err "<top>" "def" x acc))))

 (defun chk-defs (l acc)
   (if (endp l)
       acc
     (chk-defs (cdr l) (chk-def (car l) acc))))
 )

; Names a top-level form defines, as (NS . NAME) pairs.
(defun def-names (x)
  (cond ((is x "REC")
         (if (consp (cdr x))
             (append (def-names (cadr x)) (def-names (cons (car x) (cddr x))))
           nil))
        ((is x "TYP") (list (cons :typ (second x))))
        ((is x "REL") (list (cons :rel (second x))))
        ((is x "DEF") (list (cons :def (second x))))
        ((is x "GRAM") (list (cons :gram (second x))))
        (t nil)))

(defun split-acc (acc errs refs)
  (cond ((endp acc) (mv errs refs))
        ((eq (car (car acc)) :err)
         (split-acc (cdr acc) (cons (car acc) errs) refs))
        ((not (eq (car (car acc)) :ref)) (split-acc (cdr acc) errs refs))
        (t (split-acc (cdr acc) errs (cons (cons (second (car acc)) (third (car acc)))
                                           refs)))))

(defun dangling-refs (refs ok)
  (cond ((endp refs) nil)
        ((member-equal (car refs) ok) (dangling-refs (cdr refs) ok))
        (t (cons (car refs) (dangling-refs (cdr refs) ok)))))

; Check every top-level form against the schema and check that the IL is in
; dependency order: each reference is to something defined by an earlier form,
; or by the same form when that form is a REC group. A non-REC form that
; refers to itself is reported, since the translator relies on REC to know
; where mutual recursion is.
;
; Returns a list of error entries (nil = OK).
(defun check-il-forms (forms defined errs)
  (if (endp forms)
      (reverse errs)
    (let* ((x (car forms))
           (names (def-names x))
           (dups (intersection-equal names defined)))
      (mv-let (ferrs refs)
        (split-acc (chk-def x nil) nil nil)
        (let* ((refs (remove-duplicates-equal refs))
               (forward (dangling-refs refs (append (if (is x "REC") names nil)
                                                    defined)))
               (errs (append (if dups (list (list :err (second x) "duplicate definition" dups))
                               nil)
                             (if forward
                                 (list (list :err (if (is x "REC") "<rec>" (second x))
                                             "forward or undefined reference" forward))
                               nil)
                             ferrs
                             errs)))
          (check-il-forms (cdr forms) (append names defined) errs))))))

(defun count-heads (forms acc)
  ;; alist head-name -> count, counting REC members individually
  (cond ((endp forms) acc)
        ((is (car forms) "REC")
         (count-heads (cdr forms)
                      (count-heads (cdr (car forms))
                                   (put-assoc-equal "REC" (1+ (or (cdr (assoc-equal "REC" acc)) 0))
                                                    acc))))
        (t (let ((h (head (car forms))))
             (count-heads (cdr forms)
                          (put-assoc-equal h (1+ (or (cdr (assoc-equal h acc)) 0)) acc))))))

; --- Hint definitions (wasm3 prep P3; printed by the flake's SpecTec patch) ---
;
; (hint <kind> "<id>" ["<rule id>"] (<name> "<EL expression text>") ...),
; kind one of typ rel def gram rule. They are split off right after reading:
; everything else in the translator sees only definitions.

(defun hint-entries-p (l)
  (or (null l)
      (and (consp l) (true-listp (car l)) (= (len (car l)) 2)
           (sym-name (car (car l))) (stringp (second (car l)))
           (hint-entries-p (cdr l)))))

(defun hint-form-p (x)
  (and (is x "HINT") (true-listp x)
       (let ((k (sym-name (second x))))
         (cond ((member-equal k '("TYP" "REL" "DEF" "GRAM"))
                (and (stringp (third x)) (hint-entries-p (cdddr x))))
               ((equal k "RULE")
                (and (stringp (third x)) (stringp (fourth x)) (hint-entries-p (cddddr x))))
               (t nil)))))

(defun split-hints (forms)
  ;; (mv definitions hints), each in IL order
  (if (endp forms) (mv nil nil)
    (mv-let (ds hs) (split-hints (cdr forms))
      (if (is (car forms) "HINT")
          (mv ds (cons (car forms) hs))
        (mv (cons (car forms) ds) hs)))))

(defun hint-target (h)
  ;; (ns . id) of the definition a hint form annotates
  (let ((k (sym-name (second h))))
    (cons (cond ((equal k "TYP") :typ) ((equal k "REL") :rel) ((equal k "DEF") :def)
                ((equal k "GRAM") :gram) (t :rule))
          (third h))))

(defun check-hints (hints names acc)
  ;; names: (NS . NAME) pairs of every definition (rule hints: their relation)
  (if (endp hints) (reverse acc)
    (let ((h (car hints)))
      (check-hints (cdr hints) names
                   (cond ((not (hint-form-p h)) (err :hint "hint form" h acc))
                         ((let ((tg (hint-target h)))
                            (not (member-equal (if (eq (car tg) :rule) (cons :rel (cdr tg)) tg) names)))
                          (err :hint "hint for an undefined name" h acc))
                         (t acc))))))

(defun all-def-names (forms)
  (if (endp forms) nil (append (def-names (car forms)) (all-def-names (cdr forms)))))
