; Compiler from IL expressions / patterns / premises / types to ACL2 terms
; (plan §2.2-§2.3). Pure functions of the IL plus the mangle table.
;
; Generated names are represented as markers (:%W1T-SYM . "NAME") and turned
; into W1T symbols only at print time (emit.lisp), once the W1T package --
; whose imports depend on the set of generated names -- has been defined.
;
; Compilation context CX is an alist:
;   :tbl      mangle table             :fn   base name for aux functions
;   :n        counter (aux/temps)      :aux  aux defuns emitted so far (reversed)
;   :errs     unsupported constructs   :tparams  type parameters in scope
; ENV maps SpecTec variable names to the ACL2 term (a marker symbol) holding
; their value.
(in-package "IL2ACL2")
(include-book "mangle")
(program)

; --- Context ----------------------------------------------------------

(defun cx-get (k cx) (cdr (assoc-eq k cx)))
(defun cx-put (k v cx) (put-assoc-eq k v cx))

(defun cx-err (what x cx)
  (cx-put :errs (cons (list (cx-get :fn cx) what x) (cx-get :errs cx)) cx))

(defun gsym (name) (cons :%w1t-sym name))
(defun gsym-p (x) (and (consp x) (eq (car x) :%w1t-sym)))

(defun nat-str (n) (coerce (explode-atom n 10) 'string))

(defun cx-fresh (prefix cx)
  ;; (mv name-string cx); names contain % so they never clash with SpecTec ids
  (let ((n (or (cx-get :n cx) 0)))
    (mv (concatenate 'string prefix (nat-str n))
        (cx-put :n (1+ n) cx))))

(defun tbl-name (ns id cx)
  (cdr (assoc-equal id (cdr (assoc-eq ns (cx-get :tbl cx))))))

(defun var-sym (id cx) (gsym (or (tbl-name :var id cx) (concatenate 'string "%UNKNOWN-" id))))
(defun fn-sym (ns id cx) (gsym (or (tbl-name ns id cx) (concatenate 'string "%UNKNOWN-" id))))

(defun tag-kw (mixop) (intern$ (atom-tag mixop) "KEYWORD"))

(defun all-percent-p (cs)
  (or (endp cs) (and (eql (car cs) #\%) (all-percent-p (cdr cs)))))

; Atom-free mixops ("%", "%%") mark single-case newtype variants, which are
; elided (encoded as their payload). The number of holes is the arity.
(defun atom-free-p (m)
  (and (stringp m) (< 0 (length m)) (all-percent-p (coerce m 'list))))

(defun nth-term (i s)
  (if (zp i) (list 'car s) (nth-term (1- i) (list 'cdr s))))

(defun nthcdr-term (i s)
  (if (zp i) s (nthcdr-term (1- i) (list 'cdr s))))

; --- Free variables ----------------------------------------------------

(defun dom-names (doms)
  (if (endp doms) nil (cons (second (car doms)) (dom-names (cdr doms)))))

(mutual-recursion
 (defun fv-exp (e)
   (cond ((atom e) nil)
         ((nodep e "VAR" 1) (list (second e)))
         ((is e "ITER")
          (let* ((it (third e)) (doms (cdddr e))
                 (inner (set-difference-equal
                         (fv-exp (second e))
                         (append (dom-names doms)
                                 (if (and (is it "LISTN") (stringp (third it)))
                                     (list (third it)) nil)))))
            (append inner (fv-doms doms)
                    (if (is it "LISTN") (fv-exp (second it)) nil))))
         ((or (is e "NUM") (is e "TEXT") (is e "BOOL")) nil)
         ;; types are not expressions: only their exp arguments mention variables
         ((or (is e "SUB") (is e "CVT")) (fv-exp (fourth e)))
         ((is e "CALL") (fv-cargs (cddr e)))
         (t (fv-list (cdr e)))))
 (defun fv-cargs (as)
   (cond ((atom as) nil)
         ((is (car as) "EXP") (append (fv-exp (second (car as))) (fv-cargs (cdr as))))
         (t (fv-cargs (cdr as)))))
 (defun fv-doms (doms)
   (if (endp doms) nil (append (fv-exp (third (car doms))) (fv-doms (cdr doms)))))
 (defun fv-list (l)
   (if (atom l) nil (append (fv-exp (car l)) (fv-list (cdr l))))))

(defun bound-in (names env)
  ;; names (deduplicated, in order) that ENV binds
  (cond ((endp names) nil)
        ((assoc-equal (car names) env)
         (cons (car names) (remove-equal (car names) (bound-in (cdr names) env))))
        (t (bound-in (cdr names) env))))

(defun unbound-vars (e env)
  (cond ((endp e) nil)
        ((or (assoc-equal (car e) env) (equal (car e) "_")) (unbound-vars (cdr e) env))
        (t (cons (car e) (unbound-vars (cdr e) env)))))

(defun env-terms (names env)
  (if (endp names) nil
    (cons (cdr (assoc-equal (car names) env)) (env-terms (cdr names) env))))

(defun env-restrict (names env)
  (if (endp names) nil
    (cons (assoc-equal (car names) env) (env-restrict (cdr names) env))))

; --- Steps: tests and bindings, built into nested and / let* ------------

(defun take-binds (steps)
  (if (and (consp steps) (eq (car (car steps)) :bind))
      (cons (cdr (car steps)) (take-binds (cdr steps)))
    nil))

(defun take-tests (steps)
  (if (and (consp steps) (eq (car (car steps)) :test))
      (cons (cadr (car steps)) (take-tests (cdr steps)))
    nil))

(defun bind-pairs (bs)
  (if (endp bs) nil
    (cons (list (car (car bs)) (cdr (car bs))) (bind-pairs (cdr bs)))))

(defun build-steps (steps success)
  (cond ((endp steps) success)
        ;; search points are only supported at the top of a clause/rule body
        ((eq (car (car steps)) :choose) (list (gsym "%SEARCH-NOT-SUPPORTED-HERE")))
        ((eq (car (car steps)) :test)
         (let ((ts (take-tests steps)))
           (cons 'and (append ts (list (build-steps (nthcdr (len ts) steps) success))))))
        (t
         (let ((bs (take-binds steps)))
           (list 'let* (bind-pairs bs)
                 (list 'declare (cons 'ignorable (strip-cars bs)))
                 (build-steps (nthcdr (len bs) steps) success))))))

; Free generated variables (markers) of a generated ACL2 term, in order of
; first occurrence. Function names (car of a call) are not variables.
(mutual-recursion
 (defun term-fv (x bound acc)
   (cond ((gsym-p x) (if (or (member-equal x bound) (member-equal x acc)) acc (append acc (list x))))
         ((atom x) acc)
         ((member-eq (car x) (quote (let let*)))
          (term-fv-binds (cadr x) (cddr x) bound acc))
         ((eq (car x) (quote declare)) acc)
         ((eq (car x) (quote quote)) acc)
         (t (term-fv-list (cdr x) bound acc))))
 (defun term-fv-binds (binds body bound acc)
   ;; sequential (let*) scoping; our generated lets bind distinct fresh names
   (if (atom binds)
       (term-fv-list body bound acc)
     (term-fv-binds (cdr binds) body (cons (car (car binds)) bound)
                    (term-fv (cadr (car binds)) bound acc))))
 (defun term-fv-list (l bound acc)
   (if (atom l) acc (term-fv-list (cdr l) bound (term-fv (car l) bound acc)))))

(defun ignorable-decl (formals) (list 'declare (cons 'ignorable formals)))

(defun mk-defun (name formals body)
  (list 'defun name formals (ignorable-decl formals) body))

(defun mk-defun-measure (name formals measure body)
  (list 'defun name formals (ignorable-decl formals)
        (list 'declare (list 'xargs :measure measure))
        body))

(defun cx-add-aux (defun cx) (cx-put :aux (cons defun (cx-get :aux cx)) cx))

(defun gsyms-prefixed (prefix n)
  ;; (%L0 ... %L{n-1}) markers
  (if (zp n) nil
    (append (gsyms-prefixed prefix (1- n))
            (list (gsym (concatenate 'string prefix (nat-str (1- n))))))))

(defun car-binds (names lsyms cx)
  ;; ((x . (car %L0)) ...)
  (if (endp names) nil
    (cons (cons (var-sym (car names) cx) (list 'car (car lsyms)))
          (car-binds (cdr names) (cdr lsyms) cx))))

(defun strip-thirds (l) (if (endp l) nil (cons (third (car l)) (strip-thirds (cdr l)))))

(defun bind-steps (binds)
  ;; alist (sym . term) -> steps
  (if (endp binds) nil
    (cons (cons :bind (car binds)) (bind-steps (cdr binds)))))

(defun car-bind-steps (names ds cx)
  (if (endp names) nil
    (cons (cons :bind (cons (var-sym (car names) cx) (list 'car (car ds))))
          (car-bind-steps (cdr names) (cdr ds) cx))))

(defun consp-tests (lsyms)
  (if (endp lsyms) nil (cons (list 'consp (car lsyms)) (consp-tests (cdr lsyms)))))

(defun cdr-terms (lsyms)
  (if (endp lsyms) nil (cons (list 'cdr (car lsyms)) (cdr-terms (cdr lsyms)))))

(defun atom-tests (lsyms)
  (if (endp lsyms) nil (cons (list 'atom (car lsyms)) (atom-tests (cdr lsyms)))))

(defun env-add-vars (names env cx)
  (if (endp names) env
    (env-add-vars (cdr names) (acons (car names) (var-sym (car names) cx) env) cx)))

; build-steps with search points: (:choose k lo hi desc) runs the rest of
; the steps for k = lo..hi (or hi..lo), returning the first non-nil result.
; The rest is lambda-lifted into an aux function F/SEARCHn over its free
; variables. Returns (mv term cx).
(defun build-steps-cx (steps success cx)
  (cond ((endp steps) (mv success cx))
        ((eq (car (car steps)) :choose)
         (let* ((st (car steps)) (kv (second st)) (lo (third st)) (hi (fourth st))
                (desc (fifth st)))
           (mv-let (rest cx) (build-steps-cx (cdr steps) success cx)
             (mv-let (aux-name cx) (cx-fresh (concatenate (quote string) (cx-get :fn cx) "/SEARCH") cx)
               (let* ((aux (gsym aux-name))
                      (k (gsym "%K")) (l (gsym "%LO")) (h (gsym "%HI")) (r (gsym "%R"))
                      (fvs (remove-equal kv (term-fv rest nil nil)))
                      (next (list* aux (if desc (list (quote 1-) k) (list (quote 1+) k)) l h fvs))
                      (body (list (quote if)
                                  (list (quote and) (list (quote natp) k) (list (quote natp) l)
                                        (list (quote natp) h) (list (quote <=) l k) (list (quote <=) k h))
                                  (list (quote let) (list (list r (list (quote let) (list (list kv k))
                                                                        (ignorable-decl (list kv)) rest)))
                                        (ignorable-decl (list r))
                                        (list (quote if) r r next))
                                  nil))
                      (def (mk-defun-measure aux (list* k l h fvs)
                                             (if desc
                                                 (list (quote nfix) (list (quote -) (list (quote 1+) k) l))
                                               (list (quote nfix) (list (quote -) (list (quote 1+) h) k)))
                                             body)))
                 (mv (list* aux (if desc hi lo) lo hi fvs) (cx-add-aux def cx)))))))
        ((eq (car (car steps)) :test)
         (let ((ts (take-tests steps)))
           (mv-let (rest cx) (build-steps-cx (nthcdr (len ts) steps) success cx)
             (mv (cons (quote and) (append ts (list rest))) cx))))
        (t
         (let ((bs (take-binds steps)))
           (mv-let (rest cx) (build-steps-cx (nthcdr (len bs) steps) success cx)
             (mv (list (quote let*) (bind-pairs bs) (ignorable-decl (strip-cars bs)) rest) cx))))))

; --- Expressions -------------------------------------------------------

(defun numlit-value (x) (second x))

(defun binop-fn (op typ)
  (let ((op (sym-name op)) (typ (sym-name typ)))
    (cond ((equal op "AND") 'and) ((equal op "OR") 'or)
          ((equal op "IMPL") 'implies) ((equal op "EQUIV") 'iff)
          ((equal op "ADD") '+) ((equal op "SUB") '-) ((equal op "MUL") '*)
          ((equal op "DIV") '/)                 ; SpecTec: exact division
          ((equal op "MOD") 'rem)               ; SpecTec: Z.rem (truncating)
          ((equal op "POW") 'expt)
          (t (prog2$ typ nil)))))

(defun cmpop-term (op a b)
  (let ((op (sym-name op)))
    (cond ((equal op "EQ") (list 'equal a b))
          ((equal op "NE") (list 'not (list 'equal a b)))
          ((equal op "LT") (list '< a b))
          ((equal op "GT") (list '> a b))
          ((equal op "LE") (list '<= a b))
          (t (list '>= a b)))))

(defun hole-subst (term hole val)
  (cond ((equal term hole) val)
        ((atom term) term)
        ((gsym-p term) term)
        (t (cons (hole-subst (car term) hole val) (hole-subst (cdr term) hole val)))))

(defconst *hole* (cons :%w1t-sym "%HOLE"))

(mutual-recursion

 (defun cexp (e env cx)
   (cond
    ((nodep e "VAR" 1)
     (let ((b (assoc-equal (second e) env)))
       (if b (mv (cdr b) cx)
         (mv nil (cx-err "unbound variable" (second e) cx)))))
    ((nodep e "BOOL" 1) (mv (atom-is (second e) "TRUE") cx))
    ((nodep e "NUM" 1) (mv (numlit-value (second e)) cx))
    ((nodep e "TEXT" 1) (mv (second e) cx))
    ((nodep e "UN" 3)
     (mv-let (a cx) (cexp (fourth e) env cx)
       (let ((op (sym-name (second e))))
         (cond ((equal op "NOT") (mv (list 'not a) cx))
               ((equal op "MINUS") (mv (list '- a) cx))
               ((equal op "PLUS") (mv a cx))
               (t (mv nil (cx-err "unop" e cx)))))))
    ((nodep e "BIN" 4)
     (mv-let (a cx) (cexp (fourth e) env cx)
       (mv-let (b cx) (cexp (fifth e) env cx)
         (mv (list (binop-fn (second e) (third e)) a b) cx))))
    ((nodep e "CMP" 4)
     (mv-let (a cx) (cexp (fourth e) env cx)
       (mv-let (b cx) (cexp (fifth e) env cx)
         (mv (cmpop-term (second e) a b) cx))))
    ((nodep e "IDX" 2)
     (mv-let (a cx) (cexp (second e) env cx)
       (mv-let (i cx) (cexp (third e) env cx)
         (mv (list 'nth i a) cx))))
    ((nodep e "SLICE" 3)
     (mv-let (a cx) (cexp (second e) env cx)
       (mv-let (i cx) (cexp (third e) env cx)
         (mv-let (n cx) (cexp (fourth e) env cx)
           (mv (list 'take n (list 'nthcdr i a)) cx)))))
    ((or (nodep e "UPD" 3) (nodep e "EXT" 3))
     (mv-let (base cx) (cexp (second e) env cx)
       (mv-let (v cx) (cexp (fourth e) env cx)
         (cpath (third e) (if (is e "UPD") v (list 'append *hole* v))
                base env cx))))
    ((and (is e "STRUCT") (true-listp e))
     (mv-let (fs cx) (cexpfields (cdr e) env cx)
       (mv (list* 'list :%rec fs) cx)))
    ((nodep e "DOT" 2)
     (mv-let (a cx) (cexp (second e) env cx)
       (mv (list (gsym "%GET-FIELD") a (tag-kw (third e))) cx)))
    ((nodep e "COMP" 2)
     (mv-let (a cx) (cexp (second e) env cx)
       (mv-let (b cx) (cexp (third e) env cx)
         (mv (list (gsym "%COMP") a b) cx))))
    ((nodep e "MEM" 2)
     (mv-let (a cx) (cexp (second e) env cx)
       (mv-let (b cx) (cexp (third e) env cx)
         (mv (list 'consp (list 'member-equal a b)) cx))))
    ((nodep e "LEN" 1)
     (mv-let (a cx) (cexp (second e) env cx) (mv (list 'len a) cx)))
    ((or (and (is e "TUP") (true-listp e)) (and (is e "LIST") (true-listp e)))
     (mv-let (as cx) (cexps (cdr e) env cx)
       (mv (if as (cons 'list as) nil) cx)))
    ((and (is e "CALL") (true-listp e))
     (mv-let (as cx) (cargs (cddr e) env cx)
       (mv (cons (fn-sym :def (second e) cx) as) cx)))
    ((and (is e "ITER") (true-listp e) (>= (len e) 3))
     (citer (second e) (third e) (cdddr e) env cx))
    ((nodep e "PROJ" 2)
     (if (and (nodep (second e) "UNCASE" 2) (atom-free-p (third (second e)))
              (= (length (third (second e))) 1) (eql (third e) 0))
         ;; (proj (uncase x "%") 0) on an elided newtype is x itself
         (cexp (second (second e)) env cx)
       (mv-let (a cx) (cexp (second e) env cx)
         (mv (nth-term (third e) a) cx))))
    ((nodep e "CASE" 2)
     (let* ((m (second e)) (p (third e)) (tup (and (is p "TUP") (true-listp p))))
       ;; A non-tuple payload is the single component (its case type is not a tuple).
       (mv-let (pt cx) (if tup (cexps (cdr p) env cx) (cexps (list p) env cx))
         (cond ((not (atom-free-p m)) (mv (list* 'list (tag-kw m) pt) cx))
               ((= (len pt) 1) (mv (car pt) cx))
               (t (mv (cons 'list pt) cx))))))
    ((nodep e "UNCASE" 2)
     (mv-let (a cx) (cexp (second e) env cx)
       (let ((m (third e)))
         (mv (cond ((not (atom-free-p m)) (list 'cdr a))
                   ((= (length m) 1) (list 'list a))
                   (t a))
             cx))))
    ((and (is e "OPT") (true-listp e))
     (if (consp (cdr e))
         (mv-let (a cx) (cexp (second e) env cx) (mv (list 'list a) cx))
       (mv nil cx)))
    ((nodep e "UNOPT" 1) (mv-let (a cx) (cexp (second e) env cx) (mv (list 'car a) cx)))
    ((nodep e "LIFT" 1) (cexp (second e) env cx))
    ((nodep e "CAT" 2)
     (mv-let (a cx) (cexp (second e) env cx)
       (mv-let (b cx) (cexp (third e) env cx)
         (mv (list 'append a b) cx))))
    ((nodep e "CVT" 3) (cexp (fourth e) env cx))
    ((nodep e "SUB" 3) (cexp (fourth e) env cx))
    (t (mv nil (cx-err "exp" e cx)))))

 (defun cexps (es env cx)
   (if (endp es) (mv nil cx)
     (mv-let (a cx) (cexp (car es) env cx)
       (mv-let (as cx) (cexps (cdr es) env cx)
         (mv (cons a as) cx)))))

 (defun cexpfields (fs env cx)
   (if (endp fs) (mv nil cx)
     (mv-let (v cx) (cexp (third (car fs)) env cx)
       (mv-let (rest cx) (cexpfields (cdr fs) env cx)
         (mv (cons (list 'cons (tag-kw (second (car fs))) v) rest) cx)))))

 ;; Type arguments are dropped (the encoding is untyped); exp arguments kept.
 (defun cargs (as env cx)
   (cond ((endp as) (mv nil cx))
         ((is (car as) "EXP")
          (mv-let (a cx) (cexp (second (car as)) env cx)
            (mv-let (rest cx) (cargs (cdr as) env cx)
              (mv (cons a rest) cx))))
         ((is (car as) "TYP") (cargs (cdr as) env cx))
         (t (mv nil (cx-err "higher-order argument" (car as) cx)))))

 ;; Update at PATH: K is a term over *hole* giving the new value from the old.
 (defun cpath (path k base env cx)
   (cond ((atom-is path "ROOT") (mv (hole-subst k *hole* base) cx))
         ((nodep path "DOT" 2)
          (let ((kw (tag-kw (third path))))
            (cpath (second path)
                   (list (gsym "%PUT-FIELD") *hole* kw
                         (hole-subst k *hole* (list (gsym "%GET-FIELD") *hole* kw)))
                   base env cx)))
         ((nodep path "IDX" 2)
          (mv-let (i cx) (cexp (third path) env cx)
            (cpath (second path)
                   (list 'update-nth i (hole-subst k *hole* (list 'nth i *hole*)) *hole*)
                   base env cx)))
         ((nodep path "SLICE" 3)
          (mv-let (i cx) (cexp (third path) env cx)
            (mv-let (n cx) (cexp (fourth path) env cx)
              (cpath (second path)
                     (list 'append (list 'take i *hole*)
                           (hole-subst k *hole* (list 'take n (list 'nthcdr i *hole*)))
                           (list 'nthcdr (list '+ i n) *hole*))
                     base env cx))))
         (t (mv nil (cx-err "path" path cx)))))

 ;; Iteration. x over xs (list/list1/opt) with a trivial body is just xs.
 (defun citer (body it doms env cx)
   (cond
    ((and (nodep body "VAR" 1) (= (len doms) 1)
          (equal (second body) (second (car doms)))
          (name-in it '("LIST" "LIST1" "OPT")))
     (cexp (third (car doms)) env cx))
    ((atom-is it "OPT")
     ;; (if (and d1 .. dn) (let ((x1 (car d1)) ..) (list body)) nil)
     (mv-let (ds cx) (cexps (strip-thirds doms) env cx)
       (let* ((names (dom-names doms))
              (env2 (env-add-vars names env cx)))
         (mv-let (b cx) (cexp body env2 cx)
           (mv (list 'if (cons 'and ds)
                     (build-steps (car-bind-steps names ds cx) (list 'list b))
                     nil)
               cx)))))
    ((or (name-in it '("LIST" "LIST1")) (is it "LISTN"))
     (let* ((names (dom-names doms))
            (idx (and (is it "LISTN") (stringp (third it)) (third it)))
            (counted (and (is it "LISTN") (or idx (endp doms))))
            (fvs (bound-in (set-difference-equal (fv-exp body)
                                                 (if idx (cons idx names) names))
                           env))
            (fvsyms (env-terms fvs env))
            (lsyms (gsyms-prefixed "%L" (len doms))))
       (mv-let (ds cx) (cexps (strip-thirds doms) env cx)
         (mv-let (nterm cx) (if counted (cexp (second it) env cx) (mv nil cx))
           (mv-let (aux-name cx) (cx-fresh (concatenate 'string (cx-get :fn cx) "/ITER") cx)
             (let* ((aux (gsym aux-name))
                    (env2 (env-add-vars (if idx (cons idx names) names)
                                        (env-restrict fvs env) cx)))
               (mv-let (b cx) (cexp body env2 cx)
                 (let* ((kv (gsym "%K")) (nv (gsym "%N"))
                        (binds (append (if idx (list (cons (var-sym idx cx) kv)) nil)
                                       (car-binds names lsyms cx)))
                        (rec-call (cons aux (append (if counted (list (list '+ 1 kv) nv) nil)
                                                    (cdr-terms lsyms) fvsyms)))
                        (step (build-steps (bind-steps binds) (list 'cons b rec-call)))
                        (formals (append (if counted (list kv nv) nil) lsyms fvsyms))
                        (def (if counted
                                 (mk-defun-measure
                                  aux formals (list 'nfix (list '- nv kv))
                                  (list 'if (cons 'and (append (list (list 'natp kv) (list 'natp nv)
                                                                     (list '< kv nv))
                                                               (consp-tests lsyms)))
                                        step nil))
                               (mk-defun aux formals
                                         (list 'if (cons 'or (atom-tests lsyms)) nil step)))))
                   (mv (cons aux (append (if counted (list 0 nterm) nil) ds fvsyms))
                       (cx-add-aux def cx))))))))))
    (t (mv nil (cx-err "iter" (list body it) cx)))))
 )

; --- Types: recognizer terms -------------------------------------------

(mutual-recursion
 (defun fv-typ (ty)
   (cond ((atom ty) nil)
         ((is ty "VAR") (fv-targs (cddr ty)))
         ((is ty "TUP") (fv-binds (cdr ty)))
         ((is ty "ITER") (append (fv-typ (second ty))
                                 (if (is (third ty) "LISTN") (fv-exp (second (third ty))) nil)))
         (t nil)))
 (defun fv-binds (bs)
   (if (endp bs) nil
     (append (fv-typ (third (car bs)))
             (remove-equal (second (car bs)) (fv-binds (cdr bs))))))
 (defun fv-targs (as)
   (cond ((endp as) nil)
         ((is (car as) "EXP") (append (fv-exp (second (car as))) (fv-targs (cdr as))))
         ((is (car as) "TYP") (append (fv-typ (second (car as))) (fv-targs (cdr as))))
         (t (fv-targs (cdr as))))))

(defun simple-term-p (s) (or (atom s) (gsym-p s)))

; Bind S to a fresh temp unless it is already a variable or constant.
(defun scrutinee (s cx)
  ;; (mv s' pre-steps cx)
  (if (simple-term-p s)
      (mv s nil cx)
    (mv-let (name cx) (cx-fresh "%T" cx)
      (mv (gsym name) (list (list* :bind (gsym name) s)) cx))))

(defun numtyp-test (nt s)
  (let ((n (sym-name nt)))
    (cond ((equal n "NAT") (list 'natp s))
          ((equal n "INT") (list 'integerp s))
          (t (list 'rationalp s)))))

(mutual-recursion

 (defun crec (ty x env cx)
   (cond
    ((atom-is ty "BOOL") (mv (list 'booleanp x) cx))
    ((atom-is ty "NAT") (mv (list 'natp x) cx))
    ((atom-is ty "INT") (mv (list 'integerp x) cx))
    ((atom-is ty "RAT") (mv (list 'rationalp x) cx))
    ((atom-is ty "TEXT") (mv (list 'stringp x) cx))
    ((is ty "VAR")
     (if (member-equal (second ty) (cx-get :tparams cx))
         (mv t cx)                      ; type parameters are not checked
       (mv-let (as cx) (cargs (cddr ty) env cx)
         (mv (list* (fn-sym :typ (second ty) cx) x as) cx))))
    ((is ty "TUP")
     (mv-let (x pre cx) (scrutinee x cx)
       (mv-let (steps cx) (crec-binds (cdr ty) 0 x env cx)
         (mv (build-steps (append pre
                                  (list (list :test (list 'true-listp x))
                                        (list :test (list 'equal (list 'len x) (len (cdr ty)))))
                                  steps)
                          t)
             cx))))
    ((nodep ty "ITER" 2)
     (let ((it (third ty)) (ety (second ty)))
       (cond
        ((atom-is it "OPT")
         (mv-let (x pre cx) (scrutinee x cx)
           (mv-let (c cx) (crec ety (list 'car x) env cx)
             (mv (build-steps pre (list 'or (list 'null x)
                                        (list 'and (list 'consp x) (list 'null (list 'cdr x)) c)))
                 cx))))
        (t
         (let* ((fvs (bound-in (fv-typ ety) env))
                (fvsyms (env-terms fvs env))
                (xv (gsym "%X")))
           (mv-let (c cx) (crec ety (list 'car xv) (env-restrict fvs env) cx)
             (mv-let (all cx)
               (if (equal c t)
                   (mv (list 'true-listp x) cx)
                 (mv-let (aux-name cx) (cx-fresh (concatenate 'string (cx-get :fn cx) "/ITER") cx)
                   (let ((aux (gsym aux-name)))
                     (mv (list* aux x fvsyms)
                         (cx-add-aux
                          (mk-defun aux (cons xv fvsyms)
                                    (list 'if (list 'atom xv) (list 'null xv)
                                          (list 'and c (list* aux (list 'cdr xv) fvsyms))))
                          cx)))))
               (cond ((atom-is it "LIST1") (mv (list 'and (list 'consp x) all) cx))
                     ((is it "LISTN")
                      (mv-let (n cx) (cexp (second it) env cx)
                        (mv (list 'and all (list 'equal (list 'len x) n)) cx)))
                     (t (mv all cx)))))))))) 
    (t (mv nil (cx-err "typ" ty cx)))))

 ;; tuple components: (bind name ty) at positions i.. of x
 (defun crec-binds (bs i x env cx)
   (if (endp bs) (mv nil cx)
     (let* ((name (second (car bs))) (comp (nth-term i x)))
       (if (equal name "_")
           (mv-let (c cx) (crec (third (car bs)) comp env cx)
             (mv-let (rest cx) (crec-binds (cdr bs) (1+ i) x env cx)
               (mv (cons (list :test c) rest) cx)))
         (let* ((v (var-sym name cx)) (env2 (acons name v env)))
           (mv-let (c cx) (crec (third (car bs)) v env2 cx)
             (mv-let (rest cx) (crec-binds (cdr bs) (1+ i) x env2 cx)
               (mv (list* (list* :bind v comp) (list :test c) rest) cx))))))))
 )

; Environment extended by the variables crec-binds binds.
(defun binds-env (bs env cx)
  (cond ((endp bs) env)
        ((equal (second (car bs)) "_") (binds-env (cdr bs) env cx))
        (t (binds-env (cdr bs) (acons (second (car bs)) (var-sym (second (car bs)) cx) env) cx))))

; Doms whose list expression is (not) fully bound in ENV.
(defun doms-bound (doms env want-bound)
  (cond ((endp doms) nil)
        ((eq want-bound
             (not (consp (unbound-vars (remove-duplicates-equal (fv-exp (third (car doms)))) env))))
         (cons (car doms) (doms-bound (cdr doms) env want-bound)))
        (t (doms-bound (cdr doms) env want-bound))))

; Output dom (dom x (var xs?)): bind xs? from the tuple in (car tv).
(defun opt-out-binds (outs i tv cx)
  (if (endp outs) nil
    (cons (list* :bind (var-sym (second (third (car outs))) cx)
                 (list 'if (list 'car tv) (list 'list (nth-term i (list 'car tv))) nil))
          (opt-out-binds (cdr outs) (1+ i) tv cx))))

(defun env-add-out-lists (outs env cx)
  (if (endp outs) env
    (let ((id (second (third (car outs)))))
      (env-add-out-lists (cdr outs) (acons id (var-sym id cx) env) cx))))


(defun has-unbound (e env)
  (consp (unbound-vars (remove-duplicates-equal (fv-exp e)) env)))

; Row of an iterated match: ((cons o0 (nth 0 (car r))) ...)
(defun cons-cols (otms i rv)
  (if (endp otms) nil
    (cons (list (quote cons) (car otms) (nth-term i (list (quote car) rv)))
          (cons-cols (cdr otms) (1+ i) rv))))

; Output dom (dom x (var xs)) of a list match: xs := column i of (car tv).
(defun list-out-binds (outs i tv cx)
  (if (endp outs) nil
    (cons (list* :bind (var-sym (second (third (car outs))) cx)
                 (nth-term i (list (quote car) tv)))
          (list-out-binds (cdr outs) (1+ i) tv cx))))

(defun exp-args (as)
  (cond ((endp as) nil)
        ((is (car as) "EXP") (cons (second (car as)) (exp-args (cdr as))))
        (t (exp-args (cdr as)))))

; Known length of a list pattern, as a term: [p1 .. pk] or p^n with n bound.
(defun static-len2 (p env cx)
  (cond ((is p "LIST") (mv (len (cdr p)) cx))
        ((and (is p "ITER") (true-listp p) (is (third p) "LISTN") (nodep (third p) "LISTN" 1)
              (not (has-unbound (second (third p)) env)))
         (cexp (second (third p)) env cx))
        (t (mv nil cx))))

; val* ++ (B ++ C) with val* an iteration: the shape the :redex split
; strategy (config) applies to.
(defun redex-shape-p (p)
  (and (nodep p "CAT" 2) (is (second p) "ITER") (true-listp (second p))
       (nodep (third p) "CAT" 2)))

; Length constraint of a p^n iteration pattern against s: binds n when it is
; an unbound variable, else tests |s| = n.
(defun listn-count-steps (it s env cx)
  (if (not (nodep it "LISTN" 1)) (mv nil env cx)
    (let ((n (second it)))
      (if (and (nodep n "VAR" 1) (not (assoc-equal (second n) env)))
          (mv (list (list* :bind (var-sym (second n) cx) (list (quote len) s)))
              (acons (second n) (var-sym (second n) cx) env) cx)
        (mv-let (nt cx) (cexp n env cx)
          (mv (list (list :test (list (quote equal) (list (quote len) s) nt))) env cx))))))

; --- Patterns ----------------------------------------------------------

(defun trivial-iter-dom (p)
  ;; (iter b it (dom x d)) where b is (var x), or a trivial iter yielding x: d
  (and (is p "ITER") (true-listp p) (= (len p) 4)
       (let* ((b (second p)) (dom (fourth p)) (x (second dom)))
         (and (nodep dom "DOM" 2)
              (or (and (nodep b "VAR" 1) (equal (second b) x))
                  (let ((d (trivial-iter-dom b)))
                    (and d (nodep d "VAR" 1) (equal (second d) x))))
              (third dom)))))

(defun static-len (p)
  (and (is p "LIST") (true-listp p) (len (cdr p))))

(mutual-recursion

 ;; (mv steps env cx)
 (defun cpat (p s env cx)
   (cond
    ((nodep p "VAR" 1)
     (let* ((id (second p)) (b (assoc-equal id env)))
       (cond ((equal id "_") (mv nil env cx))
             (b (mv (list (list :test (list 'equal s (cdr b)))) env cx))
             (t (let ((v (var-sym id cx)))
                  (mv (list (list* :bind v s)) (acons id v env) cx))))))
    ((or (nodep p "NUM" 1) (nodep p "BOOL" 1) (nodep p "TEXT" 1))
     (mv-let (lit cx) (cexp p env cx)
       (mv (list (list :test (list 'equal s lit))) env cx)))
    ((nodep p "SUB" 3)
     (mv-let (s pre cx) (scrutinee s cx)
       (mv-let (c cx) (crec (second p) s env cx)
         (mv-let (steps env cx) (cpat (fourth p) s env cx)
           (mv (append pre (list (list :test c)) steps) env cx)))))
    ((nodep p "CVT" 3)
     (mv-let (s pre cx) (scrutinee s cx)
       (mv-let (steps env cx) (cpat (fourth p) s env cx)
         (mv (append pre (list (list :test (numtyp-test (second p) s))) steps) env cx))))
    ((nodep p "CASE" 2)
     (let* ((m (second p)) (q (third p)) (tup (and (is q "TUP") (true-listp q))))
       (mv-let (s pre cx) (scrutinee s cx)
         (cond
          ;; non-tuple payload pattern = the single component
          ((not (atom-free-p m))
           (mv-let (steps env cx)
             (cpat-seq (if tup (cdr q) (list q)) (list 'cdr s) env cx)
             (mv (append pre (list (list :test (list 'consp s))
                                   (list :test (list 'eq (list 'car s) (tag-kw m))))
                         steps)
                 env cx)))
          ((not tup)
           (mv-let (steps env cx) (cpat q s env cx) (mv (append pre steps) env cx)))
          ((= (len (cdr q)) 1)
           (mv-let (steps env cx) (cpat (second q) s env cx) (mv (append pre steps) env cx)))
          (t (mv-let (steps env cx) (cpat-seq (cdr q) s env cx)
               (mv (append pre steps) env cx)))))))
    ((or (and (is p "TUP") (true-listp p)) (and (is p "LIST") (true-listp p)))
     (mv-let (s pre cx) (scrutinee s cx)
       (mv-let (steps env cx) (cpat-seq (cdr p) s env cx)
         (mv (append pre steps) env cx))))
    ((and (is p "STRUCT") (true-listp p))
     ;; {A pa, B pb, ...}: a record with exactly these fields, in order
     (mv-let (s pre cx) (scrutinee s cx)
       (mv-let (steps env cx) (cpat-fields (cdr p) 0 (list 'cdr s) env cx)
         (mv (append pre
                     (list (list :test (list 'consp s))
                           (list :test (list 'eq (list 'car s) :%rec))
                           (list :test (list 'true-listp (list 'cdr s)))
                           (list :test (list 'equal (list 'len (list 'cdr s)) (len (cdr p)))))
                     steps)
             env cx))))
    ((and (is p "OPT") (true-listp p))
     (if (consp (cdr p))
         (mv-let (s pre cx) (scrutinee s cx)
           (mv-let (steps env cx) (cpat (second p) (list 'car s) env cx)
             (mv (append pre (list (list :test (list 'consp s))) steps) env cx)))
       (mv (list (list :test (list 'null s))) env cx)))
    ((nodep p "CAT" 2)
     (mv-let (ka cx) (static-len2 (second p) env cx)
       (mv-let (kb cx) (static-len2 (third p) env cx)
         (mv-let (s pre cx) (scrutinee s cx)
           (cond
            ((and (cx-get :redex cx) (redex-shape-p p))
             (cpat-redex p s pre env (cx-put :redex nil cx)))
            ((eql ka 1)
             (mv-let (s1 env cx) (cpat (second (second p)) (list 'car s) env cx)
               (mv-let (s2 env cx) (cpat (third p) (list 'cdr s) env cx)
                 (mv (append pre (list (list :test (list 'consp s))) s1 s2) env cx))))
            (ka
             (mv-let (s1 env cx) (cpat (second p) (list 'take ka s) env cx)
               (mv-let (s2 env cx) (cpat (third p) (list 'nthcdr ka s) env cx)
                 (mv (append pre (list (list :test (list 'true-listp s))
                                       (list :test (list '<= ka (list 'len s))))
                             s1 s2)
                     env cx))))
            (kb
             (let ((n (list '- (list 'len s) kb)))
               (mv-let (s1 env cx) (cpat (second p) (list 'take n s) env cx)
                 (mv-let (s2 env cx) (cpat (third p) (list 'nthcdr n s) env cx)
                   (mv (append pre (list (list :test (list 'true-listp s))
                                         (list :test (list '<= kb (list 'len s))))
                               s1 s2)
                       env cx)))))
            (t
             ;; Neither side has a known length: search the split point
             ;; (plan §2.5). Everything after this step runs inside the
             ;; search, so a later failure tries the next split.
             (mv-let (kname cx) (cx-fresh "%T" cx)
               (let ((kv (gsym kname)))
                 (mv-let (s1 env cx) (cpat (second p) (list 'take kv s) env cx)
                   (mv-let (s2 env cx) (cpat (third p) (list 'nthcdr kv s) env cx)
                     (mv (append pre (list (list :test (list 'true-listp s))
                                           (list :choose kv 0 (list 'len s) nil))
                                 s1 s2)
                         env cx)))))))))))
    ((and (nodep p "PROJ" 2) (eql (third p) 0) (nodep (second p) "UNCASE" 2)
          (atom-free-p (third (second p))) (= (length (third (second p))) 1))
     ;; x!%.0 on an elided newtype is x itself
     (cpat (second (second p)) s env cx))
    ((and (nodep p "BIN" 4) (name-in (second p) '("ADD" "SUB" "MUL"))
          (name-in (third p) '("NAT" "INT" "RAT"))
          (has-unbound p env)
          (not (and (has-unbound (fourth p) env) (has-unbound (fifth p) env))))
     ;; linear arithmetic pattern: solve  a op b = s  for the unbound side
     (let* ((op (sym-name (second p))) (ty (third p))
            (left-unbound (has-unbound (fourth p) env))
            (q (if left-unbound (fourth p) (fifth p)))
            (c (if left-unbound (fifth p) (fourth p))))
       (mv-let (s pre cx) (scrutinee s cx)
         (mv-let (ct cx) (cexp c env cx)
           (let ((v (cond ((equal op "ADD") (list '- s ct))
                          ((equal op "MUL") (list '/ s ct))
                          (left-unbound (list '+ s ct))     ; q - c = s
                          (t (list '- ct s)))))            ; c - q = s
             (mv-let (s1 env cx) (cpat q v env cx)
               (mv (append pre
                           (if (equal op "MUL") (list (list :test (list 'not (list 'equal ct 0)))) nil)
                           (list (list :test (numtyp-test ty v)))
                           s1)
                   env cx)))))))
    ((and (is p "CALL") (true-listp p) (has-unbound p env)
          (assoc-equal (second p) (cx-get :inverses cx)))
     ;; f(a.., x) = s with x unbound: x := f^-1(a.., s), then check f(a.., x) = s
     ;; (inverse pairs come from SpecTec hint(inverse), via the config)
     (let* ((args (exp-args (cddr p)))
            (g (cdr (assoc-equal (second p) (cx-get :inverses cx)))))
       (mv-let (s pre cx) (scrutinee s cx)
         (mv-let (others cx) (cexps (butlast args 1) env cx)
           (mv-let (tname cx) (cx-fresh "%T" cx)
             (let ((tv (gsym tname)))
               (mv-let (s1 env cx) (cpat (car (last args)) tv env cx)
                 (mv-let (chk cx) (cexp p env cx)
                   (mv (append pre
                               (list (list* :bind tv (cons (fn-sym :def g cx) (append others (list s)))))
                               s1
                               (list (list :test (list 'equal chk s))))
                       env cx)))))))))
    ((trivial-iter-dom p)
     (let ((d (trivial-iter-dom p)) (it (third p)))
       (mv-let (s pre cx) (scrutinee s cx)
         (cond
          ((atom-is it "OPT")
           (mv-let (steps env cx) (cpat d s env cx)
             (mv (append pre (list (list :test (list 'or (list 'null s)
                                                     (list 'and (list 'consp s)
                                                           (list 'null (list 'cdr s))))))
                         steps)
                 env cx)))
          ((is it "LISTN")
           (let ((n (second it)))
             (if (and (nodep n "VAR" 1) (not (assoc-equal (second n) env)))
                 (mv-let (s1 env cx) (cpat n (list 'len s) env cx)
                   (mv-let (s2 env cx) (cpat d s env cx)
                     (mv (append pre (list (list :test (list 'true-listp s))) s1 s2) env cx)))
               (mv-let (nt cx) (cexp n env cx)
                 (mv-let (s2 env cx) (cpat d s env cx)
                   (mv (append pre (list (list :test (list 'true-listp s))
                                         (list :test (list 'equal (list 'len s) nt)))
                               s2)
                       env cx))))))
          (t
           (mv-let (steps env cx) (cpat d s env cx)
             (mv (append pre
                         (list (list :test (list 'true-listp s)))
                         (if (atom-is it "LIST1") (list (list :test (list 'consp s))) nil)
                         steps)
                 env cx)))))))
    ((and (is p "ITER") (true-listp p) (>= (len p) 4)
          (or (name-in (third p) '("LIST" "LIST1" "OPT")) (nodep (third p) "LISTN" 1))
          (has-unbound p env))
     (citer-pat (second p) (third p) (cdddr p) s env cx))
    ((null (unbound-vars (remove-duplicates-equal (fv-exp p)) env))
     ;; a fully determined expression: compare
     (mv-let (v cx) (cexp p env cx)
       (mv (list (list :test (list 'equal s v))) env cx)))
    (t (mv nil env (cx-err "pattern" p cx)))))

 ;; fixed-length sequence of patterns against list s
 (defun cpat-seq (ps s env cx)
   (mv-let (steps env cx) (cpat-elems ps 0 s env cx)
     (mv (list* (list :test (list 'true-listp s))
                (list :test (list 'equal (list 'len s) (len ps)))
                steps)
         env cx)))

 ;; General iteration pattern  P*{x <- xs, ...} / P?{...} against s: match
 ;; every element against P; doms whose list is unbound are outputs,
 ;; collected per element. Bound doms are iterated in lockstep with s.
 (defun citer-pat (body it doms s env cx)
   (let* ((ins (doms-bound doms env t)) (outs (doms-bound doms env nil))
          (in-names (dom-names ins)) (out-names (dom-names outs)))
     (mv-let (s pre cx) (scrutinee s cx)
       (mv-let (ds cx) (cexps (strip-thirds ins) env cx)
         (mv-let (tname cx) (cx-fresh "%T" cx)
           (let ((tv (gsym tname)))
             (if (atom-is it "OPT")
                 (mv-let (psteps env3 cx)
                   (cpat body (list 'car s) (env-add-vars in-names env cx) cx)
                   (let ((otms (env-terms out-names env3)))
                     (mv (append pre
                                 (list (list :test (list 'or (list 'null s)
                                                         (list 'and (list 'consp s)
                                                               (list 'null (list 'cdr s)))))
                                       (list* :bind tv
                                              (list 'if s
                                                    (build-steps (append (car-bind-steps in-names ds cx)
                                                                         psteps)
                                                                 (list 'list (cons 'list otms)))
                                                    (list 'list nil)))
                                       (list :test tv))
                                 (opt-out-binds outs 0 tv cx))
                         (env-add-out-lists outs env cx) cx)))
               (let* ((fvs (bound-in (set-difference-equal (fv-exp body) (append in-names out-names))
                                     env))
                      (fvsyms (env-terms fvs env))
                      (sv (gsym "%S")) (rv (gsym "%R"))
                      (lsyms (gsyms-prefixed "%L" (len ins))))
                 (mv-let (aux-name cx) (cx-fresh (concatenate 'string (cx-get :fn cx) "/MATCH") cx)
                   (let* ((aux (gsym aux-name))
                          (rec-call (list* aux (list 'cdr sv) (append (cdr-terms lsyms) fvsyms))))
                     (mv-let (psteps env3 cx)
                       (cpat body (list 'car sv)
                             (env-add-vars in-names (env-restrict fvs env) cx) cx)
                       (let* ((otms (env-terms out-names env3))
                              (row (cons 'list (cons-cols otms 0 rv)))
                              (def (mk-defun aux (append (list sv) lsyms fvsyms)
                                             (list 'if (list 'atom sv)
                                                   (list 'if (list 'null sv)
                                                         (list 'list (cons 'list (make-list (len outs))))
                                                         nil)
                                                   (list 'let (list (list rv rec-call))
                                                         (ignorable-decl (list rv))
                                                         (list 'and rv
                                                               (build-steps
                                                                (append (bind-steps (car-binds in-names lsyms cx))
                                                                        psteps)
                                                                (list 'list row))))))))
                         (mv-let (csteps env2 cx2)
                           (listn-count-steps it s (env-add-out-lists outs env cx) (cx-add-aux def cx))
                           (mv (append pre
                                       (list (list :test (list 'true-listp s)))
                                       (if (atom-is it "LIST1") (list (list :test (list 'consp s))) nil)
                                       (list (list* :bind tv (list* aux s (append ds fvsyms)))
                                             (list :test tv))
                                       (list-out-binds outs 0 tv cx)
                                       csteps)
                               env2 cx2))))))))))))))

 ;; Config split strategy :redex for  A* ++ B ++ C  (Step/ctxt-instrs):
 ;; p = length of the longest prefix of s whose elements match A's element
 ;; pattern; B must end at position p (the first element that is not an A),
 ;; and A's length is searched from p down to 0. Plan §2.5; completeness
 ;; w.r.t. the generic search is a T8 proof obligation.
 (defun cpat-redex (p s pre env cx)
   (let* ((a (second p)) (b (second (third p))) (c (third (third p)))
          (sv (gsym "%S")))
     (mv-let (fname cx) (cx-fresh (concatenate 'string (cx-get :fn cx) "/PREFIX") cx)
       (mv-let (msteps env0 cx) (cpat (second a) (list 'car sv) nil cx)
         (declare (ignore env0))
         (let* ((f (gsym fname))
                (def (mk-defun f (list sv)
                               (list 'if (list 'atom sv) 0
                                     (list 'if (build-steps msteps t)
                                           (list '+ 1 (list f (list 'cdr sv)))
                                           0)))))
           (mv-let (pname cx) (cx-fresh "%T" cx)
             (mv-let (kname cx) (cx-fresh "%T" cx)
               (let* ((pv (gsym pname)) (kv (gsym kname)) (cx (cx-add-aux def cx)))
                 (mv-let (s1 env cx) (cpat a (list 'take kv s) env cx)
                   (mv-let (s2 env cx) (cpat b (list 'take (list '- (list '+ 1 pv) kv)
                                                     (list 'nthcdr kv s))
                                             env cx)
                     (mv-let (s3 env cx) (cpat c (list 'nthcdr (list '+ 1 pv) s) env cx)
                       (mv (append pre
                                   (list (list :test (list 'true-listp s))
                                         (list* :bind pv (list f s))
                                         (list :test (list '< pv (list 'len s)))
                                         (list :choose kv 0 pv t))
                                   s1 s2 s3)
                           env cx))))))))))))

 (defun cpat-fields (fs i r env cx)
   (if (endp fs) (mv nil env cx)
     (let ((cell (nth-term i r)))
       (mv-let (s1 env cx) (cpat (third (car fs)) (list 'cdr cell) env cx)
         (mv-let (s2 env cx) (cpat-fields (cdr fs) (1+ i) r env cx)
           (mv (append (list (list :test (list 'consp cell))
                             (list :test (list 'eq (list 'car cell) (tag-kw (second (car fs))))))
                       s1 s2)
               env cx))))))

 (defun cpat-elems (ps i s env cx)
   (if (endp ps) (mv nil env cx)
     (mv-let (s1 env cx) (cpat (car ps) (nth-term i s) env cx)
       (mv-let (s2 env cx) (cpat-elems (cdr ps) (1+ i) s env cx)
         (mv (append s1 s2) env cx)))))
 )

; --- Premises ----------------------------------------------------------


; Free variables of a premise.
(defun fv-prem (pr)
  (cond ((atom pr) nil)
        ((is pr "IF") (fv-exp (second pr)))
        ((is pr "LET") (append (fv-exp (second pr)) (fv-exp (third pr))))
        ((is pr "ITER") (append (set-difference-equal (fv-prem (second pr)) (dom-names (cdddr pr)))
                                (fv-doms (cdddr pr))))
        ((is pr "RULE") (fv-list (cddr pr)))
        (t nil)))

;; a relation premise, possibly iterated
(defun crule-premise (pr env cx)
  (let* ((rel (second pr)) (rest (cddr pr)) (n (len rest))
         (e (nth (- n 1) rest))
         (comps (if (and (is e "TUP") (true-listp e)) (cdr e) (list e)))
         (mode (cdr (assoc-equal rel (cx-get :modes cx))))
         (fn (fn-sym :rel rel cx)))
    (cond
     ((null mode) (mv nil env (cx-err "relation not available" rel cx)))
     ((eq (car mode) :fun)
      (let ((ins (butlast comps 1)) (out (car (last comps))))
        (if (has-unbound (cons (quote list) ins) env)
            (mv nil env (cx-err "relation inputs unbound" pr cx))
          (mv-let (ts cx) (cexps ins env cx)
            (mv-let (tname cx) (cx-fresh "%T" cx)
              (let ((tv (gsym tname)))
                (mv-let (s1 env cx) (cpat out (list (quote car) tv) env cx)
                  (mv (append (list (list* :bind tv (cons fn ts)) (list :test tv)) s1)
                      env cx))))))))
     (t
      (if (has-unbound (cons (quote list) comps) env)
          (mv nil env (cx-err "checker relation with unbound arguments" pr cx))
        (mv-let (ts cx) (cexps comps env cx)
          (mv (list (list :test (cons fn ts))) env cx)))))))

; ((sym . (nth i (car tv))) ...)
(defun nth-binds (syms i tv)
  (if (endp syms) nil
    (cons (cons (car syms) (nth-term i (list (quote car) tv))) (nth-binds (cdr syms) (1+ i) tv))))

(defun rule-prem-p (p)
  (or (is p "RULE") (and (is p "ITER") (rule-prem-p (second p)))))

(mutual-recursion
(defun cprem (pr env cx)
  ;; (mv steps env cx)
  (cond
   ((atom-is pr "ELSE") (mv nil env cx))
   ((and (nodep pr "IF" 1) (nodep (second pr) "BIN" 4) (atom-is (second (second pr)) "AND"))
    ;; if a /\ b  ==  if a; if b  (lets either conjunct bind, plan §2.5)
    (cprems (list (list (quote if) (fourth (second pr))) (list (quote if) (fifth (second pr))))
            env cx))
   ((nodep pr "IF" 1)
    (let ((e (second pr)))
      (cond
       ((and (nodep e "BIN" 4) (atom-is (second e) "OR") (has-unbound e env))
        ;; a \/ b binding variables: the first disjunct that holds binds them
        ;; (both disjuncts must bind the same variables)
        (mv-let (s1 e1 cx) (cprem (list 'if (fourth e)) env cx)
          (mv-let (s2 e2 cx) (cprem (list 'if (fifth e)) env cx)
            (let* ((new1 (set-difference-equal (remove-duplicates-equal (strip-cars e1)) (strip-cars env)))
                   (new2 (set-difference-equal (remove-duplicates-equal (strip-cars e2)) (strip-cars env)))
                   (syms (env-terms new1 e1)))
              (if (not (and (subsetp-equal new1 new2) (subsetp-equal new2 new1)))
                  (mv nil env (cx-err "disjuncts bind different variables" e cx))
                (mv-let (tname cx) (cx-fresh "%T" cx)
                  (let ((tv (gsym tname)))
                    (mv (append (list (list* :bind tv (list 'or (build-steps s1 (list 'list (cons 'list syms)))
                                                          (build-steps s2 (list 'list (cons 'list syms)))))
                                      (list :test tv))
                                (bind-steps (nth-binds syms 0 tv)))
                        (append (env-restrict new1 e1) env) cx))))))))
       ((and (nodep e "MEM" 2) (has-unbound (second e) env) (not (has-unbound (third e) env)))
        ;; x <- e with x unbound: choose the first element (deterministic)
        (mv-let (v cx) (cexp (third e) env cx)
          (mv-let (tname cx) (cx-fresh "%T" cx)
            (let ((tv (gsym tname)))
              (mv-let (s1 env cx) (cpat (second e) (list (quote car) tv) env cx)
                (mv (append (list (list* :bind tv v) (list :test (list (quote consp) tv))) s1)
                    env cx))))))
       ((and (nodep e "CMP" 4) (atom-is (second e) "EQ")
             (has-unbound (fourth e) env) (not (has-unbound (fifth e) env)))
        ;; x = e with x unbound: a binding (mode analysis, plan §2.5)
        (mv-let (v cx) (cexp (fifth e) env cx) (cpat (fourth e) v env cx)))
       ((and (nodep e "CMP" 4) (atom-is (second e) "EQ")
             (has-unbound (fifth e) env) (not (has-unbound (fourth e) env)))
        (mv-let (v cx) (cexp (fourth e) env cx) (cpat (fifth e) v env cx)))
       ((has-unbound e env)
        (mv nil env (cx-err "condition with unbound variables" e cx)))
       (t (mv-let (c cx) (cexp e env cx) (mv (list (list :test c)) env cx))))))
   ((nodep pr "LET" 2)
    (mv-let (v cx) (cexp (third pr) env cx) (cpat (second pr) v env cx)))
   ((and (is pr "ITER") (true-listp pr) (>= (len pr) 4))
    ;; prem*{x <- xs, ...} / prem?{...}. Doms whose list is unbound are
    ;; outputs; they are only supported for ? iteration, where each output is
    ;; bound by the inner premise (mode analysis, plan §2.5).
    (let* ((inner (second pr)) (it (third pr)) (doms (cdddr pr))
           (ins (doms-bound doms env t)) (outs (doms-bound doms env nil))
           (in-names (dom-names ins)))
      (cond
       ((endp ins) (mv nil env (cx-err "iterated premise without inputs" pr cx)))
       ((atom-is it "OPT")
        (mv-let (ds cx) (cexps (strip-thirds ins) env cx)
          (mv-let (isteps env3 cx) (cprem inner (env-add-vars in-names env cx) cx)
            (let* ((pre (car-bind-steps in-names ds cx))
                   (some (cons 'and ds)))
              (if (endp outs)
                  (mv (list (list :test (list 'or (list 'not some)
                                              (build-steps (append pre isteps) t))))
                      env cx)
                (let ((otms (env-terms (dom-names outs) env3)))
                  (if (member-equal nil otms)
                      (mv nil env (cx-err "iterated premise output not bound" pr cx))
                    (mv-let (tname cx) (cx-fresh "%T" cx)
                      (let ((tv (gsym tname)))
                        (mv (append (list (list* :bind tv
                                                 (list 'if some
                                                       (build-steps (append pre isteps)
                                                                    (list 'list (cons 'list otms)))
                                                       (list 'list nil)))
                                          (list :test tv))
                                    (opt-out-binds outs 0 tv cx))
                            (env-add-out-lists outs env cx)
                            cx))))))))))
       ((consp outs) (mv nil env (cx-err "iterated premise with output lists" pr cx)))
       (t
        (let* ((fvs (bound-in (set-difference-equal (fv-prem inner) in-names) env))
               (fvsyms (env-terms fvs env))
               (lsyms (gsyms-prefixed "%L" (len ins))))
          (mv-let (ds cx) (cexps (strip-thirds ins) env cx)
            (mv-let (isteps env3 cx)
              (cprem inner (env-add-vars in-names (env-restrict fvs env) cx) cx)
              (declare (ignore env3))
              (mv-let (aux-name cx) (cx-fresh (concatenate 'string (cx-get :fn cx) "/ALL") cx)
                (let* ((aux (gsym aux-name))
                       (rec-call (cons aux (append (cdr-terms lsyms) fvsyms)))
                       (def (mk-defun aux (append lsyms fvsyms)
                                      (list 'if (cons 'or (atom-tests lsyms)) t
                                            (build-steps (append (bind-steps (car-binds in-names lsyms cx))
                                                                 isteps)
                                                         rec-call)))))
                  (mv (list (list :test (cons aux (append ds fvsyms))))
                      env (cx-add-aux def cx)))))))))))
   ((and (is pr "RULE") (true-listp pr) (>= (len pr) 4))
    (crule-premise pr env cx))
   (t (mv nil env (cx-err "premise" pr cx)))))

;; Premises are not in dependency order in SpecTec. Schedule them: always
;; compile the first premise that compiles without errors under the current
;; bindings (deterministic; falls back to the first premise, reporting its
;; errors, when none is ready).
(defun cprems (prs env cx)
  (if (endp prs) (mv nil env cx)
    (let* ((k (or (first-ready prs 0 env cx nil) (first-ready prs 0 env cx t) 0))
           (p (nth k prs))
           (rest (append (take k prs) (nthcdr (1+ k) prs))))
      (mv-let (s1 env cx) (cprem p env cx)
        (mv-let (s2 env cx) (cprems rest env cx)
          (mv (append s1 s2) env cx))))))

;; index of the first premise that compiles cleanly; relation premises
;; (expensive calls) only when ALLOW-RULES, so cheap tests run first
(defun first-ready (prs i env cx allow-rules)
  (cond ((endp prs) nil)
        ((and (not allow-rules) (rule-prem-p (car prs)))
         (first-ready (cdr prs) (1+ i) env cx allow-rules))
        (t (mv-let (s e2 cx2) (cprem (car prs) env cx)
             (declare (ignore s e2))
             (if (equal (len (cx-get :errs cx2)) (len (cx-get :errs cx)))
                 i
               (first-ready (cdr prs) (1+ i) env cx allow-rules))))))

)

; --- Recognizers for syntax definitions --------------------------------

(defun exp-params (ps)
  (cond ((endp ps) nil)
        ((is (car ps) "EXP") (cons (car ps) (exp-params (cdr ps))))
        (t (exp-params (cdr ps)))))

(defun typ-param-names (ps)
  (cond ((endp ps) nil)
        ((is (car ps) "TYP") (cons (second (car ps)) (typ-param-names (cdr ps))))
        (t (typ-param-names (cdr ps)))))

(defun cpat-args (pats formals env cx)
  ;; match each arg pattern against its formal
  (if (or (endp pats) (endp formals)) (mv nil env cx)
    (mv-let (s1 env cx) (cpat (car pats) (car formals) env cx)
      (mv-let (s2 env cx) (cpat-args (cdr pats) (cdr formals) env cx)
        (mv (append s1 s2) env cx)))))

(defun crec-fields (fs i r cx)
  ;; record fields (field atom ty params... prems...) at positions i.. of alist r
  (if (endp fs) (mv nil cx)
    (let* ((f (car fs)) (cell (nth-term i r)))
      (mv-let (c cx) (crec (third f) (list 'cdr cell) nil cx)
        (mv-let (rest cx) (crec-fields (cdr fs) (1+ i) r cx)
          (mv (list* (list :test (list 'consp cell))
                     (list :test (list 'eq (list 'car cell) (tag-kw (second f))))
                     (list :test c)
                     rest)
              (if (consp (cdddr f)) (cx-err "record field premises" f cx) cx)))))))

(defun case-prems (c)
  ;; (case m ty params... prems...) -> prems
  (let* ((rest (cdddr c)) (ps (take-while-params rest)))
    (nthcdr (len ps) rest)))

(defun crec-case (c x env cx)
  ;; A non-tuple case type is a single anonymous component.
  (let* ((m (second c)) (ty (third c))
         (bs (if (and (is ty "TUP") (true-listp ty)) (cdr ty) (list (list (quote bind) "_" ty)))))
    (progn$
      (let* ((k (len bs)))
        (mv-let (pre p cx)
          (cond ((not (atom-free-p m))
                 (mv (list (list :test (list 'consp x))
                           (list :test (list 'eq (list 'car x) (tag-kw m))))
                     (list 'cdr x) cx))
                (t (mv nil x cx)))
          (mv-let (bsteps cx)
            (if (and (atom-free-p m) (= k 1))
                ;; elided newtype: the value is the single component
                (let ((name (second (car bs))))
                  (if (equal name "_")
                      (mv-let (c cx) (crec (third (car bs)) x env cx)
                        (mv (list (list :test c)) cx))
                    (mv-let (c cx) (crec (third (car bs)) (var-sym name cx)
                                         (acons name (var-sym name cx) env) cx)
                      (mv (list (list* :bind (var-sym name cx) x) (list :test c)) cx))))
              (mv-let (steps cx) (crec-binds bs 0 p env cx)
                (mv (list* (list :test (list 'true-listp p))
                           (list :test (list 'equal (list 'len p) k))
                           steps)
                    cx)))
            (mv-let (psteps env2 cx) (cprems (case-prems c) (binds-env bs env cx) cx)
              (declare (ignore env2))
              (mv (build-steps (append pre bsteps psteps) t) cx))))))))

(defun crec-cases (cs x env cx)
  (if (endp cs) (mv nil cx)
    (mv-let (a cx) (crec-case (car cs) x env cx)
      (mv-let (rest cx) (crec-cases (cdr cs) x env cx)
        (mv (cons a rest) cx)))))

(defun any-atom-free-case (cs)
  (and (consp cs) (or (atom-free-p (second (car cs))) (any-atom-free-case (cdr cs)))))

(defun crec-deftyp (dt x env cx)
  (cond
   ((nodep dt "ALIAS" 1) (crec (second dt) x env cx))
   ((is dt "STRUCT")
    (let ((r (list 'cdr x)) (n (len (cdr dt))))
      (mv-let (steps cx) (crec-fields (cdr dt) 0 r cx)
        (mv (build-steps (append (list (list :test (list 'consp x))
                                       (list :test (list 'eq (list 'car x) :%rec))
                                       (list :test (list 'true-listp r))
                                       (list :test (list 'equal (list 'len r) n)))
                                 steps)
                         t)
            cx))))
   ((is dt "VARIANT")
    (let ((cs (cdr dt)))
      (if (and (any-atom-free-case cs) (consp (cdr cs)))
          (mv nil (cx-err "atom-free case in a multi-case variant (cannot elide)" dt cx))
        (mv-let (terms cx) (crec-cases cs x env cx)
          (mv (if (consp (cdr terms)) (cons 'or terms) (car terms)) cx)))))
   (t (mv nil (cx-err "deftyp" dt cx)))))

(defun inst-parts (inst)
  ;; (inst params... args... deftyp) -> (mv args deftyp)
  (let* ((rest (cdr inst)) (ps (take-while-params rest))
         (rest (nthcdr (len ps) rest)) (as (take-while-args rest)))
    (mv as (car (nthcdr (len as) rest)))))

(defun crec-insts (insts formals x cx)
  (if (endp insts) (mv nil cx)
    (mv-let (as dt) (inst-parts (car insts))
      (mv-let (steps env cx) (cpat-args (exp-args as) formals nil cx)
        (mv-let (term cx) (crec-deftyp dt x env cx)
          (mv-let (rest cx) (crec-insts (cdr insts) formals x cx)
            (mv (cons (build-steps steps term) rest) cx)))))))

(defun def-parts (x)
  ;; (KIND id params... more...) -> (mv params more)
  (let* ((rest (cddr x)) (ps (take-while-params rest)))
    (mv ps (nthcdr (len ps) rest))))

; (mv defun cx) for a syntax definition
(defun ctyp (x cx)
  (mv-let (ps insts) (def-parts x)
    (let* ((formals (gsyms-prefixed "%A" (len (exp-params ps))))
           (xv (gsym "%X"))
           (cx (cx-put :tparams (typ-param-names ps) cx)))
      (mv-let (terms cx) (crec-insts insts formals xv cx)
        (mv (mk-defun (fn-sym :typ (second x) cx) (cons xv formals)
                      (if (consp (cdr terms)) (cons 'or terms) (car terms)))
            cx)))))

; --- Function definitions ----------------------------------------------

(defun clause-parts (cl)
  ;; (clause params... args... exp prems...) -> (mv args exp prems)
  (let* ((rest (cdr cl)) (ps (take-while-params rest))
         (rest (nthcdr (len ps) rest)) (as (take-while-args rest))
         (more (nthcdr (len as) rest)))
    (mv as (car more) (cdr more))))

(defun cclause (cl formals cx)
  ;; (mv term cx): (list result) if the clause applies, nil otherwise
  (mv-let (as e prs) (clause-parts cl)
    (mv-let (s1 env cx) (cpat-args (exp-args as) formals nil cx)
      (mv-let (s2 env cx) (cprems prs env cx)
        (mv-let (r cx) (cexp e env cx)
          (build-steps-cx (append s1 s2) (list 'list r) cx))))))

(defun cclauses (cls formals cx)
  (if (endp cls) (mv nil cx)
    (mv-let (c cx) (cclause (car cls) formals cx)
      (if (and (consp c) (eq (car c) 'list) (= (len c) 2))
          (mv (second c) cx)          ; unconditional clause: later ones unreachable
        (mv-let (rest cx) (cclauses (cdr cls) formals cx)
          (let ((r (gsym "%R")))
            (mv (list 'let (list (list r c)) (ignorable-decl (list r))
                      (list 'if r (list 'car r) rest))
                cx)))))))

; (mv defun-or-nil builtin cx). Builtins (no clauses) are not emitted;
; BUILTIN is then (name-string . arity).
(defun cdef (x cx)
  (mv-let (ps more) (def-parts x)
    (let* ((arity (len (exp-params ps)))
           (formals (gsyms-prefixed "%A" arity))
           (name (fn-sym :def (second x) cx))
           (cls (cdr more)))
      (if (endp cls)
          (mv nil (cons (cdr name) arity) cx)
        (mv-let (body cx) (cclauses cls formals cx)
          (mv (mk-defun name formals body) nil cx))))))

; Body of a definition that could not be translated (listed in the header).
(defun stub-defun (name formals)
  (mk-defun name formals
            (list (quote prog2$)
                  (list (quote er) (quote acl2::hard?) (list (quote quote) name)
                        "Not translated (see the stub list in the file header).")
                  nil)))

; --- Relations (plan §2.5) ----------------------------------------------
;
; Mode :fun   R(inputs) = (list output) for the first rule that applies, or
;             nil; the last component is the output.
; Mode :check R(all components) = t iff some rule applies.
; Mode :closure  refl/trans shape: R(x) = (list y), y the normal form of
;             iterating the step relation from x (bounded by (%FUEL)).

(defun rel-parts (x)
  ;; (rel id params... mixop typ rules...) -> (mv arity rules)
  (mv-let (ps more) (def-parts x)
    (declare (ignore ps))
    (let ((ty (second more)))
      (mv (if (and (is ty "TUP") (true-listp ty)) (len (cdr ty)) 1)
          (cddr more)))))

(defun rule-parts (r)
  ;; (rule id params... mixop exp prems...) -> (mv comps prems)
  (let* ((rest (cddr r)) (ps (take-while-params rest)) (more (nthcdr (len ps) rest))
         (e (second more)))
    (mv (if (and (is e "TUP") (true-listp e)) (cdr e) (list e)) (cddr more))))

; refl/trans closure of a step relation: (mv step-rel-id-or-nil)
(defun closure-step (x)
  (mv-let (n rules) (rel-parts x)
    (and (= n 2) (= (len rules) 2)
         (mv-let (c1 p1) (rule-parts (first rules))
           (mv-let (c2 p2) (rule-parts (second rules))
             (declare (ignore c2))
             (and (null p1) (equal (first c1) (second c1))
                  (= (len p2) 2)
                  (is (first p2) "RULE") (is (second p2) "RULE")
                  (equal (second (second p2)) (second x))
                  (second (first p2))))))))

(defun crule (r mode formals rel cx)
  ;; (mv term cx): (list output) / (list t) if rule R applies, else nil
  (mv-let (comps prems) (rule-parts r)
    (let* ((ins (if (eq mode :fun) (butlast comps 1) comps))
           (cx (cx-put :redex (and (member-equal (cons rel (second r)) (cx-get :split-rules cx)) t) cx)))
      (mv-let (s1 env cx) (cpat-args ins formals nil cx)
        (let ((cx (cx-put :redex nil cx)))
          (mv-let (s2 env cx) (cprems prems env cx)
            (mv-let (out cx) (if (eq mode :fun) (cexp (car (last comps)) env cx) (mv t cx))
              (build-steps-cx (append s1 s2) (list 'list out) cx))))))))

(defun crules (rs mode formals rel cx)
  (if (endp rs) (mv nil cx)
    (mv-let (c cx) (crule (car rs) mode formals rel cx)
      (mv-let (rest cx) (crules (cdr rs) mode formals rel cx)
        (mv (cons c rest) cx)))))

(defun chain-results (cs)
  ;; first non-nil of the rule results, still wrapped: (list output) or nil,
  ;; so that an empty output (e.g. NOP ~> eps) is distinguishable from failure
  (if (endp cs) nil
    (if (and (consp (car cs)) (eq (car (car cs)) 'list) (= (len (car cs)) 2))
        (car cs)                         ; unconditional rule
      (let ((r (gsym "%R")))
        (list 'let (list (list r (car cs))) (ignorable-decl (list r))
              (list 'if r r (chain-results (cdr cs))))))))

; (mv defuns cx) for one relation in the given mode
(defun crel (x mode cx)
  (mv-let (n rules) (rel-parts x)
    (let* ((name (fn-sym :rel (second x) cx))
           (cx (cx-put :fn (cdr name) cx)) (cx (cx-put :n 0 cx)) (cx (cx-put :aux nil cx))
           (cx (cx-put :tparams nil cx)))
      (if (eq mode :closure)
          (let* ((step (fn-sym :rel (closure-step x) cx))
                 (fuel (gsym "%FUEL")) (a (gsym "%A0")) (r (gsym "%R"))
                 (aux (gsym (concatenate 'string (cdr name) "/%FUEL"))))
            (mv (list (mk-defun-measure aux (list fuel a) (list 'nfix fuel)
                                        (list 'if (list 'zp fuel) nil
                                              (list 'let (list (list r (list step a)))
                                                    (ignorable-decl (list r))
                                                    (list 'if r (list aux (list '1- fuel) (list 'car r))
                                                          (list 'list a)))))
                      (mk-defun name (list a) (list aux (list (gsym "%FUEL")) a)))
                cx))
        (let ((formals (gsyms-prefixed "%A" (if (eq mode :fun) (1- n) n))))
          (mv-let (cs cx) (crules rules mode formals (second x) cx)
            (mv (append (reverse (cx-get :aux cx))
                        (list (mk-defun name formals
                                        (if (eq mode :fun) (chain-results cs)
                                          (list 'if (chain-results cs) t nil)))))
                cx)))))))

(defun rel-members (x) (if (is x "REC") (cdr x) (list x)))

(defun set-modes (xs mode cx)
  (if (endp xs) cx
    (let ((m (if (closure-step (car xs)) :closure mode)))
      (set-modes (cdr xs) mode
                 (cx-put :modes (put-assoc-equal (second (car xs))
                                                 (cons (if (eq m :check) :check :fun) m)
                                                 (cx-get :modes cx))
                         cx)))))

(defun mode-of (id cx) (cdr (cdr (assoc-equal id (cx-get :modes cx)))))

; Compile members with their registered modes; (mv defuns erroring-ids cx)
(defun crel-members (xs cx)
  (if (endp xs) (mv nil nil cx)
    (let ((nerr (len (cx-get :errs cx))))
      (mv-let (d1 cx) (crel (car xs) (mode-of (second (car xs)) cx) cx)
        (let ((bad (if (equal (len (cx-get :errs cx)) nerr) nil (list (second (car xs))))))
          (mv-let (d2 b2 cx) (crel-members (cdr xs) cx)
            (mv (append d1 d2) (append bad b2) cx)))))))

(defun set-mode-ids (ids mode cx)
  (if (endp ids) cx
    (set-mode-ids (cdr ids) mode
                  (cx-put :modes (put-assoc-equal (car ids) (cons mode mode) (cx-get :modes cx)) cx))))

(defun rel-stubs (xs bad cx)
  ;; stub defuns for erroring relations (right arity for their mode)
  (if (endp xs) nil
    (append (if (member-equal (second (car xs)) bad)
                (mv-let (n rules) (rel-parts (car xs))
                  (declare (ignore rules))
                  (let ((k (if (eq (mode-of (second (car xs)) cx) :check) n (1- n))))
                    (list (stub-defun (fn-sym :rel (second (car xs)) cx) (gsyms-prefixed "%A" k)))))
              nil)
            (rel-stubs (cdr xs) bad cx))))

(defun member-equal-prefix (nm names)
  (and (consp names)
       (or (and (< (length (car names)) (length nm))
                (equal (subseq nm 0 (1+ (length (car names))))
                       (concatenate 'string (car names) "/")))
           (member-equal-prefix nm (cdr names)))))

(defun drop-defuns-of (ds names)
  ;; drop the main defuns (and their aux) of the named relations
  (cond ((endp ds) nil)
        ((let ((nm (cdr (second (car ds)))))
           (or (member-equal nm names)
               (member-equal-prefix nm names)))
         (drop-defuns-of (cdr ds) names))
        (t (cons (car ds) (drop-defuns-of (cdr ds) names)))))

(defun rel-mangled (ids cx)
  (if (endp ids) nil (cons (tbl-name :rel (car ids) cx) (rel-mangled (cdr ids) cx))))

; A relation (or REC group of relations): try :fun; members with errors are
; retried as :check; members still failing become stubs. (mv events cx)
(defun crel-form (x cx)
  (let* ((xs (rel-members x))
         (cx (set-modes xs :fun cx))
         (errs0 (cx-get :errs cx)))
    (mv-let (ds bad cx) (crel-members xs cx)
      (if (null bad)
          (mv ds cx)
        (let* ((errs1 (cx-get :errs cx))          ; errors of the :fun attempt
               (cx (cx-put :errs errs0 cx))
               (cx (set-mode-ids bad :check cx)))
          (mv-let (ds2 bad2 cx) (crel-members xs cx)
            (if (null bad2)
                (mv ds2 cx)
              ;; neither mode works: report the :fun errors, stub in :fun mode
              (let* ((cx (cx-put :errs errs1 cx))
                     (cx (set-modes xs :fun cx))
                     (names (rel-mangled bad cx))
                     (ds (append (drop-defuns-of ds names) (rel-stubs xs bad cx))))
                (mv ds (cx-put :stubs (append (cx-get :stubs cx) names) cx))))))))))

; --- Top-level forms ---------------------------------------------------

(defun form-base (x cx)
  (cond ((is x "TYP") (tbl-name :typ (second x) cx))
        ((is x "DEF") (tbl-name :def (second x) cx))
        (t (second x))))

; Compile one non-REC member. (mv defuns builtins cx), defuns in order
; (aux functions first).
; A form that hits an unsupported construct is emitted as an explicit stub
; (its aux functions are dropped) and listed in :stubs; a def named in the
; config :overrides is treated like a builtin (hand-written in rt/).

(defun cmember (x cx)
  (let* ((cx (cx-put :fn (form-base x cx) cx))
         (cx (cx-put :n 0 cx))
         (cx (cx-put :aux nil cx))
         (cx (cx-put :tparams nil cx))
         (nerr (len (cx-get :errs cx))))
    (cond ((and (is x "DEF") (member-equal (second x) (cx-get :overrides cx)))
           (mv-let (ps more) (def-parts x)
             (declare (ignore more))
             (mv nil (list (cons (tbl-name :def (second x) cx) (len (exp-params ps)))) cx)))
          ((or (is x "TYP") (is x "DEF"))
           (mv-let (d b cx) (if (is x "TYP")
                                (mv-let (d cx) (ctyp x cx) (mv d nil cx))
                              (cdef x cx))
             (if (equal (len (cx-get :errs cx)) nerr)
                 (mv (append (reverse (cx-get :aux cx)) (if d (list d) nil))
                     (if b (list b) nil) cx)
               (mv (list (stub-defun (second d) (third d)))
                   nil
                   (cx-put :stubs (cons (cdr (second d)) (cx-get :stubs cx)) cx)))))
          (t (mv nil nil cx)))))

(defun cmembers (xs cx)
  (if (endp xs) (mv nil nil cx)
    (mv-let (d1 b1 cx) (cmember (car xs) cx)
      (mv-let (d2 b2 cx) (cmembers (cdr xs) cx)
        (mv (append d1 d2) (append b1 b2) cx)))))

; (mv events builtins skipped cx)
(defun cform (x cx)
  (cond ((or (is x "GRAM") (and (is x "REC") (is (cadr x) "GRAM")))
         (mv nil nil (list x) cx))
        ((or (is x "REL") (and (is x "REC") (is (cadr x) "REL")))
         (mv-let (ds cx) (crel-form x cx)
           (mv (if (and (is x "REC") (consp (cdr ds))) (list (cons 'mutual-recursion ds)) ds)
               nil nil cx)))
        ((is x "REC")
         (mv-let (ds bs cx) (cmembers (cdr x) cx)
           (mv (if (consp (cdr ds)) (list (cons 'mutual-recursion ds)) ds) bs nil cx)))
        (t (mv-let (ds bs cx) (cmember x cx) (mv ds bs nil cx)))))

(defun cforms (xs cx)
  (if (endp xs) (mv nil nil nil cx)
    (mv-let (e1 b1 s1 cx) (cform (car xs) cx)
      (mv-let (e2 b2 s2 cx) (cforms (cdr xs) cx)
        (mv (append e1 e2) (append b1 b2) (append s1 s2) cx)))))
