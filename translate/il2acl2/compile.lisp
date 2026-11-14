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

; An error is (fn what x . context): fn the function being compiled; inside a
; relation rule the context is (:rule "Rel/id" :pos k :mode m), k the rule's
; position in the relation (ids need not be unique), m the attempted mode.
(defun cx-err (what x cx)
  (cx-put :errs (cons (append (list (cx-get :fn cx) what x)
                              (and (cx-get :err-rule cx)
                                   (list :rule (cx-get :err-rule cx) :pos (cx-get :err-pos cx)))
                              (and (cx-get :err-mode cx) (list :mode (cx-get :err-mode cx))))
                      (cx-get :errs cx))
          cx))

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

(defun iter-end (lsyms ok)
  ;; base case of a lockstep iteration over several lists: the iteration
  ;; domain requires equal lengths, so it succeeds (with OK) only if all lists
  ;; end together (one list: always)
  (if (consp (cdr lsyms)) (list 'if (cons 'and (atom-tests lsyms)) ok nil) ok))

(defun env-add-vars (names env cx)
  (if (endp names) env
    (env-add-vars (cdr names) (acons (car names) (var-sym (car names) cx) env) cx)))

;; Size of the designated decreasing component (config :decreasing) of an
;; argument list for relation REL, or 0.
(defun dec-size (rel args cx)
  (let ((k (cdr (assoc-equal rel (cx-get :decreasing cx)))))
    (if (and k (< k (len args))) (list (gsym "%SIZE") (nth k args)) 0)))

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
                      (fin (if desc
                               (list (quote nfix) (list (quote -) (list (quote 1+) k) l))
                             (list (quote nfix) (list (quote -) (list (quote 1+) h) k))))
                      (rf (cx-get :rel-formals cx))
                      ;; inside a recursive relation: omega*size(inputs) + counter
                      (def (mk-defun-measure aux (list* k l h fvs)
                                             (if (and rf (subsetp-equal rf fvs))
                                                 (list (gsym "%OM3") (dec-size (cx-get :cur-rel cx) rf cx)
                                                       (list (gsym "%SIZE") (cons (quote list) rf)) fin)
                                               fin)
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
    ((nodep p "LIFT" 1)
     ;; lift(x?) : the option as a list -- same encoding, at most one element
     (mv-let (s pre cx) (scrutinee s cx)
       (mv-let (steps env cx) (cpat (second p) s env cx)
         (mv (append pre (list (list :test (list 'true-listp s))
                               (list :test (list '<= (list 'len s) 1)))
                     steps)
             env cx))))
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
                               (list (list* :bind tv (cons (gsym (or (tbl-name :def g cx) (concatenate (quote string) "$" (base-name g nil))))
                                                      (append others (list s)))))
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
    ((and (is p "ITER") (true-listp p) (= (len p) 3) (atom-is (third p) "OPT")
          (null (unbound-vars (remove-duplicates-equal (fv-exp (second p))) env)))
     ;; e? with no iteration variables (e.g. MUT? in globaltype): as a
     ;; pattern it matches either no element or exactly e. (As an expression
     ;; the iteration would always produce e, wrongly forcing MUT.)
     (mv-let (v cx) (cexp (second p) env cx)
       (mv (list (list :test (list 'or (list 'null s) (list 'equal s (list 'list v))))) env cx)))
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

 ;; Elements of a fixed-length sequence are independent positions, so an
 ;; element that cannot be matched yet (e.g. CONST $lunpack(Lnn) c_1 before
 ;; VSPLAT (Lnn X M) binds Lnn; G9, wasm3 prep P4) is retried once after the
 ;; others. When every element matches in order, nothing changes.
 (defun cpat-elems (ps i s env cx)
   (mv-let (steps env dfr cx) (cpat-elems-1 ps i s env cx)
     (cpat-elems-retry dfr s env steps cx)))

 (defun cpat-elems-1 (ps i s env cx)
   ;; (mv steps env deferred cx), deferred = ((pattern . index) ...) in order
   (if (endp ps) (mv nil env nil cx)
     (let ((errs0 (cx-get :errs cx)) (aux0 (cx-get :aux cx)))
       (mv-let (s1 env1 cx1) (cpat (car ps) (nth-term i s) env cx)
         (if (equal (len (cx-get :errs cx1)) (len errs0))
             (mv-let (s2 env dfr cx) (cpat-elems-1 (cdr ps) (1+ i) s env1 cx1)
               (mv (append s1 s2) env dfr cx))
           (let ((cx (cx-put :aux aux0 (cx-put :errs errs0 cx1))))
             (mv-let (s2 env dfr cx) (cpat-elems-1 (cdr ps) (1+ i) s env cx)
               (mv s2 env (cons (cons (car ps) i) dfr) cx))))))))

 (defun cpat-elems-retry (dfr s env steps cx)
   (if (endp dfr) (mv steps env cx)
     (mv-let (s1 env cx) (cpat (car (car dfr)) (nth-term (cdr (car dfr)) s) env cx)
       (cpat-elems-retry (cdr dfr) s env (append steps s1) cx))))
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

(defun split-last (comps)
  ;; :split mode: last component (case m (tup a b)) -> (mv a b), else (mv nil nil)
  (let ((l (car (last comps))))
    (if (and (nodep l "CASE" 2) (is (third l) "TUP") (= (len (cdr (third l))) 2))
        (mv (second (third l)) (third (third l)))
      (mv nil nil))))

(defun split-name (id cx) (gsym (concatenate 'string (cdr (fn-sym :rel id cx)) "/SPLIT")))


;; Before a premise call to a relation of the current recursive group: the
;; (always true for WASM Step) check size(callee inputs) < size(inputs), which
;; makes termination syntactic (see %OM in rt/prelude.lisp).
;; Before a premise call to a relation of the current recursive group: the
;; check that (size of the decreasing component, size of all inputs) of the
;; callee is lexicographically smaller than the caller's. Derivations never
;; need a subgoal that is not smaller in this order for WASM 1.0 (Step:
;; subterms; typing: shorter instruction lists, or equal ones with a smaller
;; stack), so the check only removes cycles; it makes termination syntactic.
(defun rec-size-check (rel ts cx)
  (let ((rf (cx-get :rel-formals cx)) (me (cx-get :cur-rel cx)))
    (if (and rf (member-equal rel (cx-get :rec-rels cx)))
        (let ((ca (dec-size rel ts cx)) (oa (dec-size me rf cx))
              (cb (list (gsym "%SIZE") (cons (quote list) ts)))
              (ob (list (gsym "%SIZE") (cons (quote list) rf))))
          (list (list :test (list (quote or) (list (quote <) ca oa)
                                  (list (quote and) (list (quote equal) ca oa) (list (quote <) cb ob))))))
      nil)))

;; Output of a :multi premise c(a, b) with b unbound: the output variant
;; computes b, but it drops the stack-polymorphic rules (unreachable, br,
;; br_table, return), so e.g. Instrs_ok/seq cannot get the intermediate stack
;; t_2* after a br (dead code). Fallback, sound because every candidate is
;; CHECKED with the check variant: b ranges over the empty list and the list
;; variables (names ending in *) already bound in the rule. A search point:
;; candidate 0 is the output variant's result, candidate k > 0 is the k-th list.
(defun list-var-terms (env)
  (cond ((endp env) nil)
        ((let ((nm (car (car env))))
           (and (stringp nm) (< 0 (length nm)) (eql (char nm (1- (length nm))) #\*)))
         (cons (cdr (car env)) (list-var-terms (cdr env))))
        (t (list-var-terms (cdr env)))))

(defun strip-cadrs-of (l) (if (endp l) nil (cons (cadr (car l)) (strip-cadrs-of (cdr l)))))

(defun size-tests-term (steps)
  ;; (:test e)... -> (and e...)
  (cons (quote and) (strip-cadrs-of steps)))

(defun multi-candidate-steps (rel comps ts tv sb cands env cx)
  (let* ((l (car (last comps)))
         (lc (list (first l) (second l) (list (first (third l)) (second (third l)) (list (quote var) "%CAND"))))
         (cs (gsym "%CAND")) (kv (gsym "%C"))
         (cands (cons nil cands)))                    ; the empty list first
    (mv-let (tsc cx) (cexps (append (butlast comps 1) (list lc)) (acons "%CAND" cs env) cx)
      (let ((split (list (quote and) (size-tests-term (rec-size-check rel ts cx))
                         (cons (split-name rel cx) ts)))
            (check (list (quote and) (size-tests-term (rec-size-check rel tsc cx))
                         (cons (fn-sym :rel rel cx) tsc)
                         (list (quote list) cs))))
        (mv-let (s1 env cx) (cpat sb (list (quote car) tv) env cx)
          (mv (append (list (list :choose kv 0 (len cands) nil)
                            (list* :bind cs (list (quote if) (list (quote zp) kv) nil
                                                  (list (quote nth) (list (quote 1-) kv) (cons (quote list) cands))))
                            (list* :bind tv (list (quote if) (list (quote zp) kv) split check))
                            (list :test tv))
                      s1)
              env cx))))))

;; a relation premise, possibly iterated
(defun crule-premise (pr env cx)
  (let* ((rel (second pr)) (rest (cddr pr)) (n (len rest))
         (e (nth (- n 1) rest))
         (comps (if (and (is e "TUP") (true-listp e)) (cdr e) (list e)))
         (mode (cdr (assoc-equal rel (cx-get :modes cx))))
         (fn (fn-sym :rel rel cx)))
    (cond
     ((null mode) (mv nil env (cx-err "relation not available" rel cx)))
     ((eq (car mode) :multi)
      ;; all bound: the check variant; else the split variant c(a, b) with b out
      (if (not (has-unbound (cons (quote list) comps) env))
          (mv-let (ts cx) (cexps comps env cx)
            (mv (append (rec-size-check rel ts cx) (list (list :test (cons fn ts)))) env cx))
        (mv-let (sa sb) (split-last comps)
          ;; output variant: b of a last component c(a, b), else the whole
          ;; last component (as in :fun mode)
          (let* ((ins (if sa (append (butlast comps 1) (list sa)) (butlast comps 1)))
                 (sb (if sa sb (car (last comps)))))
            (if (has-unbound (cons (quote list) ins) env)
                (mv nil env (cx-err "relation inputs unbound" pr cx))
              (mv-let (ts cx) (cexps ins env cx)
                (mv-let (tname cx) (cx-fresh "%T" cx)
                  (let ((tv (gsym tname)) (cands (list-var-terms env)))
                    (if (and sa cands)
                        (multi-candidate-steps rel comps ts tv sb cands env cx)
                      (mv-let (s1 env cx) (cpat sb (list (quote car) tv) env cx)
                        (mv (append (rec-size-check rel ts cx)
                                    (list (list* :bind tv (cons (split-name rel cx) ts)) (list :test tv))
                                    s1)
                            env cx)))))))))))
     ((eq (car mode) :fun)
      (let ((ins (butlast comps 1)) (out (car (last comps))))
        (if (has-unbound (cons (quote list) ins) env)
            (mv nil env (cx-err "relation inputs unbound" pr cx))
          (mv-let (ts cx) (cexps ins env cx)
            (mv-let (tname cx) (cx-fresh "%T" cx)
              (let ((tv (gsym tname)))
                (mv-let (s1 env cx) (cpat out (list (quote car) tv) env cx)
                  (mv (append (rec-size-check rel ts cx)
                              (list (list* :bind tv (cons fn ts)) (list :test tv)) s1)
                      env cx))))))))
     (t
      (if (has-unbound (cons (quote list) comps) env)
          (mv nil env (cx-err "checker relation with unbound arguments" pr cx))
        (mv-let (ts cx) (cexps comps env cx)
          (mv (append (rec-size-check rel ts cx) (list (list :test (cons fn ts)))) env cx)))))))

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
   ((and (is pr "ITER") (true-listp pr) (= (len pr) 3) (is (third pr) "LISTN") (true-listp (third pr)))
    ;; G3 (wasm3 prep P4): prem^(k<n) with no list domain, only a count n
    ;; (and possibly a counter k): holds iff prem holds for k = 0 .. n-1.
    ;; An aux function loops over k; the inner premise may not bind variables.
    (let* ((inner (second pr)) (n-e (second (third pr)))
           (kname (and (stringp (third (third pr))) (third (third pr))))
           (knames (and kname (list kname))))
      (if (has-unbound n-e env)
          (mv nil env (cx-err "iterated premise with an unbound count" pr cx))
        (let* ((fvs (bound-in (set-difference-equal (fv-prem inner) knames) env))
               (fvsyms (env-terms fvs env))
               (ksym (if kname (var-sym kname cx) (gsym "%K")))
               (nsym (gsym "%N"))
               (ienv (env-add-vars knames (env-restrict fvs env) cx)))
          (mv-let (nv cx) (cexp n-e env cx)
            (mv-let (isteps env3 cx) (cprem inner ienv cx)
              (if (not (equal (len env3) (len ienv)))
                  (mv nil env (cx-err "iterated premise with a count binds variables" pr cx))
                (mv-let (aux-name cx) (cx-fresh (concatenate 'string (cx-get :fn cx) "/UPTO") cx)
                  (let* ((aux (gsym aux-name))
                         (def (mk-defun-measure
                               aux (list* ksym nsym fvsyms)
                               (list 'nfix (list '- (list 'nfix nsym) (list 'nfix ksym)))
                               (list 'if (list '<= (list 'nfix nsym) (list 'nfix ksym)) t
                                     (build-steps isteps
                                                  (list* aux (list '1+ (list 'nfix ksym)) nsym fvsyms))))))
                    (mv (list (list :test (list* aux 0 nv fvsyms))) env (cx-add-aux def cx)))))))))))
   ((and (is pr "ITER") (true-listp pr) (>= (len pr) 4))
    ;; prem*{x <- xs, ...} / prem?{...}. Doms whose list is unbound are
    ;; outputs; they are only supported for ? iteration, where each output is
    ;; bound by the inner premise (mode analysis, plan §2.5).
    (let* ((inner (second pr)) (it (third pr)) (doms (cdddr pr))
           (ins (doms-bound doms env t)) (outs (doms-bound doms env nil))
           (in-names (dom-names ins)))
      (cond
       ((and (endp ins) (consp outs) (is it "LISTN") (true-listp it) (not (has-unbound (second it) env)))
        ;; G4 (wasm3 prep P4): a counted iteration whose domains are all
        ;; outputs, e.g. (if $ibytes_(K, j) = ...)^(k<M) binding j*: loop over
        ;; k = 0 .. n-1, run the inner premise with k bound, and collect the
        ;; outputs of each iteration into the output lists.
        (let* ((n-e (second it)) (kname (and (stringp (third it)) (third it)))
               (knames (and kname (list kname)))
               (fvs (bound-in (set-difference-equal (fv-prem inner) (append knames (dom-names outs))) env))
               (fvsyms (env-terms fvs env))
               (ksym (if kname (var-sym kname cx) (gsym "%K"))) (nsym (gsym "%N")) (rv (gsym "%R"))
               (ienv (env-add-vars knames (env-restrict fvs env) cx)))
          (mv-let (nv cx) (cexp n-e env cx)
            (mv-let (isteps env3 cx) (cprem inner ienv cx)
              (let ((otms (env-terms (dom-names outs) env3)))
                (if (member-equal nil otms)
                    (mv nil env (cx-err "iterated premise output not bound" pr cx))
                  (mv-let (aux-name cx) (cx-fresh (concatenate 'string (cx-get :fn cx) "/UPTO") cx)
                    (mv-let (tname cx) (cx-fresh "%T" cx)
                      (let* ((aux (gsym aux-name)) (tv (gsym tname))
                             (rec-call (list* aux (list '1+ (list 'nfix ksym)) nsym fvsyms))
                             (def (mk-defun-measure
                                   aux (list* ksym nsym fvsyms)
                                   (list 'nfix (list '- (list 'nfix nsym) (list 'nfix ksym)))
                                   (list 'if (list '<= (list 'nfix nsym) (list 'nfix ksym))
                                         (list 'list (cons 'list (make-list (len outs))))
                                         (build-steps isteps
                                                      (list 'let (list (list rv rec-call)) (ignorable-decl (list rv))
                                                            (list 'and rv (list 'list (cons 'list (cons-cols otms 0 rv))))))))))
                        (mv (append (list (list* :bind tv (list* aux 0 nv fvsyms)) (list :test tv))
                                    (list-out-binds outs 0 tv cx))
                            (env-add-out-lists outs env cx)
                            (cx-add-aux def cx)))))))))))
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
       ((consp outs)
        ;; list iteration with outputs: an aux function runs the inner premise
        ;; on each element of the input lists (in lockstep) and collects the
        ;; output elements into columns; nil if any element fails
        (let* ((fvs (bound-in (set-difference-equal (fv-prem inner) (append in-names (dom-names outs))) env))
               (fvsyms (env-terms fvs env))
               (lsyms (gsyms-prefixed "%L" (len ins)))
               (rv (gsym "%R")))
          (mv-let (ds cx) (cexps (strip-thirds ins) env cx)
            (mv-let (isteps env3 cx)
              (cprem inner (env-add-vars in-names (env-restrict fvs env) cx) cx)
              (let ((otms (env-terms (dom-names outs) env3)))
                (if (member-equal nil otms)
                    (mv nil env (cx-err "iterated premise output not bound" pr cx))
                  (mv-let (aux-name cx) (cx-fresh (concatenate 'string (cx-get :fn cx) "/MAP") cx)
                    (mv-let (tname cx) (cx-fresh "%T" cx)
                      (let* ((aux (gsym aux-name)) (tv (gsym tname))
                             (rec-call (cons aux (append (cdr-terms lsyms) fvsyms)))
                             (def (mk-defun aux (append lsyms fvsyms)
                                            (list 'if (cons 'or (atom-tests lsyms))
                                                  (iter-end lsyms (list 'list (cons 'list (make-list (len outs)))))
                                                  (build-steps
                                                   (append (bind-steps (car-binds in-names lsyms cx)) isteps)
                                                   (list 'let (list (list rv rec-call)) (ignorable-decl (list rv))
                                                         (list 'and rv (list 'list (cons 'list (cons-cols otms 0 rv))))))))))
                        (mv (append (list (list* :bind tv (cons aux (append ds fvsyms)))
                                          (list :test tv))
                                    (list-out-binds outs 0 tv cx))
                            (env-add-out-lists outs env cx)
                            (cx-add-aux def cx)))))))))))
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
                                      (list 'if (cons 'or (atom-tests lsyms)) (iter-end lsyms t)
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

(defun cpat-args-defer (pats formals env cx)
  ;; like cpat-args, but an input pattern that cannot be compiled (e.g.
  ;; FUNC funcinst.TYPE, a projection of a variable bound only by a later
  ;; premise) is deferred: (mv steps env deferred cx), deferred = ((pat . formal) ...),
  ;; to be checked as formal = pat after the premises
  (if (or (endp pats) (endp formals)) (mv nil env nil cx)
    (let ((errs0 (cx-get :errs cx)) (aux0 (cx-get :aux cx)))
      (mv-let (s1 env1 cx1) (cpat (car pats) (car formals) env cx)
        (if (equal (len (cx-get :errs cx1)) (len errs0))
            (mv-let (s2 env dfr cx) (cpat-args-defer (cdr pats) (cdr formals) env1 cx1)
              (mv (append s1 s2) env dfr cx))
          (let ((cx (cx-put :aux aux0 (cx-put :errs errs0 cx1))))
            (mv-let (s2 env dfr cx) (cpat-args-defer (cdr pats) (cdr formals) env cx)
              (mv s2 env (cons (cons (car pats) (car formals)) dfr) cx))))))))

(defun deferred-tests (dfr env cx)
  (if (endp dfr) (mv nil cx)
    (mv-let (e cx) (cexp (car (car dfr)) env cx)
      (mv-let (rest cx) (deferred-tests (cdr dfr) env cx)
        (mv (cons (list :test (list 'equal (cdr (car dfr)) e)) rest) cx)))))

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
  ;; (mv term cx): (list output) / (list t) if rule R applies, else nil.
  ;; :split: inputs are the other components plus the first half a of the
  ;; last component c(a, b); the output is b.
  (mv-let (comps prems) (rule-parts r)
    (mv-let (sa sb) (split-last comps)
    (let* ((ins (cond ((eq mode :fun) (butlast comps 1))
                      ((and (eq mode :split) sa) (append (butlast comps 1) (list sa)))
                      ((eq mode :split) (butlast comps 1))   ; no c(a, b): output is the last component
                      (t comps)))
           (cx (cx-put :redex (and (member-equal (cons rel (second r)) (cx-get :split-rules cx)) t) cx)))
      (mv-let (s1 env dfr cx) (cpat-args-defer ins formals nil cx)
        (let ((cx (cx-put :redex nil cx)))
          (mv-let (s2 env cx) (cprems prems env cx)
            (mv-let (s3 cx) (deferred-tests dfr env cx)
            (mv-let (out cx) (cond ((eq mode :fun) (cexp (car (last comps)) env cx))
                                   ((and (eq mode :split) sa) (cexp sb env cx))
                                   ((eq mode :split) (cexp (car (last comps)) env cx))
                                   (t (mv t cx)))
              (build-steps-cx (append s1 s2 s3) (list 'list out) cx))))))))))

(defun crules (rs mode formals rel cx)
  ;; in :split mode a rule whose output cannot be computed (e.g. unreachable:
  ;; t_1* -> t_2*) is dropped and recorded in :incomplete; the :check variant
  ;; keeps it
  ;;
  ;; Rules are numbered from 0 in :err-pos (error context); a rule whose
  ;; ("Rel/id" . pos) is in :drop-rules is skipped (per-rule stubs, crel-partial).
  (if (endp rs) (mv nil (cx-put :err-rule nil cx))
    (let* ((pos (or (cx-get :err-pos cx) 0))
           (rid (concatenate (quote string) rel "/" (second (car rs))))
           (skip (member-equal (cons rid pos) (cx-get :drop-rules cx)))
           (cx (cx-put :err-rule rid cx))
           (errs0 (cx-get :errs cx)) (aux0 (cx-get :aux cx)))
      (mv-let (c cx) (if skip (mv nil cx) (crule (car rs) mode formals rel cx))
        (let* ((cx (cx-put :err-pos (1+ pos) cx))
               (dropped (and (not skip) (eq mode :split) (not (equal (len (cx-get :errs cx)) (len errs0)))))
               (cx (if dropped
                       (cx-put :incomplete (cons (concatenate 'string rel "/" (second (car rs)))
                                                 (cx-get :incomplete cx))
                               (cx-put :aux aux0 (cx-put :errs errs0 cx)))
                     cx)))
          (mv-let (rest cx) (crules (cdr rs) mode formals rel cx)
            (mv (if (or skip dropped) rest (cons c rest)) cx)))))))

(defun chain-results (cs)
  ;; first non-nil of the rule results, still wrapped: (list output) or nil,
  ;; so that an empty output (e.g. NOP ~> eps) is distinguishable from failure
  (if (endp cs) nil
    (if (and (consp (car cs)) (eq (car (car cs)) 'list) (= (len (car cs)) 2))
        (car cs)                         ; unconditional rule
      (let ((r (gsym "%R")))
        (list 'let (list (list r (car cs))) (ignorable-decl (list r))
              (list 'if r r (chain-results (cdr cs))))))))

(defun rules-split-p (rules)
  ;; the output variant splits c(a, b) iff the (first) rule's last component does
  (and (consp rules)
       (mv-let (comps prems) (rule-parts (car rules))
         (declare (ignore prems))
         (mv-let (sa sb) (split-last comps) (declare (ignore sb)) (and sa t)))))

; (mv defuns cx) for one relation in the given mode
(defun crel-1-body (x mode cx)
  (mv-let (n rules) (rel-parts x)
    (let* ((name (if (eq mode :split) (split-name (second x) cx) (fn-sym :rel (second x) cx)))
           (cx (cx-put :fn (cdr name) cx)) (cx (cx-put :n 0 cx)) (cx (cx-put :aux nil cx))
           (cx (cx-put :tparams nil cx)))
      (cond
       ((zerop n)
        ;; arity 0 (e.g. the notation relation `relation R: ...` with the
        ;; empty tuple): no input/output mode exists, so fail cleanly (G7)
        (mv nil (cx-err "relation with an empty tuple (arity 0)" (second x) cx)))
       ((eq mode :closure)
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
                cx)))
       (t
        (let* ((formals (gsyms-prefixed "%A" (if (or (eq mode :fun) (and (eq mode :split) (not (rules-split-p rules))))
                                                 (1- n) n)))
               (cx (cx-put :rel-formals (and (member-equal (second x) (cx-get :rec-rels cx)) formals) cx))
               (cx (cx-put :cur-rel (second x) cx)))
          (mv-let (cs cx) (crules rules mode formals (second x) cx)
            (let ((body (if (member-eq mode '(:fun :split)) (chain-results cs) (list 'if (chain-results cs) t nil))))
              (mv (append (reverse (cx-get :aux cx))
                          (list (if (cx-get :rel-formals cx)
                                    ;; member of a recursive group: omega*(1+size(inputs))
                                    (mk-defun-measure name formals
                                                      (list (gsym "%OM3") (dec-size (second x) formals cx)
                                                            (list (quote 1+) (list (gsym "%SIZE") (cons (quote list) formals)))
                                                            0)
                                                      body)
                                  (mk-defun name formals body))))
                  cx)))))))))

; Aux functions of a relation in a rec group can contain the generated size
; check of a recursive premise, which compares against the relation's own
; formals (:rel-formals). Such an aux gets the formals it uses as extra
; trailing parameters, and every call to it in the relation passes them
; (repeated until no aux uses a formal it does not have). Found by the first
; certification of 3.0 code (COMPTYPE_SUB/MAP5, wasm3 prep P5); an aux that
; does not use them is unchanged.
(defun gsym-occurs (s x)
  (cond ((gsym-p x) (equal x s))
        ((consp x) (or (gsym-occurs s (car x)) (gsym-occurs s (cdr x))))
        (t nil)))

(defun missing-formals (rf d)
  ;; formals in rf that the body of defun d uses but d does not take
  (cond ((endp rf) nil)
        ((and (not (member-equal (car rf) (third d))) (gsym-occurs (car rf) (cdddr d)))
         (cons (car rf) (missing-formals (cdr rf) d)))
        (t (missing-formals (cdr rf) d))))

(defun needy-defuns (ds rf)
  (cond ((endp ds) nil)
        ((and (consp (car ds)) (eq (car (car ds)) 'defun) (missing-formals rf (car ds)))
         (cons (cons (second (car ds)) (missing-formals rf (car ds))) (needy-defuns (cdr ds) rf)))
        (t (needy-defuns (cdr ds) rf))))

(defun add-call-args (x name extras)
  (cond ((gsym-p x) x)
        ((atom x) x)
        ((eq (car x) (quote defun))                ; not a call: keep name and formals
         (list* (car x) (cadr x) (caddr x) (add-call-args (cdddr x) name extras)))
        ((equal (car x) name) (append (cons name (add-call-args (cdr x) name extras)) extras))
        (t (cons (add-call-args (car x) name extras) (add-call-args (cdr x) name extras)))))

(defun add-formals (ds name extras)
  (cond ((endp ds) nil)
        ((and (consp (car ds)) (eq (car (car ds)) 'defun) (equal (second (car ds)) name))
         (cons (list* 'defun name (append (third (car ds)) extras) (cdddr (car ds))) (cdr ds)))
        (t (cons (car ds) (add-formals (cdr ds) name extras)))))

(defun apply-needy (ds needy)
  (if (endp needy) ds
    (let* ((name (car (car needy))) (extras (cdr (car needy)))
           (ds (add-call-args ds name extras))
           (ds (add-formals ds name extras)))
      (apply-needy ds (cdr needy)))))

(defun close-aux-formals (ds rf fuel)
  (let ((needy (and rf (needy-defuns ds rf))))
    (if (or (null needy) (zp fuel)) ds
      (close-aux-formals (apply-needy ds needy) rf (1- fuel)))))

(defun crel-1 (x mode cx)
  ;; errors logged while compiling carry the attempted mode
  (mv-let (ds cx)
    (crel-1-body x mode (cx-put :err-pos 0 (cx-put :err-rule nil (cx-put :err-mode mode cx))))
    (mv (close-aux-formals ds (cx-get :rel-formals cx) 20)
        (cx-put :err-pos nil (cx-put :err-rule nil (cx-put :err-mode nil cx))))))

(defun crel (x mode cx)
  (if (eq mode :multi)
      ;; both variants: R (all inputs) and R/SPLIT (output = second half of the
      ;; last component)
      (mv-let (d1 cx) (crel-1 x :check cx)
        (mv-let (d2 cx) (crel-1 x :split cx)
          (mv (append d1 d2) cx)))
    (crel-1 x mode cx)))

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
                  (let ((k (if (eq (mode-of (second (car xs)) cx) :check) n (nfix (1- n)))))
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
(defun strip-seconds (l) (if (endp l) nil (cons (second (car l)) (strip-seconds (cdr l)))))

(defun calls-multi (x cx)
  ;; does IL term x contain a premise (rule "Rel" ...) of a :multi relation?
  (cond ((atom x) nil)
        ((and (is x "RULE") (stringp (second x)) (eq (mode-of (second x) cx) :multi)) t)
        (t (or (calls-multi (car x) cx) (calls-multi (cdr x) cx)))))

; --- Per-rule stubs (wasm3 prep P1) -----------------------------------
;
; When no mode compiles every rule of a relation group, the attempt with the
; fewest failing rules wins: its failing rules are dropped (:drop-rules) and
; the group is compiled again in that attempt's modes. Dropping a rule is
; sound (every result still has a derivation) but incomplete; the dropped
; rules are listed in :partial and in the generated header. Errors that no
; rule carries (relation-level) cannot be dropped: such members, or a group
; that still fails, are stubbed as before.

(defun new-errs (errs errs0) (take (- (len errs) (len errs0)) errs))

(defun err-rule-keys (errs acc)
  ;; distinct ("Rel/id" . pos) of the errors that carry a rule
  (if (endp errs) acc
    (let* ((ctx (cdddr (car errs))) (r (member :rule ctx)))
      (err-rule-keys (cdr errs)
                     (if r
                         (let ((k (cons (cadr r) (cadr (member :pos ctx)))))
                           (if (member-equal k acc) acc (append acc (list k))))
                       acc)))))

(defun count-unattributed (errs)
  (cond ((endp errs) 0)
        ((member :rule (cdddr (car errs))) (count-unattributed (cdr errs)))
        (t (1+ (count-unattributed (cdr errs))))))

(defun attempt-score (errs)
  ;; failing rules, with relation-level errors counted as unrecoverable
  (+ (len (err-rule-keys errs nil)) (* 100000 (count-unattributed errs))))

(defun attempt-scores (attempts)
  ;; (failing-rules . unattributed-errors) per attempt
  (if (endp attempts) nil
    (cons (cons (len (err-rule-keys (car (car attempts)) nil)) (count-unattributed (car (car attempts))))
          (attempt-scores (cdr attempts)))))

(defun best-attempt (attempts best)
  ;; attempts: list of (new-errs . modes); earliest wins a tie
  (cond ((endp attempts) best)
        ((or (null best) (< (attempt-score (car (car attempts))) (attempt-score (car best))))
         (best-attempt (cdr attempts) (car attempts)))
        (t (best-attempt (cdr attempts) best))))

(defun keys-of-rel (keys rel)
  ;; rule ids of the keys that belong to relation rel
  (cond ((endp keys) nil)
        ((let ((s (car (car keys))))
           (and (< (length rel) (length s))
                (equal (subseq s 0 (1+ (length rel))) (concatenate 'string rel "/"))))
         (cons (car (car keys)) (keys-of-rel (cdr keys) rel)))
        (t (keys-of-rel (cdr keys) rel))))

(defun partial-entries (xs keys modes)
  ;; (("Rel" total (dropped "Rel/id" ...) mode) ...) for members that keep
  ;; some rules; a member that would lose every rule is stubbed instead
  (if (endp xs) nil
    (let ((d (keys-of-rel keys (second (car xs)))))
      (mv-let (n rules) (rel-parts (car xs))
        (declare (ignore n))
        (if (and d (< (len d) (len rules)))
            (cons (list (second (car xs)) (len rules) d
                        (cdr (cdr (assoc-equal (second (car xs)) modes))))
                  (partial-entries (cdr xs) keys modes))
          (partial-entries (cdr xs) keys modes))))))

(defun fully-dropped (xs keys)
  ;; ids of the members whose every rule is dropped
  (if (endp xs) nil
    (let ((d (keys-of-rel keys (second (car xs)))))
      (mv-let (n rules) (rel-parts (car xs))
        (declare (ignore n))
        (if (and d (>= (len d) (len rules)))
            (cons (second (car xs)) (fully-dropped (cdr xs) keys))
          (fully-dropped (cdr xs) keys))))))

(defun rel-fn-names (ids cx)
  ;; main and split function names of relations ids
  (if (endp ids) nil
    (list* (tbl-name :rel (car ids) cx) (cdr (split-name (car ids) cx))
           (rel-fn-names (cdr ids) cx))))

(defun stub-named-defuns (ds names)
  ;; replace each defun named in names by a stub with the same formals
  (cond ((endp ds) nil)
        ((and (consp (car ds)) (eq (car (car ds)) 'defun) (member-equal (cdr (second (car ds))) names))
         (cons (stub-defun (second (car ds)) (third (car ds))) (stub-named-defuns (cdr ds) names)))
        (t (cons (car ds) (stub-named-defuns (cdr ds) names)))))

(defun salvageable (attempt)
  ;; some rule fails, and every error belongs to a rule (so dropping helps)
  (and (err-rule-keys (car attempt) nil) (equal (count-unattributed (car attempt)) 0)))

(defun attempt-index (a attempts) (- (len attempts) (len (member-equal a attempts))))

; (mv defuns cx). ds/bad/errs1: the :fun attempt; attempts: (new-errs . modes)
; for :fun, :check, :multi.
;  - reported: the errors of the attempt with the fewest failing rules (the
;    one that got furthest), plus those of the emitted attempt if different;
;    every error carries its :mode
;  - emitted: the :fun attempt when dropping rules saves it (the interface the
;    old whole-relation stub had: per-rule stubs change granularity, not
;    modes), else the best salvageable attempt. Choosing better modes is the
;    mode table's job (wasm3 prep P4)
(defun crel-partial (xs ds bad errs0 errs1 attempts cx)
  (let* ((best (best-attempt attempts nil))
         (emit (cond ((salvageable (car attempts)) (car attempts))
                     ((salvageable best) best)
                     (t nil)))
         (keys (and emit (err-rule-keys (car emit) nil)))
         (reported (append (car best) (if (and emit (not (equal emit best))) (car emit) nil)))
         (drop0 (cx-get :drop-rules cx))
         (cx (cx-put :attempt-log
                     (append (cx-get :attempt-log cx)
                             (list (list (strip-seconds xs) (attempt-scores attempts)
                                         :best (attempt-index best attempts)
                                         :emitted (and emit (attempt-index emit attempts)))))
                     cx)))
    (mv-let (dsr badr cxr)
      (if emit
          (crel-members xs (cx-put :drop-rules (append keys drop0)
                                   (cx-put :modes (cdr emit) (cx-put :errs errs0 cx))))
        (mv nil t cx))
      (if (null badr)
          (let* ((cxr (cx-put :drop-rules drop0 cxr))
                 (cxr (cx-put :errs (append reported errs0) cxr))
                 (full (fully-dropped xs keys))
                 (cxr (cx-put :stubs (append (cx-get :stubs cxr) (rel-mangled full cxr)) cxr)))
            (mv (stub-named-defuns dsr (rel-fn-names full cxr))
                (cx-put :partial (append (cx-get :partial cxr) (partial-entries xs keys (cdr emit))) cxr)))
        ;; still failing: report the best attempt's errors, stub in :fun mode
        (let* ((cx (cx-put :errs (if (car best) (append (car best) errs0) errs1) cx))
               (cx (set-modes xs :fun cx))
               (names (rel-mangled bad cx))
               (ds (append (drop-defuns-of ds names) (rel-stubs xs bad cx))))
          (mv ds (cx-put :stubs (append (cx-get :stubs cx) names) cx)))))))

(defun crel-form-1 (x cx)
  (let* ((xs (rel-members x))
         (cx (set-modes xs :fun cx))
         (errs0 (cx-get :errs cx)))
    (mv-let (ds bad cx) (crel-members xs cx)
      (if (null bad)
          ;; multi-mode propagates: a :fun relation that calls a :multi one
          ;; (e.g. Expr_ok -> Instrs_ok) is also compiled :multi, so callers
          ;; that know its output (Func_ok knows t_2?) use the check variant,
          ;; which keeps the rules the output variant drops (return, br, ...)
          (if (calls-multi (rel-members x) cx)
              (mv-let (dsm badm cxm)
                (crel-members xs (set-mode-ids (strip-seconds xs) :multi (cx-put :errs errs0 cx)))
                (if (null badm) (mv dsm cxm) (mv ds cx)))
            (mv ds cx))
        (let* ((errs1 (cx-get :errs cx))          ; errors of the :fun attempt
               (modes1 (cx-get :modes cx))
               (cx (cx-put :errs errs0 cx))
               (cx (set-mode-ids bad :check cx))
               (modes2 (cx-get :modes cx)))
          (mv-let (ds2 bad2 cx) (crel-members xs cx)
            (if (null bad2)
                (mv ds2 cx)
              ;; third attempt: :multi (check variant + split variant)
              (let* ((errs2 (cx-get :errs cx))
                     (cx (set-mode-ids (strip-seconds xs) :multi (cx-put :errs errs0 cx)))
                     (modes3 (cx-get :modes cx)))
                (mv-let (ds3 bad3 cx) (crel-members xs cx)
                  (if (null bad3)
                      (mv ds3 cx)
                    ;; no mode works for every rule: per-rule stubs
                    (crel-partial xs ds bad errs0 errs1
                                  (list (cons (new-errs errs1 errs0) modes1)
                                        (cons (new-errs errs2 errs0) modes2)
                                        (cons (new-errs (cx-get :errs cx) errs0) modes3))
                                  cx)))))))))))

; --- Grammars (plan §2.6): binary-format parsers -----------------------
;
; A grammar G becomes GRAM/G(%S, params...) returning (list value rest) or
; nil: productions in order (PEG-style ordered choice), greedy iteration
; that stops when an iteration consumes nothing. Grammars with grammar
; parameters (Blist, Bsection_) are inlined at each use with the argument
; substituted (cx :gram-subst), so no higher-order functions are needed.
; Config :sized (G . var): in G, the item after the one binding VAR is
; parsed from exactly VAR bytes (the IL's `len = 0` stands for
; `len = ||BX||`, which elaboration loses).

(defun hex-value-cs (cs acc)
  (if (endp cs) acc
    (hex-value-cs (cdr cs)
                  (+ (* 16 acc)
                     (let ((c (car cs)))
                       (if (char<= #\A c) (+ 10 (- (char-code c) (char-code #\A)))
                         (- (char-code c) (char-code #\0))))))))

(defun hex-value (s)
  ;; "0X0B" -> 11
  (let ((cs (coerce (string-upcase (subseq s 2 (length s))) 'list)))
    (hex-value-cs cs 0)))

(defun gram-def (id cx) (cdr (assoc-equal id (cx-get :gram-defs cx))))

(defun gram-param-in (ps)
  (and (consp ps) (or (is (car ps) "GRAM") (gram-param-in (cdr ps)))))

(defun gram-parametric-p (x)
  ;; has a grammar parameter
  (mv-let (ps more) (def-parts x)
    (declare (ignore more))
    (gram-param-in ps)))

(defun gram-prods (x) (mv-let (ps more) (def-parts x) (declare (ignore ps)) (cdr more)))

(defun prod-parts (p)
  ;; (prod params... sym exp prems...) -> (mv sym exp prems)
  (let* ((rest (cdr p)) (ps (take-while-params rest)) (more (nthcdr (len ps) rest)))
    (mv (first more) (second more) (cddr more))))

(defun size-zero-prem-p-loose (pr var)
  ;; compare by symbol names (the IL reader's package does not matter)
  (and (nodep pr "IF" 1)
       (let ((e (second pr)))
         (and (nodep e "CMP" 4) (atom-is (second e) "EQ")
              (nodep (fourth e) "VAR" 1) (equal (second (fourth e)) var)
              (nodep (fifth e) "NUM" 1) (nodep (second (fifth e)) "NAT" 1)
              (eql (second (second (fifth e))) 0)))))

(defun drop-size-prems (prs var)
  (cond ((endp prs) nil)
        ((and var (size-zero-prem-p-loose (car prs) var)) (drop-size-prems (cdr prs) var))
        (t (cons (car prs) (drop-size-prems (cdr prs) var)))))

(defun gram-args-exps (as) (exp-args as))

(defun gram-args-grams (as)
  (cond ((endp as) nil)
        ((is (car as) "GRAM") (cons (second (car as)) (gram-args-grams (cdr as))))
        (t (gram-args-grams (cdr as)))))

(defun gram-param-names (ps)
  (cond ((endp ps) nil)
        ((is (car ps) "GRAM") (cons (second (car ps)) (gram-param-names (cdr ps))))
        (t (gram-param-names (cdr ps)))))

(defun exp-param-names (ps)
  (cond ((endp ps) nil)
        ((is (car ps) "EXP") (cons (second (car ps)) (exp-param-names (cdr ps))))
        (t (exp-param-names (cdr ps)))))

(defun bind-names-terms (names terms cx)
  ;; steps binding SpecTec vars NAMES to TERMS, and the env entries
  (if (endp names) (mv nil nil)
    (mv-let (s e) (bind-names-terms (cdr names) (cdr terms) cx)
      (mv (cons (list* :bind (var-sym (car names) cx) (car terms)) s)
          (acons (car names) (var-sym (car names) cx) e)))))

(defun pair-subst (names syms env)
  (if (endp names) nil
    (acons (car names) (cons (car syms) env) (pair-subst (cdr names) (cdr syms) env))))

(defun cons-cols-of (n i e rv)
  ;; ((cons (nth i (car e)) (nth i (car rv))) ...)
  (if (zp n) nil
    (cons (list 'cons (nth-term i (list 'car e)) (nth-term i (list 'car rv)))
          (cons-cols-of (1- n) (1+ i) e rv))))

(defun single-cols (n i e)
  (if (zp n) nil
    (cons (list 'list (nth-term i (list 'car e))) (single-cols (1- n) (1+ i) e))))

(defun list-out-binds-from (outs i tv cx)
  (if (endp outs) nil
    (cons (list* :bind (var-sym (second (third (car outs))) cx)
                 (nth-term i (list 'car tv)))
          (list-out-binds-from (cdr outs) (1+ i) tv cx))))

(mutual-recursion

 ;; (mv steps value-term pos-term env cx)
 (defun csym (sym pos env cx)
   (cond
    ((atom-is sym "EPS") (mv nil nil pos env cx))
    ((nodep sym "NUM" 1)
     (let ((n (hex-value (symbol-name (second sym)))))
       (mv (list (list :test (list 'consp pos)) (list :test (list 'equal (list 'car pos) n)))
           n (list 'cdr pos) env cx)))
    ((nodep sym "RANGE" 2)
     (let ((a (hex-value (symbol-name (second (second sym)))))
           (b (hex-value (symbol-name (second (third sym))))))
       (mv (list (list :test (list 'consp pos))
                 (list :test (list 'integerp (list 'car pos)))
                 (list :test (list '<= a (list 'car pos)))
                 (list :test (list '<= (list 'car pos) b)))
           (list 'car pos) (list 'cdr pos) env cx)))
    ((and (is sym "VAR") (true-listp sym))
     (let* ((id (second sym)) (sub (assoc-equal id (cx-get :gram-subst cx))))
       (cond
        (sub ;; grammar parameter: the argument, compiled in the caller's env
         (mv-let (steps v p env2 cx) (csym (cadr sub) pos (cddr sub) cx)
           (declare (ignore env2))
           (mv steps v p env cx)))
        ((let ((d (gram-def id cx))) (and d (gram-parametric-p d)))
         (cinline-gram (gram-def id cx) (cddr sym) pos env cx))
        (t
         (mv-let (as cx) (cexps (gram-args-exps (cddr sym)) env cx)
           (mv-let (tname cx) (cx-fresh "%T" cx)
             (let ((tv (gsym tname)))
               ;; progress check (always true): rest is no longer than the input,
               ;; which makes parser termination syntactic (T8)
               (mv (list (list* :bind tv (list* (fn-sym :gram id cx) pos as))
                         (list :test tv)
                         (list :test (list (quote <=) (list (quote len) (list (quote cadr) tv))
                                           (list (quote len) pos))))
                   (list 'car tv) (list 'cadr tv) env cx))))))))
    ((nodep sym "ATTR" 2)
     (mv-let (steps v p env cx) (csym (third sym) pos env cx)
       (mv-let (vname cx) (cx-fresh "%T" cx)
         (let ((vv (gsym vname)))
           (mv-let (s2 env cx) (cpat (second sym) vv env cx)
             (mv (append steps (list (list* :bind vv v)) s2) vv p env cx))))))
    ((and (is sym "SEQ") (true-listp sym))
     (cseq (cdr sym) pos env nil cx))
    ((and (is sym "ALT") (true-listp sym))
     (mv-let (alts cx) (calts (cdr sym) pos env cx)
       (mv-let (tname cx) (cx-fresh "%T" cx)
         (let ((tv (gsym tname)))
           (mv (list (list* :bind tv (cons 'or alts)) (list :test tv))
               (list 'car tv) (list 'cadr tv) env cx)))))
    ((and (is sym "ITER") (true-listp sym) (>= (len sym) 3))
     (citer-sym (second sym) (third sym) (cdddr sym) pos env cx))
    (t (mv nil nil pos env (cx-err "grammar symbol" sym cx)))))

 ;; sequence; SIZED-NEXT is the var whose value bounds the next item
 (defun cseq (syms pos env sized-next cx)
   (if (endp syms) (mv nil nil pos env cx)
     (let ((svar (cdr (assoc-equal (cx-get :gram-name cx) (cx-get :sized cx)))))
       (if sized-next
           (let ((lenv (cdr (assoc-equal sized-next env))))
             (mv-let (bname cx) (cx-fresh "%T" cx)
               (let ((bv (gsym bname)))
                 (mv-let (s1 v1 p1 env cx) (csym (car syms) bv env cx)
                   (declare (ignore v1))
                   (mv-let (s2 v2 p2 env cx)
                     (cseq (cdr syms) (list 'nthcdr lenv pos) env nil cx)
                     (mv (append (list (list :test (list 'natp lenv))
                                       (list :test (list '<= lenv (list 'len pos)))
                                       (list* :bind bv (list 'take lenv pos)))
                                 s1
                                 (list (list :test (list 'null p1)))
                                 s2)
                         v2 p2 env cx))))))
         (mv-let (s1 v1 p1 env1 cx) (csym (car syms) pos env cx)
           (mv-let (pname cx) (cx-fresh "%T" cx)
             (let* ((pv (gsym pname))
                    (next-sized (and svar (assoc-equal svar env1) (not (assoc-equal svar env)) svar)))
               (mv-let (s2 v2 p2 env cx) (cseq (cdr syms) pv env1 next-sized cx)
                 (mv (append s1 (list (list* :bind pv p1)) s2)
                     (if (endp (cdr syms)) v1 v2) p2 env cx)))))))))

 (defun calts (syms pos env cx)
   (if (endp syms) (mv nil cx)
     (mv-let (s v p env2 cx) (csym (car syms) pos env cx)
       (declare (ignore env2))
       (mv-let (rest cx) (calts (cdr syms) pos env cx)
         (mv (cons (build-steps s (list 'list v p)) rest) cx)))))

 ;; sym*{x <- xs ...} / sym^n / sym?: greedy loop in an aux function.
 ;; Columns: element values, then each output dom.
 (defun citer-sym (body it doms pos env cx)
   (let* ((outs (doms-bound doms env nil)) (out-names (dom-names outs))
          (sv (gsym "%S")) (kv (gsym "%K")) (nv (gsym "%N")) (rv (gsym "%R"))
          (counted (is it "LISTN")) (opt (atom-is it "OPT")))
     (mv-let (bsteps bval bpos env3 cx) (csym body sv env cx)
       (let* ((otms (env-terms out-names env3))
              (elem (build-steps (append bsteps (list (list* :bind (gsym "%P") bpos)))
                                 (list 'list (cons 'list (cons bval otms)) (gsym "%P"))))
              (fvs (set-difference-equal (term-fv elem nil nil) (list sv (gsym "%P"))))
              (ncols (1+ (len outs)))
              (empty (cons 'list (make-list ncols))))
         (mv-let (aux-name cx) (cx-fresh (concatenate 'string (cx-get :fn cx) "/REP") cx)
           (let* ((aux (gsym aux-name))
                  (e (gsym "%E"))
                  (cols (cons 'list (cons-cols-of ncols 0 e rv)))
                  (def
                   (cond
                    (opt (mk-defun aux (cons sv fvs)
                                   (list 'let (list (list e elem)) (ignorable-decl (list e))
                                         (list 'if e
                                               (list 'list (cons 'list (single-cols ncols 0 e)) (list 'cadr e))
                                               (list 'list empty sv)))))
                    (counted
                     (mk-defun-measure aux (list* kv nv sv fvs) (list 'nfix (list '- nv kv))
                       (list 'if (list 'not (list 'and (list 'natp kv) (list 'natp nv) (list '< kv nv)))
                             (list 'list empty sv)
                             (list 'let (list (list e elem)) (ignorable-decl (list e))
                                   (list 'and e
                                         (list 'let (list (list rv (list* aux (list '1+ kv) nv (list 'cadr e) fvs)))
                                               (ignorable-decl (list rv))
                                               (list 'and rv (list 'list cols (list 'cadr rv)))))))))
                    (t
                     (mk-defun-measure aux (cons sv fvs) (list '+ 1 (list '* 2 (list 'len sv)))
                       (list 'let (list (list e elem)) (ignorable-decl (list e))
                             (list 'if (list 'and e (list '< (list 'len (list 'cadr e)) (list 'len sv)))
                                   (list 'let (list (list rv (list* aux (list 'cadr e) fvs)))
                                         (ignorable-decl (list rv))
                                         (list 'and rv (list 'list cols (list 'cadr rv))))
                                   (list 'list empty sv))))))))
             (mv-let (cnt cx) (if counted (cexp (second it) env cx) (mv nil cx))
               (mv-let (tname cx) (cx-fresh "%T" cx)
                 (let ((tv (gsym tname)))
                   (mv (append (list (list* :bind tv (if counted (list* aux 0 cnt pos fvs) (list* aux pos fvs)))
                                     (list :test tv)
                                     (list :test (list (quote <=) (list (quote len) (list (quote cadr) tv))
                                                       (list (quote len) pos))))
                               (list-out-binds-from outs 1 tv cx))
                       (list 'car (list 'car tv))
                       (list 'cadr tv)
                       (env-add-out-lists outs env cx)
                       (cx-add-aux def cx)))))))))))

 ;; inline a grammar with grammar parameters at a use site
 (defun cinline-gram (g args pos env cx)
   (mv-let (ps more) (def-parts g)
     (declare (ignore more))
     (mv-let (as cx) (cexps (gram-args-exps args) env cx)
       (mv-let (bsteps benv) (bind-names-terms (exp-param-names ps) as cx)
         (let* ((saved-subst (cx-get :gram-subst cx)) (saved-name (cx-get :gram-name cx))
                (cx (cx-put :gram-subst (append (pair-subst (gram-param-names ps) (gram-args-grams args) env)
                                                saved-subst)
                            cx))
                (cx (cx-put :gram-name (second g) cx)))
           (mv-let (pname cx) (cx-fresh "%T" cx)
             (let ((pv (gsym pname)))
               (mv-let (terms cx) (cprods (gram-prods g) pv benv cx)
                 (let* ((cx (cx-put :gram-subst saved-subst cx))
                        (cx (cx-put :gram-name saved-name cx)))
                   (mv-let (tname cx) (cx-fresh "%T" cx)
                     (let ((tv (gsym tname)))
                       (mv (append (list (list* :bind pv pos))
                                   bsteps
                                   (list (list* :bind tv (chain-results terms)) (list :test tv)
                                         (list :test (list (quote <=) (list (quote len) (list (quote cadr) tv))
                                                           (list (quote len) pv)))))
                           (list 'car tv) (list 'cadr tv) env cx))))))))))))

 (defun cprods (prods pos env cx)
   (if (endp prods) (mv nil cx)
     (mv-let (term cx) (cprod (car prods) pos env cx)
       (mv-let (rest cx) (cprods (cdr prods) pos env cx)
         (mv (cons term rest) cx)))))

 ;; one production: (list (list result rest)) or nil
 (defun cprod (p pos env cx)
   (mv-let (sym e prems) (prod-parts p)
     (let* ((svar (cdr (assoc-equal (cx-get :gram-name cx) (cx-get :sized cx))))
            (prems (if svar (drop-size-prems prems svar) prems)))
       (mv-let (s1 v p1 env cx) (csym sym pos env cx)
         (declare (ignore v))
         (mv-let (pname cx) (cx-fresh "%T" cx)
           (let ((pv (gsym pname)))
             (mv-let (s2 env cx) (cprems prems env cx)
               (mv-let (r cx) (cexp e env cx)
                 (mv (build-steps (append s1 (list (list* :bind pv p1)) s2)
                                  (list 'list r pv))
                     cx)))))))))
 )

; (mv defun cx) for a non-parametric grammar
(defun cgram (x cx)
  (mv-let (ps more) (def-parts x)
    (declare (ignore more))
    (let* ((sv (gsym "%S"))
           (cx (cx-put :gram-name (second x) cx)) (cx (cx-put :gram-subst nil cx))
           (names (exp-param-names ps))
           (formals (gsyms-prefixed "%A" (len names))))
      (mv-let (bsteps benv) (bind-names-terms names formals cx)
        (mv-let (terms cx) (cprods (gram-prods x) sv benv cx)
          (mv (if (cx-get :gram-rec cx)
                  ;; recursive grammar: measure 2|S| (its loops use 2|S|+1)
                  (mk-defun-measure (fn-sym :gram (second x) cx) (cons sv formals)
                                    (list (quote *) 2 (list (quote len) sv))
                                    (build-steps bsteps (chain-results terms)))
                (mk-defun (fn-sym :gram (second x) cx) (cons sv formals)
                          (build-steps bsteps (chain-results terms))))
              cx))))))

(defun cgram-members (xs cx)
  ;; (mv defuns cx); parametric grammars are inlined, not emitted
  (if (endp xs) (mv nil cx)
    (if (gram-parametric-p (car xs))
        (cgram-members (cdr xs) cx)
      (let* ((cx (cx-put :fn (tbl-name :gram (second (car xs)) cx) cx))
             (cx (cx-put :n 0 cx)) (cx (cx-put :aux nil cx)) (cx (cx-put :tparams nil cx))
             (nerr (len (cx-get :errs cx))))
        (mv-let (d cx) (cgram (car xs) cx)
          (let* ((ok (equal (len (cx-get :errs cx)) nerr))
                 (mine (if ok (append (reverse (cx-get :aux cx)) (list d))
                         (list (stub-defun (second d) (third d)))))
                 (cx (if ok cx (cx-put :stubs (cons (cdr (second d)) (cx-get :stubs cx)) cx))))
            (mv-let (rest cx) (cgram-members (cdr xs) cx)
              (mv (append mine rest) cx))))))))

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
(defun crel-form (x cx)
  (mv-let (ds cx) (crel-form-1 x (cx-put :rec-rels (and (is x "REC") (strip-seconds (cdr x))) cx))
    (mv ds (cx-put :rel-formals nil (cx-put :rec-rels nil cx)))))

; --- Cliques: only functions that really recurse go in mutual-recursion ---

(mutual-recursion
(defun calls-of (x acc)
  ;; generated function names called in term x
  (cond ((atom x) acc)
        ((gsym-p x) acc)
        (t (let ((acc (if (and (gsym-p (car x)) (not (member-equal (cdr (car x)) acc)))
                          (cons (cdr (car x)) acc)
                        acc)))
             (if (gsym-p (car x))
                 (calls-of-list (cdr x) acc)
               (calls-of-list x acc))))))

(defun calls-of-list (l acc)
  (if (atom l) acc (calls-of-list (cdr l) (calls-of (car l) acc)))))

(defun defun-name (d) (cdr (second d)))
(defun defun-calls (d) (calls-of (cdddr d) nil))

(defun member-main-names (xs cx)
  (cond ((endp xs) nil)
        (t (cons (cond ((is (car xs) "TYP") (tbl-name :typ (second (car xs)) cx))
                       ((is (car xs) "DEF") (tbl-name :def (second (car xs)) cx))
                       ((is (car xs) "REL") (tbl-name :rel (second (car xs)) cx))
                       (t (tbl-name :gram (second (car xs)) cx)))
                 (member-main-names (cdr xs) cx)))))

; names in DS (by name) that can reach a name in SET; iterate to a fixpoint
(defun reaching-step (ds set)
  (cond ((endp ds) set)
        ((and (not (member-equal (defun-name (car ds)) set))
              (intersection-equal (defun-calls (car ds)) set))
         (reaching-step (cdr ds) (cons (defun-name (car ds)) set)))
        (t (reaching-step (cdr ds) set))))

(defun reaching (ds set fuel)
  (if (zp fuel) set
    (let ((set2 (reaching-step ds set)))
      (if (equal (len set2) (len set)) set (reaching ds set2 (1- fuel))))))

(defun split-clique (ds in)
  ;; (mv outside inside), order preserved
  (if (endp ds) (mv nil nil)
    (mv-let (o i) (split-clique (cdr ds) in)
      (if (member-equal (defun-name (car ds)) in)
          (mv o (cons (car ds) i))
        (mv (cons (car ds) o) i)))))

(defun strip-defun-names (ds)
  (if (endp ds) nil (cons (defun-name (car ds)) (strip-defun-names (cdr ds)))))

(defun suffix-all (l s)
  (if (endp l) nil (cons (concatenate (quote string) (car l) s) (suffix-all (cdr l) s))))

;; config :memoize. A memoized relation R (and R/SPLIT) becomes an entry R that
;; HONS-COPYs its arguments and calls R/%M, the original body, which is
;; memoized after the clique. Semantically the identity (hons-copy x = x); the
;; copy makes equal arguments EQ, so the memo table hits for the sub-lists the
;; split searches build with TAKE (memoize keys unnormed conses by address).
(defun rel-mangled-memo (ids cx)
  (if (endp ids) nil (cons (tbl-name :rel (car ids) cx) (rel-mangled-memo (cdr ids) cx))))

(defun memo-measure (d)
  ;; d's (declare (xargs :measure (%OM3 a b 0))) with the last component 1
  (let ((m (and (consp (fifth d)) (consp (cdr (fifth d))) (consp (cadr (fifth d)))
                (cadr (member :measure (cdr (cadr (fifth d))))))))
    (and (consp m) (append (butlast m 1) (list 1)))))

(defun hons-copy-args (fs)
  (if (endp fs) nil (cons (list (quote acl2::hons-copy) (car fs)) (hons-copy-args (cdr fs)))))

(defun memo-wrap (ds names)
  ;; (mv defuns memoize-events)
  (if (endp ds) (mv nil nil)
    (mv-let (rest mems) (memo-wrap (cdr ds) names)
      (let ((d (car ds)))
        (if (and (member-equal (defun-name d) names) (memo-measure d))
            (let* ((inner (gsym (concatenate 'string (defun-name d) "/%M")))
                   (formals (third d))
                   (entry (mk-defun-measure (second d) formals (memo-measure d)
                                            (cons inner (hons-copy-args formals)))))
              (mv (list* entry (list* 'defun inner (cddr d)) rest)
                  (cons (list (quote acl2::memoize) (list 'quote inner)) mems)))
          (mv (cons d rest) mems))))))

(defun clique-events (x ds cx)
  (if (not (is x "REC")) ds
    (let* ((mains0 (member-main-names (cdr x) cx))
           ;; multi-mode relations also have an R/SPLIT variant
           (mains (append mains0 (suffix-all mains0 "/SPLIT")))
           (in (reaching ds (intersection-equal mains (strip-defun-names ds)) (1+ (len ds))))
           (memo0 (rel-mangled-memo (cx-get :memo cx) cx))
           (memo (append memo0 (suffix-all memo0 "/SPLIT"))))
      (mv-let (outside inside) (split-clique ds in)
        (mv-let (inside mems) (memo-wrap inside memo)
          (append outside
                  (if (consp (cdr inside)) (list (cons 'mutual-recursion inside)) inside)
                  mems))))))

(defun override-events (ds)
  (if (endp ds) nil (cons (cons :%w1t-override (car ds)) (override-events (cdr ds)))))

(defun cform (x cx)
  (cond ((or (is x "GRAM") (and (is x "REC") (is (cadr x) "GRAM")))
         (mv-let (ds cx) (cgram-members (rel-members x) (cx-put :gram-rec (is x "REC") cx))
           (mv (clique-events x ds cx) nil nil (cx-put :gram-rec nil cx))))
        ((and (is x "REL") (assoc-equal (second x) (cx-get :rel-overrides cx)))
         ;; config :rel-override: hand-written defuns, emitted in place; the
         ;; relation keeps its :fun interface for callers
         (mv (override-events (cdr (assoc-equal (second x) (cx-get :rel-overrides cx))))
             nil nil
             (cx-put :modes (put-assoc-equal (second x) (cons :fun :fun) (cx-get :modes cx)) cx)))
        ((or (is x "REL") (and (is x "REC") (is (cadr x) "REL")))
         (mv-let (ds cx) (crel-form x cx)
           (mv (clique-events x ds cx) nil nil cx)))
        ((is x "REC")
         (mv-let (ds bs cx) (cmembers (cdr x) cx)
           (mv (clique-events x ds cx) bs nil cx)))
        (t (mv-let (ds bs cx) (cmember x cx) (mv ds bs nil cx)))))

(defun cforms (xs cx)
  (if (endp xs) (mv nil nil nil cx)
    (mv-let (e1 b1 s1 cx) (cform (car xs) cx)
      (mv-let (e2 b2 s2 cx) (cforms (cdr xs) cx)
        (mv (append e1 e2) (append b1 b2) (append s1 s2) cx)))))
