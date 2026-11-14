; Specialization of function-valued arguments (wasm3 prep P4, gap G1).
;
; A def with `def` parameters (3.0: $ivunop_(shape, def $f_(N, iN) : iN,
; vec_) and 15 more) is called only with constant function names
; ((def "fabs_") at every site). An IL pre-pass, before compilation:
;  - every call (call "f" ... (def "g") ...) of such an f whose function
;    arguments are all constants becomes (call "f.g" ...) without them;
;  - the def "f.g" is f with each function parameter p replaced by its
;    argument g: the binders (def p ...) and argument patterns (def p) are
;    removed, (call p ...) becomes (call g ...), and (def p) passed on to
;    another such def becomes (def g), which is specialized in turn;
;  - "f.g" is placed right before the first form that needs it (so g and
;    everything f calls already exist), its own needs before it;
;  - the unspecialized f is dropped: it cannot be compiled (it would call an
;    unknown function). Defs inside REC groups are left alone.
; Without such defs (WASM 1.0) the forms are returned unchanged.
(in-package "IL2ACL2")
(include-book "schema")
(program)

(defun sp-take-params (l)
  (if (and (consp l) (param-p (car l))) (cons (car l) (sp-take-params (cdr l))) nil))

(defun sp-def-param-names (ps)
  (cond ((endp ps) nil)
        ((is (car ps) "DEF") (cons (second (car ps)) (sp-def-param-names (cdr ps))))
        (t (sp-def-param-names (cdr ps)))))

(defun sp-ho-defs (forms)
  ;; ((id param-name ...) ...) for top-level defs with def parameters
  (cond ((endp forms) nil)
        ((is (car forms) "DEF")
         (let ((ns (sp-def-param-names (sp-take-params (cddr (car forms))))))
           (if ns (cons (cons (second (car forms)) ns) (sp-ho-defs (cdr forms)))
             (sp-ho-defs (cdr forms)))))
        (t (sp-ho-defs (cdr forms)))))

(defun sp-form-named (id forms)
  (cond ((endp forms) nil)
        ((and (is (car forms) "DEF") (equal (second (car forms)) id)) (car forms))
        (t (sp-form-named id (cdr forms)))))

; --- Substitution of function parameters ---------------------------------

(mutual-recursion
 (defun sp-subst (x s)
   (cond ((atom x) x)
         ((and (is x "CALL") (true-listp x) (stringp (second x)))
          (list* (car x)
                 (let ((hit (assoc-equal (second x) s))) (if hit (cdr hit) (second x)))
                 (sp-call-args (cddr x) s)))
         (t (sp-subst-list x s))))
 (defun sp-call-args (as s)
   (if (atom as) as
     (cons (let ((a (car as)))
             (if (and (is a "DEF") (true-listp a) (= (len a) 2) (assoc-equal (second a) s))
                 (list (car a) (cdr (assoc-equal (second a) s)))
               (sp-subst a s)))
           (sp-call-args (cdr as) s))))
 (defun sp-subst-list (l s)
   (cond ((atom l) l)
         ((and (is (car l) "DEF") (true-listp (car l)) (stringp (second (car l)))
               (assoc-equal (second (car l)) s))
          (sp-subst-list (cdr l) s))        ; a binder or an argument pattern
         (t (cons (sp-subst (car l) s) (sp-subst-list (cdr l) s))))))

; --- Call-site rewriting -------------------------------------------------

(defun sp-fn-args (as)
  ;; names of the (def "g") arguments, or :no if one is not a constant name
  (cond ((atom as) nil)
        ((is (car as) "DEF")
         (if (and (true-listp (car as)) (= (len (car as)) 2) (stringp (second (car as))))
             (let ((rest (sp-fn-args (cdr as))))
               (if (eq rest :no) :no (cons (second (car as)) rest)))
           :no))
        (t (sp-fn-args (cdr as)))))

(defun sp-drop-fn-args (as)
  (cond ((atom as) as)
        ((is (car as) "DEF") (sp-drop-fn-args (cdr as)))
        (t (cons (car as) (sp-drop-fn-args (cdr as))))))

(defun sp-join (f gs)
  (if (endp gs) f (sp-join (concatenate 'string f "." (car gs)) (cdr gs))))

; Rewrite x; (mv x' needs), needs = ((new-id f g ...) ...) in order of first use
(mutual-recursion
 (defun sp-rewrite (x ho needs)
   (cond ((atom x) (mv x needs))
         ((and (is x "CALL") (true-listp x) (stringp (second x)) (assoc-equal (second x) ho))
          (let ((gs (sp-fn-args (cddr x))))
            (if (or (eq gs :no) (null gs))
                (mv-let (as needs) (sp-rewrite-list (cddr x) ho needs)
                  (mv (list* (car x) (second x) as) needs))
              (let ((id (sp-join (second x) gs)))
                (mv-let (as needs) (sp-rewrite-list (sp-drop-fn-args (cddr x)) ho needs)
                  (mv (list* (car x) id as)
                      (if (assoc-equal id needs) needs
                        (append needs (list (list* id (second x) gs))))))))))
         (t (sp-rewrite-list x ho needs))))
 (defun sp-rewrite-list (l ho needs)
   (if (atom l) (mv l needs)
     (mv-let (a needs) (sp-rewrite (car l) ho needs)
       (mv-let (d needs) (sp-rewrite-list (cdr l) ho needs)
         (mv (cons a d) needs))))))

; Generate the specializations in needs that are not done yet, each after
; its own needs. (mv forms-in-order done)
(defun sp-generate (needs ho all done fuel)
  (cond ((or (endp needs) (zp fuel)) (mv nil done))
        ((member-equal (car (car needs)) done) (sp-generate (cdr needs) ho all done fuel))
        (t (let* ((n (car needs)) (id (car n)) (f (cadr n)) (gs (cddr n))
                  (callee (sp-form-named f all))
                  (s (pairlis$ (cdr (assoc-equal f ho)) gs))
                  (body (sp-subst callee s))
                  (body (list* (car body) id (cddr body)))
                  (done (cons id done)))
             (mv-let (body sub) (sp-rewrite body ho nil)
               (mv-let (pre done) (sp-generate sub ho all done (1- fuel))
                 (mv-let (rest done) (sp-generate (cdr needs) ho all done fuel)
                   (mv (append pre (list body) rest) done))))))))

(defun sp-forms (forms ho all done acc)
  ;; acc reversed output
  (cond ((endp forms) (mv (reverse acc) done))
        ((and (is (car forms) "DEF") (assoc-equal (second (car forms)) ho))
         (sp-forms (cdr forms) ho all done acc))      ; the unspecialized original
        (t (mv-let (x needs) (sp-rewrite (car forms) ho nil)
             (mv-let (pre done) (sp-generate needs ho all done 1000)
               (sp-forms (cdr forms) ho all done (cons x (revappend pre acc))))))))

; (mv forms' specialized-ids dropped-ids)
(defun specialize-fn-args (forms)
  (let ((ho (sp-ho-defs forms)))
    (if (null ho) (mv forms nil nil)
      (mv-let (out done) (sp-forms forms ho forms nil nil)
        (mv out (reverse done) (strip-cars ho))))))
