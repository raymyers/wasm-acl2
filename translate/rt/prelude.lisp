; Hand-written runtime support for the generated W1T semantics (plan §3).
; Names start with % so they can never clash with generated names.
;
; Records are encoded (:%REC (:FIELD . value) ...) with fields in declaration
; order (plan §2.2).
(in-package "W1T")

(defun %get-field (r k)
  (declare (xargs :guard t))
  (if (and (consp r) (alistp (cdr r)))
      (cdr (assoc-equal k (cdr r)))
    nil))

(defun %put-field (r k v)
  (declare (xargs :guard t))
  (if (and (consp r) (alistp (cdr r)))
      (cons (car r) (put-assoc-equal k v (cdr r)))
    r))

; SpecTec record/list composition (il/eval.ml CompE): lists append, an
; empty option yields the other side, records compose field by field.
(defun %rec-p (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :%rec) (alistp (cdr x))))

(defun %comp-fields (f1 f2)
  (declare (xargs :guard (and (alistp f1) (alistp f2))))
  (if (endp f1)
      nil
    (cons (cons (caar f1)
                (let ((a (cdar f1)) (b (cdr (assoc-equal (caar f1) f2))))
                  (if (and (true-listp a) (true-listp b)) (append a b) a)))
          (%comp-fields (cdr f1) f2))))

(defun %comp (a b)
  (declare (xargs :guard t))
  (cond ((and (%rec-p a) (%rec-p b)) (cons :%rec (%comp-fields (cdr a) (cdr b))))
        ((and (true-listp a) (true-listp b)) (append a b))
        (t a)))

; (%try-logic EVENT): admit EVENT (a defun or mutual-recursion) in logic mode
; if ACL2 accepts it -- termination via ACL2's default measures, guards not
; verified -- and otherwise in program mode. Deterministic for a given ACL2.
(defun %program-defun (d)
  (declare (xargs :guard t))
  (if (and (true-listp d) (eq (car d) 'defun) (consp (cdr d)) (consp (cddr d)))
      (list* 'defun (cadr d) (caddr d)
             '(declare (xargs :mode :program))
             (cdddr d))
    d))

(defun %program-defuns (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil
    (cons (%program-defun (car ds)) (%program-defuns (cdr ds)))))

(defun %program-version (ev)
  (declare (xargs :guard t))
  (if (and (consp ev) (eq (car ev) 'mutual-recursion))
      (cons 'mutual-recursion (%program-defuns (cdr ev)))
    (%program-defun ev)))

; The logic attempt uses :ruler-extenders :all (generated recursive calls sit
; inside let*/and, which the default rulers do not see through) and is
; bounded by a prover step limit (deterministic, unlike a time limit), so a
; hard termination proof falls back instead of hanging.
(defun %logic-defun (d)
  (declare (xargs :guard t))
  (if (and (true-listp d) (eq (car d) 'defun) (consp (cdr d)) (consp (cddr d)))
      (list* 'defun (cadr d) (caddr d)
             '(declare (xargs :ruler-extenders :all))
             (cdddr d))
    d))

(defun %logic-defuns (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (cons (%logic-defun (car ds)) (%logic-defuns (cdr ds)))))

(defun %logic-version (ev)
  (declare (xargs :guard t))
  (if (and (consp ev) (eq (car ev) 'mutual-recursion))
      (cons 'mutual-recursion (%logic-defuns (cdr ev)))
    (%logic-defun ev)))

; Second logic alternative: prove termination in ACL2's ground-zero theory,
; so the prover does not open (large) generated callees; parser loop
; measures only need the generated progress checks about len.
(defun %gz-defun (d)
  (declare (xargs :guard t))
  (if (and (true-listp d) (eq (car d) 'defun) (consp (cdr d)) (consp (cddr d)))
      (list* 'defun (cadr d) (caddr d)
             '(declare (xargs :ruler-extenders :all
                              :hints (("Goal" :in-theory (theory 'acl2::ground-zero)))))
             (cdddr d))
    d))

(defun %gz-defuns (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (cons (%gz-defun (car ds)) (%gz-defuns (cdr ds)))))

(defun %gz-version (ev)
  (declare (xargs :guard t))
  (if (and (consp ev) (eq (car ev) 'mutual-recursion))
      (cons 'mutual-recursion (%gz-defuns (cdr ev)))
    (%gz-defun ev)))

(defmacro %try-logic (ev)
  `(make-event '(:or (with-prover-step-limit 200000 ,(%logic-version ev))
                     (with-prover-step-limit 200000 ,(%gz-version ev))
                     ,(%program-version ev))))

; Step bound for closure relations (Steps): R(x) iterates the step relation
; at most (%FUEL) times and has no result if the bound is reached.
(defun %fuel () (declare (xargs :guard t)) 1000000)

; (%try-guards f): verify the guards of F (and its clique) if ACL2 can, within
; a prover step limit; otherwise leave them unverified. Deterministic.
(defmacro %try-guards (name)
  `(make-event '(:or (with-prover-step-limit 100000 (verify-guards ,name))
                     (value-triple :guards-not-verified))))
