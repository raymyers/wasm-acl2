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

(defmacro %try-logic (ev)
  `(make-event '(:or ,ev ,(%program-version ev))))
