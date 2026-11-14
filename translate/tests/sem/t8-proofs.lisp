; T8: theorems about the GENERATED semantics (logic-mode functions translated
; from the SpecTec rules), the analogs of WASM1's add-correct and
; div-by-zero-traps proofs. Each holds for all inputs.
;
; Step_pure rules that use the generic split search (trap-vals,
; br-zero, ...) are lifted into STEP_PURE/SEARCHn functions; the proofs
; expand all of them (names collected from gen/wasm1.lisp, so the hints do
; not depend on the generated numbering).
(in-package "W1T")
(include-book "../../gen/wasm1")
(local (include-book "arithmetic-5/top" :dir :system))

(defun i32c (n) (list :const '(:i32) n))

; numeric level: integer division / remainder by zero has no result (trap)
(defthm idiv-by-zero-has-no-result
  (equal ($idiv_ n sx a 0) nil))

(defthm irem-by-zero-has-no-result
  (equal ($irem_ n sx a 0) nil))

(program)
(set-state-ok t)

(defun read-forms-loop (channel acc state)
  (mv-let (eofp obj state) (read-object channel state)
    (if eofp (mv (reverse acc) state) (read-forms-loop channel (cons obj acc) state))))

(defun all-defuns (x)
  ;; (name . formals) of every defun inside x
  (cond ((atom x) nil)
        ((and (eq (car x) 'defun) (consp (cdr x)) (symbolp (cadr x)))
         (list (cons (cadr x) (caddr x))))
        (t (append (all-defuns (car x)) (all-defuns (cdr x))))))

(defun prefixed (ds prefix)
  (cond ((endp ds) nil)
        ((let ((n (symbol-name (car (car ds)))))
           (and (<= (length prefix) (length n)) (equal (subseq n 0 (length prefix)) prefix)))
         (cons (car ds) (prefixed (cdr ds) prefix)))
        (t (prefixed (cdr ds) prefix))))

(defun expand-hints (ds)
  (if (endp ds) nil
    (cons (list :free (cdr (car ds)) (cons (car (car ds)) (cdr (car ds))))
          (expand-hints (cdr ds)))))

(defmacro defthm-step-pure (name form)
  `(make-event
    (mv-let (channel state) (open-input-channel "../../gen/wasm1.lisp" :object state)
      (mv-let (forms state) (read-forms-loop channel nil state)
        (let ((state (close-input-channel channel state)))
          (mv nil
              (list 'defthm ',name ',form
                    :hints (list (list "Goal" :in-theory '(enable step_pure)
                                       :expand (expand-hints (prefixed (all-defuns forms) "STEP_PURE/SEARCH")))))
              state))))))

(logic)

; reduction level: Step_pure/binop-val for i32.add
(defthm-step-pure step-pure-i32-add
  (implies (and (natp a) (< a (expt 2 32)) (natp b) (< b (expt 2 32)))
           (equal (step_pure (list (i32c a) (i32c b) '(:binop (:i32) (:add))))
                  (list (list (i32c (mod (+ a b) (expt 2 32))))))))

; reduction level: Step_pure/binop-trap for i32.div_u by zero, for all a
(defthm-step-pure step-pure-i32-div-u-by-zero-traps
  (implies (and (natp a) (< a (expt 2 32)))
           (equal (step_pure (list (i32c a) (i32c 0) '(:binop (:i32) (:div (:u)))))
                  (list '((:trap))))))

; reduction level: select picks its first operand on a nonzero condition
(defthm-step-pure step-pure-select-nonzero
  (implies (and (natp a) (< a (expt 2 32)) (natp b) (< b (expt 2 32))
                (natp c) (< c (expt 2 32)) (not (equal c 0)))
           (equal (step_pure (list (i32c a) (i32c b) (i32c c) '(:select)))
                  (list (list (i32c a))))))
