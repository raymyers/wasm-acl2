; T8 exit: a run-level theorem about the GENERATED semantics. For all 32-bit
; a, b, running  i32.const a; i32.const b; i32.add  with STEPS (the generated
; refl/trans closure of STEP, translated from 8-reduction.spectec) ends in
; i32.const ((a + b) mod 2^32). The WASM1 analog is proofs/proof-add-spec.lisp.
(in-package "W1T")
(include-book "../../gen/wasm1")
(local (include-book "arithmetic-5/top" :dir :system))

(defun i32c (n) (list :const '(:i32) n))
(defun u32p (x) (and (natp x) (< x (expt 2 32))))

; a fixed state: empty store, empty frame
(defconst *z*
  '(:|%;%| (:%rec (:funcs) (:globals) (:tables) (:mems))
           (:%rec (:locals) (:module :%rec (:types) (:funcs) (:globals) (:tables) (:mems) (:exports)))))

(defun cfg (instrs) (list :|%;%| *z* instrs))

; the i32.add result, kept opaque outside its own lemma
(defun add32 (a b) (mod (+ a b) (expt 2 32)))

(defthm u32p-of-add32
  (implies (and (u32p a) (u32p b)) (u32p (add32 a b))))

(in-theory (disable add32))

(program)
(set-state-ok t)

(defun read-forms-loop (channel acc state)
  (mv-let (eofp obj state) (read-object channel state)
    (if eofp (mv (reverse acc) state) (read-forms-loop channel (cons obj acc) state))))

(defun all-defuns (x)
  (cond ((atom x) nil)
        ((and (eq (car x) 'defun) (consp (cdr x)) (symbolp (cadr x)))
         (list (cons (cadr x) (caddr x))))
        (t (append (all-defuns (car x)) (all-defuns (cdr x))))))

(defun member-if-prefix (n prefixes)
  (and (consp prefixes)
       (or (and (<= (length (car prefixes)) (length n))
                (equal (subseq n 0 (length (car prefixes))) (car prefixes)))
           (member-if-prefix n (cdr prefixes)))))

(defun prefixed (ds prefixes)
  (cond ((endp ds) nil)
        ((let ((n (symbol-name (car (car ds)))))
           (member-if-prefix n prefixes))
         (cons (car ds) (prefixed (cdr ds) prefixes)))
        (t (prefixed (cdr ds) prefixes))))

(defun expand-hints (ds)
  (if (endp ds) nil
    (cons (list :free (cdr (car ds)) (cons (car (car ds)) (cdr (car ds))))
          (expand-hints (cdr ds)))))

; defthm with :expand hints for the generated search / step functions
(defmacro defthm-gen (name form &key (expand-prefixes '("STEP_PURE/SEARCH")) enable)
  `(make-event
    (mv-let (channel state) (open-input-channel "../../gen/wasm1.lisp" :object state)
      (mv-let (forms state) (read-forms-loop channel nil state)
        (let ((state (close-input-channel channel state)))
          (mv nil
              (list 'defthm ',name ',form
                    :hints (list (list "Goal" :in-theory '(enable ,@enable)
                                       :expand (expand-hints (prefixed (all-defuns forms) ',expand-prefixes)))))
              state))))))

(logic)

(defthm-gen step-pure-i32-add
  (implies (and (u32p a) (u32p b))
           (equal (step_pure (list (i32c a) (i32c b) '(:binop (:i32) (:add))))
                  (list (list (i32c (add32 a b))))))
  :enable (step_pure add32))

; one STEP performs the addition (rule Step/pure, the first rule)
(defthm-gen step-i32-add
  (implies (and (u32p a) (u32p b))
           (equal (step (cfg (list (i32c a) (i32c b) '(:binop (:i32) (:add)))))
                  (list (cfg (list (i32c (add32 a b)))))))
  :expand-prefixes ("STEP/SEARCH" "STEP_PURE/SEARCH")
  :enable (step add32))

; a single value does not step: no rule of Step applies
(defthm-gen step-of-value-is-stuck
  (implies (u32p v)
           (equal (step (cfg (list (i32c v)))) nil))
  :expand-prefixes ("STEP/SEARCH" "STEP_PURE/SEARCH" "STEP_READ/SEARCH")
  :enable (step step_pure step_read))

; the generated fuel loop of STEPS (refl/trans closure): opening lemmas
(defthm steps-fuel-stuck
  (implies (and (posp f) (not (step x)))
           (equal (steps/%fuel f x) (list x)))
  :hints (("Goal" :in-theory (disable step) :expand ((steps/%fuel f x)))))

(defthm steps-fuel-step
  (implies (and (posp f) (step x))
           (equal (steps/%fuel f x) (steps/%fuel (1- f) (car (step x)))))
  :hints (("Goal" :in-theory (disable step) :expand ((steps/%fuel f x)))))

(in-theory (disable steps/%fuel))

; the run-level theorem
(defthm steps-i32-add
  (implies (and (u32p a) (u32p b))
           (equal (steps (cfg (list (i32c a) (i32c b) '(:binop (:i32) (:add)))))
                  (list (cfg (list (i32c (add32 a b)))))))
  :hints (("Goal" :in-theory (e/d (steps %fuel) (step cfg add32 steps/%fuel i32c)))))
