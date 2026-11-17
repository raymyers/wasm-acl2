; License: MIT. See the file LICENSE at the top of the repository.
;
; First facts about the generated 3.0 step functions (plan/wasm-engine E4):
; a test that ACL2 can reason about them now that they are in logic mode
; and each rule is its own function (E2). Not yet the E4 library.
(in-package "WE")
(include-book "../../translate/gen/wasm-3.0/wasm3")

; 1. A whole step of the specification, for any state Z: `nop` alone.
;    STEP opens to its first rule, Step/pure, whose premise STEP_PURE is
;    run on the constant instruction list.
(defthm step-of-nop-alone
  (equal (w3t::step (list :|%;%| z '((:nop))))
         (list (list :|%;%| z nil)))
  :hints (("Goal" :in-theory (enable w3t::step w3t::step/r-pure))))

; The generated patterns test (TRUE-LISTP x) and (EQUAL (LEN x) k). Two
; facts about LEN turn these into the shape of x.
(defthm true-listp-len-0
  (implies (and (true-listp x) (equal (len x) 0))
           (equal x nil))
  :rule-classes :forward-chaining)

(defthm len-cdr-consp
  (implies (and (equal (len x) k) (posp k))
           (consp x))
  :rule-classes :forward-chaining)

; 2. Dispatch, one rule: Step_pure/drop fires only on `val drop`.
(defthm step_pure/r-drop-fires-only-on-val-drop
  (implies (w3t::step_pure/r-drop l)
           (and (equal (len l) 2)
                (w3t::val-p (car l))
                (equal (cadr l) '(:drop))))
  :hints (("Goal" :in-theory (enable w3t::step_pure/r-drop)))
  :rule-classes nil)

; 3. Dispatch, a rule with a premise: Step_pure/if-true.
(defthm step_pure/r-if-true-fires-only-on-const-if
  (implies (w3t::step_pure/r-if-true l)
           (and (equal (len l) 2)
                (equal (car (car l)) :const)
                (equal (car (cadr l)) :ifelse)))
  :hints (("Goal" :in-theory (enable w3t::step_pure/r-if-true)))
  :rule-classes nil)

; 4. A rule in its clean form: what Step_pure/if-true returns.
(defthm step_pure/r-if-true-clean
  (implies (and (natp c) (not (equal c 0))
                (true-listp is1) (true-listp is2))
           (equal (w3t::step_pure/r-if-true
                   (list (list :const '(:i32) c)
                         (list :ifelse bt is1 is2)))
                  (list (list (list :block bt is1)))))
  :hints (("Goal" :in-theory (enable w3t::step_pure/r-if-true)))
  :rule-classes nil)

; 5. A step under a label, for any state Z: STEP must find that no rule
;    before Step/ctxt-label fires on the one-element list (LABEL_ 0 () nop),
;    and then recur. The theory STEP-RULE-DEFS enables the definition of
;    every function of the step group (the relation functions, their rule
;    functions and helpers), so each earlier rule is opened and fails on
;    the shape of the instruction.
(defun step-group-name-p (name)
  (declare (xargs :mode :program))
  (and (symbolp name)
       (equal (symbol-package-name name) "W3T")
       (let ((s (symbol-name name)))
         (and (<= 4 (length s))
              (equal (subseq s 0 4) "STEP")))))

(defun step-group-defs (runes)
  (declare (xargs :mode :program))
  (cond ((endp runes) nil)
        ((and (consp (car runes))
              (eq (car (car runes)) :definition)
              (step-group-name-p (cadr (car runes))))
         (cons (car runes) (step-group-defs (cdr runes))))
        (t (step-group-defs (cdr runes)))))

(deftheory step-rule-defs
  (step-group-defs (function-theory :here)))

(defthm step-of-nop-under-a-label
  (equal (w3t::step (list :|%;%| z '((:label_%{%}% 0 nil ((:nop))))))
         (list (list :|%;%| z '((:label_%{%}% 0 nil nil)))))
  :hints (("Goal" :in-theory (enable step-rule-defs)
           ;; the functions of STEP's own clique are recursive, so they
           ;; are opened by name: STEP, the ctxt-instrs rule and its search
           :expand ((:free (c) (w3t::step c))
                    (:free (c) (w3t::step/r-ctxt-instrs c))
                    (:free (k lo hi a b z c) (w3t::step/search21 k lo hi a b z c))))))
