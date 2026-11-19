; License: MIT. See the file LICENSE at the top of the repository.
;
; OP-STEP on the innermost block (plan/wasm-engine/plan2.md V2, item 4 and
; the exit): when OP-STEP applies a rule, W3T::STEP of the machine's block,
;   (store; frame; rev(vals) ++ is),
; is the block of the next state. With an empty control stack that block is
; MACHINE-ABS, so this is constraint C2 of E3 for those steps
; (OP-STEP-SIMULATES-FLAT). V3 lifts the same lemma through the control
; stack.
;
; The opcode enters through rules/flat.lisp only (STEP-OF-FLAT-BLOCK,
; TRY-RULES-ON-REDEX-IS-STEP), which has it from the per-relation lemmas of
; rules/dispatch.lisp: nothing here is per opcode.
;
; Excluded by hypothesis: a head TRAP or THROW_REF (V4: the rules on a whole
; block fire there) and an administrative term (MACHINE-STEP enters it).
(in-package "WE")
(include-book "clock0")
(include-book "../rules/flat")

(set-prover-step-limit 2000000)

(in-theory (disable mv-nth value-head-p redex-arity try-rules apply-rule))

; the machine's invariant says VAL-LIST-P; the lemmas about STEP say VALS-P
(defthm vals-p-when-val-list-p
  (implies (val-list-p l) (vals-p l))
  :hints (("Goal" :induct (len l) :in-theory (enable value-instr-p))))

(defthm ms-status-of-ms-with-status
  (equal (ms-status (ms-with-status st s)) st)
  :hints (("Goal" :in-theory (enable ms-with-status))))

; The block. The redex of OP-STEP, (rev-onto (take-n k vals) (list i)), is
; (operands k vals) ++ (i).
(defthm op-step-is-step-of-flat-block
  (implies (and (machine-ok s)
                (consp (ms-is s))
                (op-instr-p (car (ms-is s)))
                (equal (ms-status (op-step s)) :run))
           (and (equal (w3t::step (list :|%;%| (list :|%;%| (ms-store s) (ms-frame s))
                                        (rev-onto (ms-vals s) (ms-is s))))
                       (list (list :|%;%|
                                   (list :|%;%| (ms-store (op-step s)) (ms-frame (op-step s)))
                                   (rev-onto (ms-vals (op-step s)) (ms-is (op-step s))))))
                (equal (ms-ctrl (op-step s)) (ms-ctrl s))))
  :hints (("Goal" :in-theory (e/d (op-step ms-z machine-lists entry-kind-becomes-car
                                   car-t-of-drop-n nth-of-constant)
                                  (machine-abs-of-state-variable))
                  :use ((:instance step-of-flat-block
                                   (vals (ms-vals s)) (i (car (ms-is s))) (r (cdr (ms-is s)))
                                   (s (ms-store s)) (f (ms-frame s))
                                   (a (redex-arity (car (ms-is s))
                                                   (list :|%;%| (ms-store s) (ms-frame s))
                                                   (ms-vals s)))
                                   (inner (w3t::step
                                           (list :|%;%| (list :|%;%| (ms-store s) (ms-frame s))
                                                 (append (operands
                                                          (redex-arity (car (ms-is s))
                                                                       (list :|%;%| (ms-store s)
                                                                             (ms-frame s))
                                                                       (ms-vals s))
                                                          (ms-vals s))
                                                         (list (car (ms-is s)))))))))
                  :do-not-induct t)))

; An instruction on which OP-STEP applies a rule is an OP-INSTR-P, but for
; the heads MACHINE-STEP does not give it: a value's head has no rule.
(defthm no-rules-for-a-value-head
  (implies (or (value-head-p kw) (not kw))
           (equal (rules-for (list :op kw)) nil))
  :hints (("Goal" :in-theory (enable value-head-p (:e rules-for)))))

(defthm op-instr-p-when-op-step-runs
  (implies (and (equal (ms-status (op-step s)) :run)
                (not (admin-kind (car-t (ms-is s))))
                (not (sym-member (entry-kind (car-t (ms-is s))) '(:trap :throw_ref))))
           (op-instr-p (car (ms-is s))))
  :hints (("Goal" :in-theory (e/d (op-step op-instr-p admin-kind entry-kind machine-lists)
                                  (rules-for))
                  :use ((:instance no-rules-for-a-value-head (kw (car (car (ms-is s))))))
                  :do-not-induct t)))

(defthm consp-when-op-instr-p-of-car
  (implies (op-instr-p (car x)) (consp x))
  :hints (("Goal" :in-theory (enable op-instr-p)))
  :rule-classes :forward-chaining)

; C2 for OP-STEP with an empty control stack, for every opcode with rules
(defthm op-step-simulates-flat
  (implies (and (machine-ok s)
                (not (consp (ms-ctrl s)))
                (not (admin-kind (car-t (ms-is s))))
                (not (sym-member (entry-kind (car-t (ms-is s))) '(:trap :throw_ref)))
                (equal (ms-status (op-step s)) :run))
           (equal (stepn 1 (machine-abs s))
                  (list (machine-abs (op-step s)))))
  :hints (("Goal" :in-theory (e/d (machine-abs)
                                  (machine-abs-of-state-variable rev-onto sym-member))
                  :use (op-step-is-step-of-flat-block op-instr-p-when-op-step-runs)
                  :do-not-induct t)))
