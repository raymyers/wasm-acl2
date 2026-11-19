; License: MIT. See the file LICENSE at the top of the repository.
;
; Exits and propagation (plan/wasm-engine/plan2.md V4): constraint C2 of E3
; for the clock-1 steps of the list machine that are not the rule of an
; opcode with its operands under any head (machine/op-context.lisp):
;   - EXIT-STEP-SIMULATES: EXIT-STEP rebuilds the administrative term of the
;     innermost control entry and applies one of its rules;
;   - ANYPREFIX-STEP-SIMULATES: ANYPREFIX-STEP applies TRAP-INSTRS or
;     THROW_REF-INSTRS to the whole innermost block;
;   - OP-STEP-SIMULATES-THROW_REF-NULL: OP-STEP on THROW_REF with a null
;     reference on the operand stack.
; Each is a step of a block (rules/exits.lisp) lifted through the control
; stack by STEP-UNDER-CTRL: for EXIT-STEP the block is the one around the
; innermost entry, for the other two the innermost block.
(in-package "WE")
(include-book "op-context")
(include-book "../rules/exits")

(set-prover-step-limit 2000000)

(in-theory (disable mv-nth value-head-p redex-arity try-rules apply-rule admin-term
                    abs-ctrl abs-ctrl-of-cons-entry ctrl-ok entry-ok))

; STEP-UNDER-CTRL with the step of the block given by its components, as C2
(defthm stepn-1-under-ctrl
  (implies (and (ctrl-ok ctrl) (true-listp b) (not (exit-body-p b))
                (equal (w3t::step (list :|%;%| (list :|%;%| s fr) b))
                       (list (list :|%;%| (list :|%;%| s2 fr2) b2))))
           (equal (stepn 1 (list :|%;%| (list :|%;%| s (mv-nth 1 (abs-ctrl ctrl b fr)))
                                 (mv-nth 0 (abs-ctrl ctrl b fr))))
                  (list (list :|%;%| (list :|%;%| s2 (mv-nth 1 (abs-ctrl ctrl b2 fr2)))
                              (mv-nth 0 (abs-ctrl ctrl b2 fr2))))))
  :hints (("Goal" :use step-under-ctrl :in-theory (disable step-under-ctrl) :do-not-induct t))
  :rule-classes nil)

; A step of the innermost block that keeps the control stack is a step of the
; machine: S2 is the next state. The block steps, so it is not the body of an
; exit (rules/context.lisp).
(defthm block-step-simulates
  (implies (and (machine-ok s) (consp (ms-is s))
                (not (value-head-p (car (car (ms-is s)))))
                (equal (ms-ctrl s2) (ms-ctrl s))
                (equal (w3t::step (list :|%;%| (list :|%;%| (ms-store s) (ms-frame s))
                                        (append (revappend (ms-vals s) nil) (ms-is s))))
                       (list (list :|%;%| (list :|%;%| (ms-store s2) (ms-frame s2))
                                   (append (revappend (ms-vals s2) nil) (ms-is s2))))))
           (equal (stepn 1 (machine-abs s)) (list (machine-abs s2))))
  :hints (("Goal" :in-theory (e/d (machine-abs rev-onto-becomes-revappend)
                                  (machine-abs-of-state-variable rev-onto sym-member))
                  :use ((:instance stepn-1-under-ctrl
                                   (ctrl (ms-ctrl s)) (s (ms-store s)) (fr (ms-frame s))
                                   (b (append (revappend (ms-vals s) nil) (ms-is s)))
                                   (s2 (ms-store s2)) (fr2 (ms-frame s2))
                                   (b2 (append (revappend (ms-vals s2) nil) (ms-is s2))))
                        (:instance not-exit-body-p-when-block-steps
                                   (v (revappend (ms-vals s) nil)) (i (car (ms-is s)))
                                   (r (cdr (ms-is s)))
                                   (z (list :|%;%| (ms-store s) (ms-frame s)))))
                  :do-not-induct t))
  :rule-classes nil)

; V4 item 1 and the exit. The step is that of the block around the innermost
; entry, (entry-v e) ++ (term) ++ (entry-r e), in the frame outside the entry;
; that block is not the body of an exit, whatever the term's own body is.
; Nothing is asked of the block inside: any rule of the term that fires is
; STEP's.
(defthm exit-step-simulates
  (implies (and (machine-ok s)
                (consp (ms-ctrl s))
                (equal (ms-status (exit-step s)) :run))
           (equal (stepn 1 (machine-abs s))
                  (list (machine-abs (exit-step s)))))
  :hints (("Goal" :in-theory (e/d (machine-abs exit-step rev-onto-becomes-revappend machine-lists
                                   abs-ctrl-when-consp car-t-of-drop-n nth-of-constant)
                                  (machine-abs-of-state-variable rev-onto sym-member))
                  :use ((:instance stepn-1-under-ctrl
                                   (ctrl (cdr (ms-ctrl s)))
                                   (s (ms-store s))
                                   (fr (if (equal (entry-kind (car (ms-ctrl s))) :f)
                                           (entry-x (car (ms-ctrl s)))
                                         (ms-frame s)))
                                   (b (append (revappend (entry-v (car (ms-ctrl s))) nil)
                                              (cons (admin-term
                                                     (entry-kind (car (ms-ctrl s)))
                                                     (entry-n (car (ms-ctrl s)))
                                                     (if (equal (entry-kind (car (ms-ctrl s))) :f)
                                                         (ms-frame s)
                                                       (entry-x (car (ms-ctrl s))))
                                                     (revappend (ms-vals s) (ms-is s)))
                                                    (entry-r (car (ms-ctrl s))))))
                                   (s2 (ms-store (exit-step s)))
                                   (fr2 (ms-frame (exit-step s)))
                                   (b2 (revappend (ms-vals (exit-step s)) (ms-is (exit-step s)))))
                        (:instance step-of-exit-term
                                   (k (entry-kind (car (ms-ctrl s))))
                                   (n (entry-n (car (ms-ctrl s))))
                                   (x (if (equal (entry-kind (car (ms-ctrl s))) :f)
                                          (ms-frame s)
                                        (entry-x (car (ms-ctrl s)))))
                                   (b (revappend (ms-vals s) (ms-is s)))
                                   (v (revappend (entry-v (car (ms-ctrl s))) nil))
                                   (r (entry-r (car (ms-ctrl s))))
                                   (z (list :|%;%| (ms-store s)
                                            (if (equal (entry-kind (car (ms-ctrl s))) :f)
                                                (entry-x (car (ms-ctrl s)))
                                              (ms-frame s))))
                                   (tr (try-rules
                                        (rules-for (list :entry (entry-kind (car (ms-ctrl s)))))
                                        (list :|%;%| (ms-store s)
                                              (if (equal (entry-kind (car (ms-ctrl s))) :f)
                                                  (entry-x (car (ms-ctrl s)))
                                                (ms-frame s)))
                                        (list (admin-term
                                               (entry-kind (car (ms-ctrl s)))
                                               (entry-n (car (ms-ctrl s)))
                                               (if (equal (entry-kind (car (ms-ctrl s))) :f)
                                                   (ms-frame s)
                                                 (entry-x (car (ms-ctrl s))))
                                               (revappend (ms-vals s) (ms-is s))))))))
                  :do-not-induct t)))

; V4 item 2 and the exit. The head of the block's instructions is TRAP or
; THROW_REF, as MACHINE-STEP has it when it calls ANYPREFIX-STEP.
(defthm anyprefix-step-simulates
  (implies (and (machine-ok s)
                (sym-member (entry-kind (car-t (ms-is s))) '(:trap :throw_ref))
                (equal (ms-status (anyprefix-step s)) :run))
           (equal (stepn 1 (machine-abs s))
                  (list (machine-abs (anyprefix-step s)))))
  :hints (("Goal" :in-theory (e/d (anyprefix-step ms-z machine-lists entry-kind-becomes-car
                                   rev-onto-becomes-revappend car-t-of-drop-n nth-of-constant)
                                  (machine-abs-of-state-variable))
                  :use ((:instance block-step-simulates (s2 (anyprefix-step s)))
                        (:instance step-of-block-rule
                                   (vals (ms-vals s)) (i (car (ms-is s))) (r (cdr (ms-is s)))
                                   (z (list :|%;%| (ms-store s) (ms-frame s)))))
                  :do-not-induct t)))

; V4 item 3: the head that OP-STEP-SIMULATES excludes and MACHINE-STEP gives
; to OP-STEP, THROW_REF with a null reference on the operand stack.
(defthm op-step-simulates-throw_ref-null
  (implies (and (machine-ok s)
                (equal (entry-kind (car-t (ms-is s))) :throw_ref)
                (equal (entry-kind (car-t (ms-vals s))) :ref.null_addr)
                (equal (ms-status (op-step s)) :run))
           (equal (stepn 1 (machine-abs s))
                  (list (machine-abs (op-step s)))))
  :hints (("Goal" :in-theory (e/d (op-step ms-z machine-lists entry-kind-becomes-car redex-arity
                                   rev-onto-becomes-revappend car-t-of-drop-n nth-of-constant
                                   (:e rules-for))
                                  (machine-abs-of-state-variable take-of-1))
                  :use ((:instance block-step-simulates (s2 (op-step s)))
                        (:instance try-rules-on-null-throw_ref-is-step
                                   (vals (ms-vals s)) (i (car (ms-is s)))
                                   (z (list :|%;%| (ms-store s) (ms-frame s)))
                                   (tr (try-rules (rules-for '(:op :throw_ref))
                                                  (list :|%;%| (ms-store s) (ms-frame s))
                                                  (append (operands 1 (ms-vals s))
                                                          (list (car (ms-is s)))))))
                        (:instance step-of-null-throw_ref-block
                                   (vals (ms-vals s)) (i (car (ms-is s))) (r (cdr (ms-is s)))
                                   (z (list :|%;%| (ms-store s) (ms-frame s)))
                                   (inner (w3t::step
                                           (list :|%;%| (list :|%;%| (ms-store s) (ms-frame s))
                                                 (append (operands 1 (ms-vals s))
                                                         (list (car (ms-is s)))))))))
                  :do-not-induct t)))
