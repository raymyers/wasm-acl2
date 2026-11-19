; License: MIT. See the file LICENSE at the top of the repository.
;
; Contexts (plan/wasm-engine/plan2.md V3, items 3 and 4 and the exit): a
; step of the innermost block is a step of the whole configuration.
;   - STEP-UNDER-CTRL, the context lemma, by induction on the control stack:
;     if W3T::STEP of (store; frame; b) is (store'; frame'; b') and B is not
;     the body of an exit, then STEP of the configuration that ABS-CTRL builds
;     around B is the one it builds around B' with FRAME'. Each induction
;     step is STEP-OF-ADMIN-TERM-IN-BLOCK (rules/context.lisp).
;   - OP-STEP-SIMULATES: constraint C2 of E3 for OP-STEP under any control
;     stack, from OP-STEP-IS-STEP-OF-FLAT-BLOCK (op-flat.lisp).
; Label, handler and frame entries are in the same induction.
(in-package "WE")
(include-book "op-flat")
(include-book "../rules/context")

(set-prover-step-limit 2000000)

(in-theory (disable mv-nth value-head-p redex-arity try-rules apply-rule admin-term
                    abs-ctrl abs-ctrl-of-cons-entry ctrl-ok entry-ok))

; ABS-CTRL, one entry at a time, with the lists of rules/
(defthm abs-ctrl-when-not-consp
  (implies (not (consp ctrl))
           (equal (abs-ctrl ctrl cur fr) (mv cur fr)))
  :hints (("Goal" :in-theory (enable abs-ctrl))))

(defthm abs-ctrl-when-consp
  (implies (consp ctrl)
           (equal (abs-ctrl ctrl cur fr)
                  (abs-ctrl (cdr ctrl)
                            (append (revappend (entry-v (car ctrl)) nil)
                                    (cons (admin-term (entry-kind (car ctrl)) (entry-n (car ctrl))
                                                      (if (equal (entry-kind (car ctrl)) :f)
                                                          fr
                                                        (entry-x (car ctrl)))
                                                      cur)
                                          (entry-r (car ctrl))))
                            (if (equal (entry-kind (car ctrl)) :f) (entry-x (car ctrl)) fr))))
  :hints (("Goal" :in-theory (enable machine-lists) :expand ((abs-ctrl ctrl cur fr)))))

; what STEP-OF-ADMIN-TERM-IN-BLOCK asks of an entry
(defthm entry-of-car-ctrl-for-step
  (implies (and (ctrl-ok c) (consp c))
           (and (member-equal (entry-kind (car c)) '(:l :h :f))
                (vals-p (revappend (entry-v (car c)) nil))
                (implies (not (equal (entry-kind (car c)) :f))
                         (true-listp (entry-x (car c))))))
  :hints (("Goal" :in-theory (enable ctrl-ok entry-ok))))

; the block and the frame one entry further out
(defun abs-ctrl-induct (ctrl b fr s)
  (if (atom ctrl)
      (list b fr s)
    (let* ((e (car ctrl)) (k (entry-kind e)))
      (abs-ctrl-induct (cdr ctrl)
                       (append (revappend (entry-v e) nil)
                               (cons (admin-term k (entry-n e) (if (equal k :f) fr (entry-x e)) b)
                                     (entry-r e)))
                       (if (equal k :f) (entry-x e) fr)
                       s))))

; V3 item 3, the context lemma. The step of the block is named by its
; components, as in rules/flat.lisp.
(defthm step-under-ctrl
  (implies (and (ctrl-ok ctrl) (true-listp b) (not (exit-body-p b))
                (w3t::step (list :|%;%| (list :|%;%| s fr) b))
                (state-shape-p (cadr (car (w3t::step (list :|%;%| (list :|%;%| s fr) b))))))
           (equal (w3t::step (list :|%;%| (list :|%;%| s (mv-nth 1 (abs-ctrl ctrl b fr)))
                                   (mv-nth 0 (abs-ctrl ctrl b fr))))
                  (let* ((inner (w3t::step (list :|%;%| (list :|%;%| s fr) b)))
                         (s2 (cadr (cadr (car inner))))
                         (fr2 (caddr (cadr (car inner))))
                         (b2 (caddr (car inner))))
                    (list (list :|%;%| (list :|%;%| s2 (mv-nth 1 (abs-ctrl ctrl b2 fr2)))
                                (mv-nth 0 (abs-ctrl ctrl b2 fr2)))))))
  :hints (("Goal" :induct (abs-ctrl-induct ctrl b fr s))))

(in-theory (disable abs-ctrl-when-consp abs-ctrl-when-not-consp))

; V3 item 4 and the exit: C2 for OP-STEP under any control stack, for every
; opcode with rules
(defthm op-step-simulates
  (implies (and (machine-ok s)
                (not (admin-kind (car-t (ms-is s))))
                (not (sym-member (entry-kind (car-t (ms-is s))) '(:trap :throw_ref)))
                (equal (ms-status (op-step s)) :run))
           (equal (stepn 1 (machine-abs s))
                  (list (machine-abs (op-step s)))))
  :hints (("Goal" :in-theory (e/d (machine-abs rev-onto-becomes-revappend)
                                  (machine-abs-of-state-variable rev-onto sym-member
                                   step-under-ctrl))
                  :use (op-step-is-step-of-flat-block
                        op-instr-p-when-op-step-runs
                        (:instance step-under-ctrl
                                   (ctrl (ms-ctrl s)) (b (rev-onto (ms-vals s) (ms-is s)))
                                   (s (ms-store s)) (fr (ms-frame s)))
                        (:instance not-exit-body-p-when-block-steps
                                   (v (revappend (ms-vals s) nil)) (i (car (ms-is s)))
                                   (r (cdr (ms-is s)))
                                   (z (list :|%;%| (ms-store s) (ms-frame s)))))
                  :do-not-induct t)))
