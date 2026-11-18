; License: MIT. See the file LICENSE at the top of the repository.
;
; T1, the theorem of the list machine (plan/wasm-engine/plan2.md V5, items 1
; and 2): when MACHINE-RUN ends with a result, the specification's
; STEPS/%FUEL, started from the abstraction of the first state with enough
; fuel, returns the abstraction of the last state.
;   - MACHINE-STEP-SIMULATES: constraint C2 of E3 for every running state
;     with the invariant. A step of clock 0 keeps MACHINE-ABS (clock0.lisp).
;     A step of clock 1 is, by the case split of MACHINE-STEP
;     (MACHINE-STEP-CLOCK-1-CASES), one of EXIT-STEP, ANYPREFIX-STEP and
;     OP-STEP under the hypotheses of the four step theorems of
;     op-context.lisp and exit-steps.lisp.
;   - MACHINE-RESULT-IS-SPEC-RESULT: ENGINE-RESULT-IS-SPEC-RESULT
;     (theorem/simulation.lisp) for the six functions of the machine, with C1
;     (ok.lisp), C2, C3 (terminal-ok.lisp) and C4.
; No opcode is named here and none is excluded: the clock is 1 for every
; instruction that is not a value and not an administrative term, the bulk
; memory instructions included (their rules rewrite to smaller instructions,
; one spec step each).
(in-package "WE")
(include-book "exit-steps")
(include-book "terminal-ok")

(set-prover-step-limit 2000000)

(in-theory (disable mv-nth value-head-p redex-arity try-rules apply-rule admin-term
                    abs-ctrl abs-ctrl-of-cons-entry ctrl-ok entry-ok))

; The clock, and the step of a state whose clock is 1.
(defthm machine-clock-is-0-or-1
  (or (equal (machine-clock s) 0) (equal (machine-clock s) 1))
  :hints (("Goal" :in-theory (enable machine-clock)))
  :rule-classes nil)

(defthm machine-step-runs-when-clock-1
  (implies (equal (machine-clock s) 1)
           (and (equal (ms-status s) :run)
                (equal (ms-status (machine-step s)) :run)))
  :hints (("Goal" :in-theory (enable machine-clock)))
  :rule-classes nil)

; The case split of MACHINE-STEP, in its order: each disjunct is a step
; function with the tests MACHINE-STEP made before it called it, which are
; the hypotheses of that function's step theorem.
(defthm machine-step-clock-1-cases
  (implies (and (equal (ms-status s) :run)
                (equal (machine-clock s) 1))
           (or (and (consp (ms-ctrl s))
                    (equal (machine-step s) (exit-step s)))
               (and (equal (entry-kind (car-t (ms-is s))) :throw_ref)
                    (equal (entry-kind (car-t (ms-vals s))) :ref.null_addr)
                    (equal (machine-step s) (op-step s)))
               (and (sym-member (entry-kind (car-t (ms-is s))) '(:trap :throw_ref))
                    (equal (machine-step s) (anyprefix-step s)))
               (and (not (admin-kind (car-t (ms-is s))))
                    (not (sym-member (entry-kind (car-t (ms-is s))) '(:trap :throw_ref)))
                    (equal (machine-step s) (op-step s)))))
  :hints (("Goal" :in-theory (enable machine-step machine-clock)))
  :rule-classes nil)

(in-theory (disable machine-step machine-clock machine-running machine-result-p))

(defthm machine-clock-1-simulates
  (implies (and (machine-ok s) (equal (machine-clock s) 1))
           (equal (stepn 1 (machine-abs s))
                  (list (machine-abs (machine-step s)))))
  :hints (("Goal" :use (machine-step-clock-1-cases machine-step-runs-when-clock-1
                        exit-step-simulates anyprefix-step-simulates
                        op-step-simulates-throw_ref-null op-step-simulates)
                  :in-theory (disable exit-step-simulates anyprefix-step-simulates
                                      op-step-simulates-throw_ref-null op-step-simulates
                                      machine-abs-of-state-variable stepn
                                      sym-member (:e sym-member))
                  :do-not-induct t))
  :rule-classes nil)

; C2 of E3 for the list machine
(defthm machine-step-simulates
  (implies (and (machine-ok s) (machine-running s))
           (equal (stepn (machine-clock s) (machine-abs s))
                  (list (machine-abs (machine-step s)))))
  :hints (("Goal" :use (machine-clock-is-0-or-1 machine-clock-0-simulates
                        machine-clock-1-simulates)
                  :in-theory (disable machine-clock-0-simulates machine-clock-0-keeps-abs
                                      machine-abs-of-state-variable stepn)
                  :do-not-induct t)))

; C4 of E3 for the list machine
(defthm machine-result-not-running
  (implies (machine-result-p s)
           (not (machine-running s)))
  :hints (("Goal" :in-theory (enable machine-result-p machine-running))))

; The spec steps that a run of N machine steps stands for (E3's M-CLOCKS).
(defun machine-clocks (n s)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (or (zp n) (not (machine-running s)))
      0
    (+ (machine-clock s) (machine-clocks (1- n) (machine-step s)))))

; T1 (plan2.md section 1)
(defthm machine-result-is-spec-result
  (implies (and (machine-ok s)
                (machine-result-p (machine-run n s))
                (natp fuel)
                (< (machine-clocks n s) fuel))
           (equal (w3t::steps/%fuel fuel (machine-abs s))
                  (list (machine-abs (machine-run n s)))))
  :hints (("Goal" :use ((:functional-instance engine-result-is-spec-result
                                              (m-ok machine-ok)
                                              (m-running machine-running)
                                              (m-result-p machine-result-p)
                                              (m-step machine-step)
                                              (m-abs machine-abs)
                                              (m-clock machine-clock)
                                              (m-run machine-run)
                                              (m-clocks machine-clocks)))
                  :in-theory (disable machine-abs-of-state-variable))))

(in-theory (disable machine-clocks machine-run))
