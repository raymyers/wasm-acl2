; License: MIT. See the file LICENSE at the top of the repository.
;
; V8 of plan/wasm-engine/plan2.md, item 3: what a run of the fast machine
; that stops :unsupported stands for. A driver with host functions (TeX,
; plan2.md P1) calls FAST-RUN, which stops :unsupported at a call_ref of a
; host function; the driver sets the status back to :run, makes the host
; step itself and calls FAST-RUN again. T2 says nothing of such a stretch:
; its hypothesis is a result. Here:
;   - FAST-STEP-WHEN-REFUSED: a step that ends :unsupported changes the
;     status and nothing else, whatever the reason of the refusal;
;   - FAST-RUN-RESUMED: so the stobj of a run that ended :unsupported, with
;     its status set back to :run, is the stobj after the steps the run took
;     before the refused one (FAST-SUPPORTED-STEPS of them);
;   - FAST-STRETCH-IS-SPEC-STEPS: that stobj has the invariant, and the
;     configuration it stands for is the one the specification reaches from
;     the configuration of the first stobj in exactly MACHINE-CLOCKS steps
;     (STEPN, theorem/simulation.lisp);
;   - FAST-RUN-IS-SPEC-STEPS: the same for a run that does not end
;     :unsupported (it ended with a result, :stuck, or its fuel);
;   - FAST-RUN-FUEL: FAST-RUN that also returns the fuel it did not use, for
;     a driver that counts steps;
;   - FM-INV-CHECK: FM-INV without building the list state (MACHINE-OK does
;     not read the store), for a driver that checks the invariant often.
; Nothing here is about a host step: what the driver does to the stobj
; between two stretches is outside every theorem (plan2.md P1).
;
; Normal forms: those of inv.lisp. A field of the stobj is (NTH k FM).
(in-package "WE")
(include-book "spec-result")

(set-prover-step-limit 2000000)

; REDEX-ARITY-WHEN-HEAD-NOT-SUPPORTED (../machine/opcodes.lisp) is tried at
; every REDEX-ARITY and opens the value predicates: 1,911,587 prover steps
; for FAST-OP-STEP-WHEN-REFUSED with it, 40,543 without.
(local (in-theory (disable redex-arity-when-head-not-supported
                           fallback-shape-ok put-z-bytes mem0-of-store)))

; ---------------------------------------------------------------------------
; 1. A rule that does not fire, or is refused, leaves the stobj

(defthm fast-apply-fallback-stobj-when-not-fired
  (implies (or (not (mv-nth 0 (fast-apply-fallback fn z redex fm)))
               (equal (mv-nth 0 (fast-apply-fallback fn z redex fm)) :refuse))
           (equal (mv-nth 3 (fast-apply-fallback fn z redex fm)) fm))
  :hints (("Goal" :in-theory (enable fast-apply-fallback))))

(defthm fast-apply-rule-stobj-when-not-fired
  (implies (or (not (mv-nth 0 (fast-apply-rule fn z redex fm)))
               (equal (mv-nth 0 (fast-apply-rule fn z redex fm)) :refuse))
           (equal (mv-nth 3 (fast-apply-rule fn z redex fm)) fm))
  :hints (("Goal" :in-theory (enable fast-apply-rule))))

(defthm fast-try-rules-stobj-when-refused
  (implies (equal (mv-nth 0 (fast-try-rules rules z redex fm)) :refuse)
           (equal (mv-nth 3 (fast-try-rules rules z redex fm)) fm))
  :hints (("Goal" :induct (fast-try-rules rules z redex fm)
                  :in-theory (enable fast-try-rules))))

; ---------------------------------------------------------------------------
; 2. A step that ends :unsupported changes only the status

(defthm fast-op-step-when-refused
  (implies (and (equal (fm-status fm) :run)
                (equal (fm-status (fast-op-step fm)) :unsupported))
           (equal (fast-op-step fm) (update-fm-status :unsupported fm)))
  :hints (("Goal" :in-theory (e/d (fast-op-step)
                                  (fast-try-op op-has-rules rules-for op-has-rules-is-rules-for))
                  :do-not-induct t)))

(defthm fast-exit-step-when-refused
  (implies (and (equal (fm-status fm) :run)
                (sym-member (entry-kind (car (fm-ctrl fm))) '(:l :h :f))
                (equal (fm-status (fast-exit-step fm)) :unsupported))
           (equal (fast-exit-step fm) (update-fm-status :unsupported fm)))
  :hints (("Goal" :in-theory (e/d (fast-exit-step) (fast-try-entry rules-for))
                  :do-not-induct t)))

(defthm fast-anyprefix-step-when-refused
  (implies (and (equal (fm-status fm) :run)
                (equal (fm-status (fast-anyprefix-step fm)) :unsupported))
           (equal (fast-anyprefix-step fm) (update-fm-status :unsupported fm)))
  :hints (("Goal" :in-theory (e/d (fast-anyprefix-step)
                                  (fast-try-anyprefix rules-for (:e rules-for)))
                  :do-not-induct t)))

; entering an administrative term is never refused
(defthm fast-enter-step-is-not-refused
  (implies (equal (nth *fm-status* fm) :run)
           (not (equal (nth *fm-status* (fast-enter-step fm)) :unsupported)))
  :hints (("Goal" :in-theory (e/d (fast-enter-step) (enterable-p admin-kind)))))

(defthm fast-step-when-refused
  (implies (and (fmp fm)
                (ctrl-kinds-ok (fm-ctrl fm))
                (equal (fm-status fm) :run)
                (equal (fm-status (fast-step fm)) :unsupported))
           (equal (fast-step fm) (update-fm-status :unsupported fm)))
  :hints (("Goal" :in-theory (e/d (fast-step) (fast-val-p exit-instr-p admin-kind ctrl-kinds-ok
                                               (:e sym-member)))
                  :do-not-induct t)))

; the same for a state that is not :unsupported already: it was running
(defthm fast-step-when-refused-and-not-unsupported
  (implies (and (fmp fm)
                (ctrl-kinds-ok (fm-ctrl fm))
                (not (equal (nth *fm-status* fm) :unsupported))
                (equal (fm-status (fast-step fm)) :unsupported))
           (and (equal (nth *fm-status* fm) :run)
                (equal (fast-step fm) (update-nth *fm-status* :unsupported fm))))
  :hints (("Goal" :use (fast-step-when-refused fast-step-when-not-running)
                  :in-theory (disable fast-step-when-refused fast-step-when-not-running)))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; 3. The steps of a run before the one that is refused

(defun-nx fast-supported-steps (n fm)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n)
          (not (equal (fm-status fm) :run))
          (equal (fm-status (fast-step fm)) :unsupported))
      0
    (+ 1 (fast-supported-steps (- n 1) (fast-step fm)))))

(defthm fast-run-supported-of-fast-supported-steps
  (fast-run-supported (fast-supported-steps n fm) fm)
  :hints (("Goal" :induct (fast-supported-steps n fm)
                  :in-theory (enable fast-run-supported))))

(defthm fast-supported-run-is-not-unsupported
  (implies (not (equal (fm-status fm) :unsupported))
           (not (equal (nth *fm-status* (fast-run (fast-supported-steps n fm) fm)) :unsupported)))
  :hints (("Goal" :induct (fast-supported-steps n fm)
                  :in-theory (enable fast-run))))

; a run that ends :unsupported is those steps and then the refused one
(defthm fast-run-is-refused-step-after-supported-steps
  (implies (and (equal (fm-status (fast-run n fm)) :unsupported)
                (not (equal (fm-status fm) :unsupported)))
           (equal (fast-run n fm)
                  (fast-step (fast-run (fast-supported-steps n fm) fm))))
  :hints (("Goal" :induct (fast-supported-steps n fm)
                  :in-theory (enable fast-run)))
  :rule-classes nil)

(in-theory (disable fast-supported-steps))

; those steps are the list machine's, and keep the invariant
(defthm fast-supported-run-is-machine-run
  (implies (fm-inv fm)
           (and (equal (fm->ms (fast-run (fast-supported-steps n fm) fm))
                       (machine-run (fast-supported-steps n fm) (fm->ms fm)))
                (fm-inv (fast-run (fast-supported-steps n fm) fm))))
  :hints (("Goal" :use ((:instance fast-run-is-machine-run-when-supported
                                   (n (fast-supported-steps n fm))))
                  :in-theory (disable fast-run-is-machine-run-when-supported))))

(defthm fmp-when-fm-inv
  (implies (fm-inv fm)
           (fmp fm))
  :hints (("Goal" :in-theory (enable fm-inv))))

(defthm ctrl-kinds-ok-when-fm-inv
  (implies (fm-inv fm)
           (ctrl-kinds-ok (nth *fm-ctrl* fm)))
  :hints (("Goal" :in-theory (enable fm-inv))))

(defthm fast-run-when-refused
  (implies (and (fm-inv fm)
                (not (equal (fm-status fm) :unsupported))
                (equal (fm-status (fast-run n fm)) :unsupported))
           (and (equal (fm-status (fast-run (fast-supported-steps n fm) fm)) :run)
                (equal (fast-run n fm)
                       (update-fm-status :unsupported
                                         (fast-run (fast-supported-steps n fm) fm)))))
  :hints (("Goal" :use (fast-run-is-refused-step-after-supported-steps
                        (:instance fast-step-when-refused-and-not-unsupported
                                   (fm (fast-run (fast-supported-steps n fm) fm))))
                  :do-not-induct t))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; 4. The stretch: a run that ends :unsupported, resumed

(defthm update-status-of-update-status
  (implies (and (fmp fm) (equal (nth *fm-status* fm) st))
           (equal (update-nth *fm-status* st (update-nth *fm-status* st2 fm)) fm))
  :hints (("Goal" :in-theory (enable fmp update-nth nth len))))

; the driver's resuming: the status set back to :run gives the stobj after
; the supported steps
(defthm fast-run-resumed
  (implies (and (fm-inv fm)
                (not (equal (fm-status fm) :unsupported))
                (equal (fm-status (fast-run n fm)) :unsupported))
           (equal (update-fm-status :run (fast-run n fm))
                  (fast-run (fast-supported-steps n fm) fm)))
  :hints (("Goal" :use (fast-run-when-refused fast-supported-run-is-machine-run)
                  :in-theory (disable fast-supported-run-is-machine-run
                                      update-nth-update-nth-same)
                  :do-not-induct t))
  :rule-classes nil)

; The list machine's run is so many steps of the specification, result or
; not: M-RUN-SIMULATES of theorem/simulation.lisp for the list machine, as
; T1 is ENGINE-RESULT-IS-SPEC-RESULT for it.
(defthm machine-run-is-spec-steps
  (implies (machine-ok s)
           (equal (stepn (machine-clocks n s) (machine-abs s))
                  (list (machine-abs (machine-run n s)))))
  :hints (("Goal" :use ((:functional-instance m-run-simulates
                                              (m-ok machine-ok)
                                              (m-running machine-running)
                                              (m-result-p machine-result-p)
                                              (m-step machine-step)
                                              (m-abs machine-abs)
                                              (m-clock machine-clock)
                                              (m-run machine-run)
                                              (m-clocks machine-clocks)))
                  :in-theory (e/d (machine-run machine-clocks)
                                  (machine-abs-of-state-variable stepn)))))

; The claim for a stretch that stopped :unsupported (at a host call, or at
; anything else the fast machine refuses). K is FAST-SUPPORTED-STEPS.
(defthm fast-stretch-is-spec-steps
  (implies (and (fm-inv fm)
                (not (equal (fm-status fm) :unsupported))
                (equal (fm-status (fast-run n fm)) :unsupported))
           (and (fm-inv (update-fm-status :run (fast-run n fm)))
                (equal (stepn (machine-clocks (fast-supported-steps n fm) (fm->ms fm))
                              (machine-abs (fm->ms fm)))
                       (list (machine-abs (fm->ms (update-fm-status :run (fast-run n fm))))))))
  :hints (("Goal" :use (fast-run-resumed
                        fast-supported-run-is-machine-run
                        (:instance machine-run-is-spec-steps
                                   (n (fast-supported-steps n fm)) (s (fm->ms fm))))
                  :in-theory (disable fast-supported-run-is-machine-run machine-run-is-spec-steps
                                      machine-abs stepn update-fm-status
                                      machine-abs-of-state-variable)
                  :do-not-induct t))
  :rule-classes nil)

; The claim for a stretch that did not stop :unsupported.
(defthm fast-run-is-spec-steps
  (implies (and (fm-inv fm)
                (not (equal (fm-status (fast-run n fm)) :unsupported)))
           (equal (stepn (fast-clocks n fm) (machine-abs (fm->ms fm)))
                  (list (machine-abs (fm->ms (fast-run n fm))))))
  :hints (("Goal" :use ((:instance machine-run-is-spec-steps (s (fm->ms fm))))
                  :in-theory (e/d (fast-clocks)
                                  (machine-run-is-spec-steps machine-abs stepn
                                   machine-abs-of-state-variable))
                  :do-not-induct t))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; 5. FAST-RUN with the fuel that is left

(defun fast-run-fuel (n fm)              ; (mv fuel-left fm)
  (declare (xargs :stobjs fm :guard (natp n) :measure (nfix n)))
  (if (or (zp n) (not (eq (fm-status fm) :run))) (mv n fm)
    (let ((fm (fast-step fm))) (fast-run-fuel (1- n) fm))))

(defthm fast-run-fuel-is-fast-run
  (equal (mv-nth 1 (fast-run-fuel n fm))
         (fast-run n fm))
  :hints (("Goal" :induct (fast-run-fuel n fm)
                  :in-theory (enable fast-run))))

(defthm fuel-left-of-fast-run-fuel
  (implies (natp n)
           (and (natp (mv-nth 0 (fast-run-fuel n fm)))
                (<= (mv-nth 0 (fast-run-fuel n fm)) n)))
  :hints (("Goal" :induct (fast-run-fuel n fm)))
  :rule-classes nil)

(in-theory (disable fast-run-fuel))

; ---------------------------------------------------------------------------
; 6. The invariant without the list state

(defun fm-inv-check (fm)
  (declare (xargs :stobjs fm))
  (and (fast-inv-store (fm-store fm))
       (machine-ok (ms nil (fm-frame fm) (fm-vals fm) (fm-is fm) (fm-ctrl fm) (fm-status fm)))))

; by MACHINE-OK-OF-MS (../machine/ok.lisp): the store is not read
(defthm fm-inv-is-fm-inv-check
  (implies (fmp fm)
           (equal (fm-inv fm) (fm-inv-check fm)))
  :hints (("Goal" :in-theory (e/d (fm-inv fm->ms) (status-ok))))
  :rule-classes nil)

(in-theory (disable fm-inv-check))
