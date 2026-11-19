; License: MIT. See the file LICENSE at the top of the repository.
;
; T3, the engine as it is called (plan/wasm-engine/plan2.md V8, section 1).
;   - ENGINE-RUN: load a configuration of the specification into the stobj
;     and run the fast machine. It is the function a driver calls.
;   - ENGINE-CONFIG: the configuration the stobj stands for.
;   - ENGINE-RUN-IS-SPEC-RUN: when ENGINE-RUN ends with a result, the
;     specification's STEPS/%FUEL, started from the configuration with
;     enough fuel, returns the configuration of the last stobj.
;   - ENGINE-RUN-IS-SPEC-STEPS: whatever way ENGINE-RUN ends, the
;     configuration of the last stobj is one the specification reaches from
;     the configuration it was given, in ENGINE-STEPS steps of STEP. So the
;     engine follows the specification or stops: it is never in a
;     configuration the specification does not reach. (The converse is not
;     claimed: where the engine stops without a result, the specification
;     may step on.)
; How to inspect the two theorems: THEOREM.md and inspect.lsp.
; T3 is T2 (fast/spec-result.lisp) with the loader lemmas of fast/inv.lisp:
; the invariant FM-INV of T2 is no longer a hypothesis. What is asked of the
; input is its shape, CONFIG-SHAPE-P, which is executable: ((s; f); instr*)
; with a store that has every field and a memory 0 with a byte list. A store
; with no memory is outside (plan2.md V6).
;
; One hypothesis is not in the statement of plan2.md section 1 as first
; written: (FMP FM), that FM is a stobj of the machine. ACL2 guarantees it
; of the live stobj (it is in the guard of every function that takes FM);
; in a theorem FM is any object, and the loader lemma FM-INV-OF-FM-LOAD-MS
; needs it.
;
; ENGINE-INVOKE-IS-SPEC-RUN is T3 for the configuration the specification's
; $invoke builds from a store, a function address and arguments. $invoke is
; in logic mode. $instantiate is in program mode (it calls the validation
; relation Module_ok), so there is no such statement from a module.
(in-package "WE")
(include-book "fast/stretch")

(set-prover-step-limit 2000000)

(defun engine-run (n c fm)
  (declare (xargs :stobjs fm :guard (natp n)))
  (let ((fm (fm-load-ms (ms-of-config c) fm)))
    (fast-run n fm)))

(defun engine-result-p (fm)
  (declare (xargs :stobjs fm))
  (fast-result-p fm))

(defun engine-config (fm)
  (declare (xargs :stobjs fm))
  (machine-abs (fm->ms fm)))

; The spec steps that a run of N engine steps from C stands for: those of
; the list machine's run from the same configuration. Executable, at the
; list machine's speed; it is only a bound on the specification's fuel.
(defun engine-clocks (n c)
  (declare (xargs :guard (natp n)))
  (machine-clocks n (ms-of-config c)))

; T3
(defthm engine-run-is-spec-run
  (implies (and (config-shape-p c)
                (fmp fm)
                (engine-result-p (engine-run n c fm))
                (natp fuel)
                (< (engine-clocks n c) fuel))
           (equal (w3t::steps/%fuel fuel c)
                  (list (engine-config (engine-run n c fm)))))
  :hints (("Goal" :use ((:instance fast-result-is-spec-result
                                   (fm (fm-load-ms (ms-of-config c) fm))))
                  :in-theory (e/d (fast-clocks) (fast-result-is-spec-result machine-abs fmp))
                  :do-not-induct t)))

(in-theory (disable engine-run engine-result-p engine-config engine-clocks))

; T3 for an invocation: the configuration is the one $invoke builds
(defthm engine-invoke-is-spec-run
  (implies (and (config-shape-p (w3t::$invoke s a vals))
                (fmp fm)
                (engine-result-p (engine-run n (w3t::$invoke s a vals) fm))
                (natp fuel)
                (< (engine-clocks n (w3t::$invoke s a vals)) fuel))
           (equal (w3t::steps/%fuel fuel (w3t::$invoke s a vals))
                  (list (engine-config (engine-run n (w3t::$invoke s a vals) fm)))))
  :hints (("Goal" :in-theory (disable w3t::$invoke (:e tau-system)))))

; ---------------------------------------------------------------------------
; The engine follows the specification or stops.

(defthm fm-status-of-fm-load-ms-of-ms-of-config
  (equal (nth *fm-status* (fm-load-ms (ms-of-config c) fm)) :run)
  :hints (("Goal" :in-theory (enable fm-load-ms ms-of-config))))

; The steps of the specification that the run stands for: those of the list
; machine's run over the machine steps the engine took, the refused one not
; counted (FAST-RUN-STEPS, fast/stretch.lisp). Not executable: the theorem
; says that such a number exists, and this is it.
(defun-nx engine-steps (n c fm)
  (machine-clocks (fast-run-steps n (fm-load-ms (ms-of-config c) fm))
                  (ms-of-config c)))

; STEPN (theorem/simulation.lisp) is exactly K steps of W3T::STEP.
(defthm engine-run-is-spec-steps
  (implies (and (config-shape-p c)
                (fmp fm))
           (equal (stepn (engine-steps n c fm) c)
                  (list (engine-config (engine-run n c fm)))))
  :hints (("Goal" :use ((:instance fast-run-is-spec-steps-or-refused
                                   (fm (fm-load-ms (ms-of-config c) fm))))
                  :in-theory (e/d (engine-run engine-config)
                                  (fast-run-is-spec-steps-or-refused machine-abs stepn fmp))
                  :do-not-induct t)))

(in-theory (disable engine-steps))
