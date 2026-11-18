; License: MIT. See the file LICENSE at the top of the repository.
;
; T2, the theorem of the fast machine (plan/wasm-engine/plan2.md V6 and V7):
; when FAST-RUN ends with a result, the specification's STEPS/%FUEL,
; started from the configuration the first stobj stands for with enough
; fuel, returns the configuration the last stobj stands for.
;
; It is T1 (../machine/spec-result.lisp) for the list state FM->MS of the
; stobj, with the run lemma of inv.lisp: a fast run that ends with a result
; did not end :unsupported, so it is the list machine's run.
;
; It is the statement of plan2.md section 1: no hypothesis about an
; instruction. At a call_ref of a host function the fast machine stops
; :unsupported (plan2.md P1), which is not a result.
(in-package "WE")
(include-book "inv")
(include-book "../machine/spec-result")

(set-prover-step-limit 2000000)

(defun fast-result-p (fm)
  (declare (xargs :stobjs fm))
  (sym-member (fm-status fm) '(:done :trap :throw)))

; The spec steps that a run of N fast steps stands for: those of the list
; machine's run from the same state (MACHINE-CLOCKS). Not executable: it is
; only a bound on the fuel that the specification needs.
(defun-nx fast-clocks (n fm)
  (machine-clocks n (fm->ms fm)))

(defthm fast-result-is-not-unsupported
  (implies (fast-result-p fm)
           (not (equal (nth *fm-status* fm) :unsupported)))
  :hints (("Goal" :in-theory (enable sym-member))))

(defthm machine-result-p-of-fm->ms
  (equal (machine-result-p (fm->ms fm))
         (fast-result-p fm))
  :hints (("Goal" :in-theory (enable machine-result-p))))

(defthm machine-ok-when-fm-inv
  (implies (fm-inv fm)
           (machine-ok (fm->ms fm)))
  :hints (("Goal" :in-theory (enable fm-inv))))

(in-theory (disable fast-result-p fast-clocks))

; the list machine's run ends with the result of the fast run
(defthm machine-result-p-of-machine-run-of-fm->ms
  (implies (and (fm-inv fm)
                (fast-result-p (fast-run n fm)))
           (machine-result-p (machine-run n (fm->ms fm))))
  :hints (("Goal" :use (fast-run-is-machine-run
                        (:instance machine-result-p-of-fm->ms (fm (fast-run n fm))))
                  :in-theory (disable fast-run-is-machine-run machine-result-p-of-fm->ms)
                  :do-not-induct t)))

; T2
(defthm fast-result-is-spec-result
  (implies (and (fm-inv fm)
                (fast-result-p (fast-run n fm))
                (natp fuel)
                (< (fast-clocks n fm) fuel))
           (equal (w3t::steps/%fuel fuel (machine-abs (fm->ms fm)))
                  (list (machine-abs (fm->ms (fast-run n fm))))))
  :hints (("Goal" :use ((:instance machine-result-is-spec-result (s (fm->ms fm))))
                  :in-theory (e/d (fast-clocks)
                                  (machine-result-is-spec-result machine-abs
                                   machine-abs-of-state-variable))
                  :do-not-induct t)))
