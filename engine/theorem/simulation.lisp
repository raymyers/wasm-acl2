; License: MIT. See the file LICENSE at the top of the repository.
;
; The engine's theorem, stated once for any machine (plan/wasm-engine E3).
;
; A machine is six functions: a state invariant, "still running", "stopped
; with a result", one step, the abstraction to a spec configuration, and
; the clock (how many spec steps one machine step stands for). They are
; constrained by four properties. From these alone this book proves the
; run-level theorem ENGINE-RESULT-IS-SPEC-RESULT: when the machine stops
; with a result, the specification's STEPS/%FUEL, started from the
; abstraction of the initial state with enough fuel, returns the
; abstraction of the final state.
;
; Nothing here is assumed about a particular machine and nothing is
; skipped. E11 discharges the four constraints for the real machine and
; gets the theorem for it by functional instantiation. Host functions: the
; spec's $hostcall is a constrained function (rt/builtins-3.0.lisp), so a
; fact about W3T::STEP holds for every host.
;
; The statement is one direction: results of the machine are results of
; the spec. A machine that stops without a result (stuck, unsupported
; instruction) claims nothing (notes E3-theorem.md, E5-machine.md).
(in-package "WE")
(include-book "../../translate/gen/wasm-3.0/wasm3")

(local (in-theory (disable w3t::step)))

; Exactly K steps of the specification: (list c') if STEP succeeds K times
; from C, else nil. STEP returns (list c') or nil.
(defun stepn (k c)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      (list c)
    (let ((r (w3t::step c)))
      (and r (stepn (1- k) (car r))))))

(encapsulate
  (((m-ok *) => *)        ; invariant of machine states
   ((m-running *) => *)   ; the machine takes another step
   ((m-result-p *) => *)  ; the machine stopped with a result (values or a trap)
   ((m-step *) => *)
   ((m-abs *) => *)       ; machine state -> spec configuration
   ((m-clock *) => *))    ; spec steps that the next machine step stands for

  (local (defun m-ok (s) (declare (ignore s)) t))
  (local (defun m-running (s) (declare (ignore s)) nil))
  (local (defun m-result-p (s) (declare (ignore s)) nil))
  (local (defun m-step (s) s))
  (local (defun m-abs (s) s))
  (local (defun m-clock (s) (declare (ignore s)) 0))

  (defthm m-clock-natp
    (natp (m-clock s))
    :rule-classes :type-prescription)

  ; C1: a step keeps the invariant
  (defthm m-step-preserves-ok
    (implies (and (m-ok s) (m-running s))
             (m-ok (m-step s))))

  ; C2: one machine step is exactly (m-clock s) spec steps
  (defthm m-step-simulates
    (implies (and (m-ok s) (m-running s))
             (equal (stepn (m-clock s) (m-abs s))
                    (list (m-abs (m-step s))))))

  ; C3: a result is a configuration that the spec does not step
  (defthm m-result-is-terminal
    (implies (and (m-ok s) (m-result-p s))
             (not (w3t::step (m-abs s)))))

  ; C4: a machine with a result has stopped
  (defthm m-result-not-running
    (implies (m-result-p s)
             (not (m-running s)))))

; The machine run with fuel N, and the spec steps it stands for.
(defun m-run (n s)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (not (m-running s)))
      s
    (m-run (1- n) (m-step s))))

(defun m-clocks (n s)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (not (m-running s)))
      0
    (+ (m-clock s) (m-clocks (1- n) (m-step s)))))

(defthm m-run-ok
  (implies (m-ok s)
           (m-ok (m-run n s))))

(defthm stepn-of-+
  (implies (and (natp a) (natp b))
           (equal (stepn (+ a b) c)
                  (and (stepn a c)
                       (stepn b (car (stepn a c)))))))

; Run level, part 1: N machine steps are (m-clocks n s) spec steps.
(defthm m-run-simulates
  (implies (m-ok s)
           (equal (stepn (m-clocks n s) (m-abs s))
                  (list (m-abs (m-run n s))))))

; The spec's own run function agrees with STEPN followed by a failed STEP.
(local
 (defun stepn-fuel-induct (k fuel c)
   (declare (xargs :measure (nfix k)))
   (if (zp k)
       (list fuel c)
     (stepn-fuel-induct (1- k) (1- fuel) (car (w3t::step c))))))

(defthm stepn-then-no-step-is-steps
  (implies (and (equal (stepn k c) (list c2))
                (not (w3t::step c2))
                (natp fuel)
                (< (nfix k) fuel))
           (equal (w3t::steps/%fuel fuel c)
                  (list c2)))
  :hints (("Goal" :induct (stepn-fuel-induct k fuel c))))

; The theorem. S is any machine state with the invariant; N is the
; machine's fuel; FUEL is the spec's fuel.
;   m-ok s                       the invariant holds at the start
;   m-result-p (m-run n s)       the machine stopped with a result within N steps
;   m-clocks n s < fuel          the spec is given at least as many steps as
;                                the run stands for, plus the one that fails
(defthm engine-result-is-spec-result
  (implies (and (m-ok s)
                (m-result-p (m-run n s))
                (natp fuel)
                (< (m-clocks n s) fuel))
           (equal (w3t::steps/%fuel fuel (m-abs s))
                  (list (m-abs (m-run n s)))))
  :hints (("Goal" :use ((:instance stepn-then-no-step-is-steps
                                   (k (m-clocks n s))
                                   (c (m-abs s))
                                   (c2 (m-abs (m-run n s))))
                        (:instance m-run-simulates))
           :in-theory (disable stepn-then-no-step-is-steps m-run-simulates))))
