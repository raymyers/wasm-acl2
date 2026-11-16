; E7 Phase A test: the fast machine against the list machine (D7).
;  - lockstep: at every step, FM->MS of the fast state equals the list
;    machine's state (small runs: FM->MS copies the memory);
;  - whole runs: the final states are equal; both machines are timed.
; From engine/fast inside nix develop (benchmarks from ../bench/build.sh):
;   SBCL_USER_ARGS='--control-stack-size 1000' acl2 < fasttest.lsp > OUT
(ld "cert.acl2")
(include-book "fast")
(in-package "WE")
(ld "../machine/difftest.lsp" :ld-skip-proofsp t)
(in-package "WE")
(program)
(set-state-ok t)

; lockstep: (mv steps disagreements first-bad fm)
(defun lock-walk (s k n bad first fm)
  (declare (xargs :stobjs fm))
  (if (or (zp k) (not (machine-running s))) (mv n bad first fm)
    (let* ((s2 (machine-step s)) (fm (fast-step fm))
           (ok (equal (fm->ms fm) s2)))
      (lock-walk s2 (1- k) (1+ n) (if ok bad (1+ bad))
                 (or first (and (not ok) (list :at n :instr (car (ms-is s))))) fm))))

(defun lock1 (name file field args fm state)
  (declare (xargs :stobjs fm))
  (mv-let (c state) (invoke-config file field args state)
    (let* ((s (ms-of-config c)) (fm (fm-load-ms s fm)))
      (mv-let (n bad first fm) (lock-walk s 100000000 0 0 nil fm)
        (prog2$ (cw "LOCKSTEP ~s0: steps ~x1 disagreements ~x2 first-bad ~x3 status ~x4~%"
                    name n bad first (fm-status fm))
                (mv fm state))))))

(defun ms-of (t0 t1) (round (* 1000 (- t1 t0)) 1))

(defun run1 (name file field args fm state)
  (declare (xargs :stobjs fm))
  (mv-let (c state) (invoke-config file field args state)
    (let ((s (ms-of-config c)))
      (mv-let (t0 state) (read-run-time state)
        (let ((s2 (machine-run 1000000000 s)))
          (mv-let (t1 state) (read-run-time state)
            (let ((fm (fm-load-ms s fm)))
              (mv-let (t2 state) (read-run-time state)
                (let ((fm (fast-run 1000000000 fm)))
                  (mv-let (t3 state) (read-run-time state)
                    (prog2$ (cw "RUN ~s0: equal ~x1 status ~x2 list-ms ~x3 fast-ms ~x4 result ~x5~%"
                                name (equal (fm->ms fm) s2) (fm-status fm)
                                (ms-of t0 t1) (ms-of t2 t3) (caddr (machine-abs s2)))
                            (mv fm state))))))))))))
