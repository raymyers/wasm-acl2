; E6 differential test 1 (plan/wasm-engine): at every step of a run, the
; machine's MACHINE-ABS after the step equals the spec stepped (MACHINE-CLOCK s) times
; from MACHINE-ABS before it. Programs: the E0 benchmarks (engine/bench/wasm,
; `sh ../bench/build.sh` first), instantiated and invoked with the spec's
; own $instantiate and $invoke; the machine starts from the configuration
; $invoke returns (MS-OF-CONFIG). From engine/machine (nix develop ../..):
;   acl2 < difftest.lsp > ../../plan/wasm-engine/notes/data/e6-machine/difftest1.out
(ld "cert.acl2")
(include-book "machine")
(in-package "WE")
(program)
(set-state-ok t)

(defun read-bytes-loop (channel acc state)
  (mv-let (b state) (read-byte$ channel state)
    (if (null b) (mv (reverse acc) state) (read-bytes-loop channel (cons b acc) state))))
(defun read-bytes (file state)
  (mv-let (channel state) (open-input-channel file :byte state)
    (if (null channel) (mv nil state)
      (mv-let (bs state) (read-bytes-loop channel nil state)
        (let ((state (close-input-channel channel state))) (mv bs state))))))
(defconst *s0* '(:%rec (:tags) (:globals) (:mems) (:tables) (:funcs) (:datas) (:elems) (:structs) (:arrays) (:exns)))
(defun stepn (k c)
  (if (zp k) (list c) (let ((r (w3t::step c))) (and r (stepn (1- k) (car r))))))
(defun spec-run (c k)                          ; STEP to the end: final config
  (if (zp k) c (let ((r (w3t::step c))) (if (atom r) c (spec-run (car r) (1- k))))))
(defun find-export (field exs)
  (cond ((atom exs) nil)
        ((equal (wrt::%get-field (car exs) :name) field) (wrt::%get-field (car exs) :addr))
        (t (find-export field (cdr exs)))))
(defun str-bytes (s) (if (atom s) nil (cons (char-code (car s)) (str-bytes (cdr s)))))

; the configuration of a call of export FIELD of module FILE on ARGS
(defun invoke-config (file field args state)
  (mv-let (bs state) (read-bytes file state)
    (let* ((p (and bs (w3t::gram/bmodule bs)))
           (m (and p (null (cadr p)) (car p)))
           (c0 (and m (w3t::$instantiate *s0* m nil)))
           (cf0 (and c0 (spec-run c0 10000000)))
           (s (cadr (cadr cf0)))
           (inst (wrt::%get-field (caddr (cadr cf0)) :module))
           (addr (find-export (str-bytes (coerce field 'list)) (wrt::%get-field inst :exports))))
      (mv (and addr (w3t::$invoke s (cadr addr) args)) state))))

; walk the machine; at every step compare with the spec
; -> (mv machine-steps spec-steps disagreements first-bad final-state)
(defun diff-walk (s k msteps ssteps bad first)
  (if (or (zp k) (not (machine-running s)))
      (mv msteps ssteps bad first s)
    (let* ((s2 (machine-step s)) (n (machine-clock s))
           (spec (stepn n (machine-abs s)))
           (ok (equal spec (list (machine-abs s2)))))
      (diff-walk s2 (1- k) (1+ msteps) (+ n ssteps) (if ok bad (1+ bad))
                 (or first (and (not ok) (list :at msteps :instr (car (ms-is s)) :clock n)))))))

(defun diff1 (name file field args state)
  (mv-let (c state) (invoke-config file field args state)
    (if (null c) (prog2$ (cw "DIFF1 ~s0: no configuration~%" name) (mv nil :ok state))
      (let ((s (ms-of-config c)))
        (mv-let (ms ss bad first fin) (diff-walk s 10000000 0 0 0 nil)
          (let* ((spec-final (spec-run c 100000000))
                 (same-final (equal (machine-abs fin) spec-final)))
            (prog2$
             (cw "DIFF1 ~s0: abs-of-loader ~x1 machine-steps ~x2 spec-steps ~x3 disagreements ~x4 status ~x5 final-equals-spec-run ~x6 result ~x7 first-bad ~x8~%"
                 name (equal (machine-abs s) c) ms ss bad (ms-status fin) same-final
                 (caddr (machine-abs fin)) first)
             (mv nil :ok state))))))))

(defun i32 (n) (list :const '(:i32) n))
(defun i64 (n) (list :const '(:i64) n))

; the machine alone, timed (no spec comparison): machine steps per second
(defun mrun (s k n)
  (if (or (zp k) (not (machine-running s))) (mv n s) (mrun (machine-step s) (1- k) (1+ n))))
(defun mclocks (s k acc)
  (if (or (zp k) (not (machine-running s))) acc (mclocks (machine-step s) (1- k) (+ acc (machine-clock s)))))
(defun rate1 (name file field args state)
  (mv-let (c state) (invoke-config file field args state)
    (mv-let (t0 state) (read-run-time state)
      (mv-let (n fin) (mrun (ms-of-config c) 100000000 0)
        (mv-let (t1 state) (read-run-time state)
          (let ((ms (round (* 1000 (- t1 t0)) 1)) (spec (mclocks (ms-of-config c) 100000000 0)))
            (prog2$ (cw "RATE ~s0: machine-steps ~x1 spec-steps ~x2 ms ~x3 spec-steps/s ~x4 status ~x5 result ~x6~%"
                        name n spec ms (if (< 0 ms) (round (* 1000 spec) ms) 0) (ms-status fin) (caddr (machine-abs fin)))
                    (mv nil :ok state))))))))
