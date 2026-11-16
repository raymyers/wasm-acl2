; E0 item 4: what STEP returns. Runs the counting loop and a trapping and a
; throwing function, and records the shape of every STEP result: NIL, or a
; list of how many configurations. Also STEP on a lone TRAP, on a value
; list, and on an uncaught exception. From engine/bench (nix develop ../..):
;   acl2 < probe-step.lsp > ../../plan/wasm-engine/notes/data/e0-baseline/probe-step.out
(ld "bench.lsp")
(in-package "W3T")
(defun shapes (c k acc)       ; acc: alist (length-of-result . count)
  (if (zp k) (mv acc c)
    (let* ((r (step c)) (key (if (atom r) :nil (acl2::len r)))
           (acc (put-assoc-equal key (1+ (or (cdr (assoc-equal key acc)) 0)) acc)))
      (if (atom r) (mv acc c) (shapes (car r) (1- k) acc)))))
(defun probe (file field args state)
  (mv-let (bs state) (read-bytes file state)
    (let* ((p (gram/bmodule bs)) (m (car p))
           (c0 ($instantiate *s0* m nil)))
      (mv-let (n0 cf0) (run-steps c0 1000000 0)
        (declare (ignore n0))
        (let* ((s (cadr (cadr cf0))) (inst (%get-field (caddr (cadr cf0)) :module))
               (addr (find-export (str-bytes (coerce field 'list)) (%get-field inst :exports)))
               (c ($invoke s (cadr addr) args)))
          (mv-let (acc cf) (shapes c 1000000 nil)
            (prog2$ (cw "PROBE ~s0 ~s1: result lengths ~x2; final instrs ~x3; STEP of final ~x4~%"
                        file field acc (caddr cf) (step cf))
                    (mv nil :ok state))))))))
(probe "wasm/count-1.wasm" "run" (list (i32 50)) state)
(probe "wasm/throw-1.wasm" "run" (list (i32 5)) state)
(probe "wasm/trap-1.wasm" "div" (list (i32 0)) state)
(probe "wasm/trap-1.wasm" "uncaught" (list (i32 3)) state)
