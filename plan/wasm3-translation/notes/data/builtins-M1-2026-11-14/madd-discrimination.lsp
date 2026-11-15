; wasm3 M1: does the full-profile check of t3-simd-3.0 discriminate? Count the
; relaxed_madd vectors whose V8 result the full profile reproduces with
; R_fmadd = 0 (unfused) and = 1 (fused, %fma). From translate/tests/sem-3.0,
; after make check-3.0:  acl2 < ../../../plan/wasm3-translation/notes/data/builtins-M1-2026-11-14/madd-discrimination.lsp
(ld "cert.acl2")
(include-book "t3-simd-3.0")
(in-package "W3T")
(set-state-ok t)
(program)
(defun madd-lanes (r n as bs cs)
  (if (atom as) nil
    (cons (car (%frelaxed-madd t r n (car as) (car bs) (car cs))) (madd-lanes r n (cdr as) (cdr bs) (cdr cs)))))
(defun madd-r (vs r acc)
  ;; madd vectors whose V8 result the full profile with R_fmadd = r reproduces
  (if (endp vs) acc
    (let* ((v (car vs)) (name (car v)))
      (if (or (equal name "f32x4.relaxed_madd") (equal name "f64x2.relaxed_madd"))
          (let* ((instr (cdr (assoc-equal name *simd-ops*))) (sh (cadr instr)) (n (%lane-size (cadr sh)))
                 (as ($lanes_ sh (nth 1 v))) (bs ($lanes_ sh (nth 2 v))) (cs ($lanes_ sh (nth 3 v)))
                 (got ($inv_lanes_ sh (madd-lanes r n as bs cs))))
            (madd-r (cdr vs) r (if (v128-match instr (nth 5 v) got) (1+ acc) acc)))
        (madd-r (cdr vs) r acc)))))
(mv-let (channel state) (open-input-channel "simd-vectors-3.0.lsp" :object state)
  (mv-let (eofp vs state) (read-object channel state)
    (declare (ignore eofp))
    (let ((state (close-input-channel channel state)))
      (prog2$ (cw "MUT madd vectors reproducing V8: R_fmadd=0 ~x0 of 48, R_fmadd=1 ~x1 of 48~%" (madd-r vs 0 0) (madd-r vs 1 0)) (mv nil :ok state)))))
