; 2.0 SIMD check (wasm3 prep P4, 2.0 gate): the generated Step_pure rules for
; vector instructions, with the shared builtins (rt/: lanes_, inv_lanes_,
; iavgr_, iq15mulr_sat_, narrow__, ibitselect_, iandnot_, fpmin_, fpmax_),
; agree with Node/V8 on every vector in simd-vectors-2.0.lsp
; (../oracle/gen-simd-vectors.mjs): [VCONST a, VCONST b, (VCONST c,) op]
; reduces in one Step_pure step to [VCONST result].
(in-package "W2T")
(include-book "../../gen/wasm-2.0/wasm2")

(program)
(set-state-ok t)

(defconst *simd-ops*
  ;; wat name -> instruction (the encoding of the generated 2.0 semantics)
  '(("i8x16.add" :vbinop (:x (:i8) 16) (:add))
    ("i16x8.sub" :vbinop (:x (:i16) 8) (:sub))
    ("i32x4.mul" :vbinop (:x (:i32) 4) (:mul))
    ("i64x2.add" :vbinop (:x (:i64) 2) (:add))
    ("i8x16.add_sat_s" :vbinop (:x (:i8) 16) (:add_sat (:s)))
    ("i16x8.sub_sat_u" :vbinop (:x (:i16) 8) (:sub_sat (:u)))
    ("i8x16.avgr_u" :vbinop (:x (:i8) 16) (:avgru))
    ("i16x8.avgr_u" :vbinop (:x (:i16) 8) (:avgru))
    ("i16x8.q15mulr_sat_s" :vbinop (:x (:i16) 8) (:q15mulr_sats))
    ("i8x16.min_s" :vbinop (:x (:i8) 16) (:min (:s)))
    ("i32x4.max_u" :vbinop (:x (:i32) 4) (:max (:u)))
    ("i8x16.narrow_i16x8_s" :vnarrow (:x (:i8) 16) (:x (:i16) 8) (:s))
    ("i16x8.narrow_i32x4_u" :vnarrow (:x (:i16) 8) (:x (:i32) 4) (:u))
    ("v128.and" :vvbinop (:v128) (:and))
    ("v128.andnot" :vvbinop (:v128) (:andnot))
    ("v128.bitselect" :vvternop (:v128) (:bitselect))
    ("f32x4.add" :vbinop (:x (:f32) 4) (:add))
    ("f64x2.mul" :vbinop (:x (:f64) 2) (:mul))
    ("f32x4.min" :vbinop (:x (:f32) 4) (:min))
    ("f64x2.max" :vbinop (:x (:f64) 2) (:max))
    ("f32x4.pmin" :vbinop (:x (:f32) 4) (:pmin))
    ("f64x2.pmax" :vbinop (:x (:f64) 2) (:pmax))))

(defun vc (c) (list :vconst '(:v128) c))
(defun vcs (cs) (if (atom cs) nil (cons (vc (car cs)) (vcs (cdr cs)))))

(defun run-simd (v)
  ;; v = (name a b [c] result): the Step_pure result, or the instruction
  ;; name when the op is unknown
  (let ((instr (cdr (assoc-equal (car v) *simd-ops*))))
    (if (null instr) (list :unknown (car v))
      (step_pure (append (vcs (butlast (cdr v) 1)) (list instr))))))

(defun check-simd (vs nok bad)
  (if (endp vs) (mv nok (reverse bad))
    (let* ((v (car vs)) (want (list (list (vc (car (last v))))))
           (got (run-simd v)))
      (if (equal got want)
          (check-simd (cdr vs) (1+ nok) bad)
        (check-simd (cdr vs) nok (cons (list v :got got) bad))))))

(make-event
 (mv-let (channel state) (open-input-channel "simd-vectors-2.0.lsp" :object state)
   (mv-let (eofp vs state) (read-object channel state)
     (let ((state (close-input-channel channel state)))
       (if eofp (mv (msg "no vectors") nil state)
         (mv-let (nok bad) (check-simd vs 0 nil)
           (prog2$ (cw "~%T3 SIMD (2.0): ~x0 of ~x1 vectors agree with the WASM engine.~%"
                       nok (acl2::len vs))
                   (if bad
                       (mv (msg "~x0 vectors disagree; first ones:~%~x1" (acl2::len bad)
                                (take (min 6 (acl2::len bad)) bad))
                           nil state)
                     (mv nil '(value-triple :t3-simd-2.0-ok) state)))))))))
