; 3.0 SIMD check (wasm3 M1): the generated Step_pure rules for vector
; instructions, with rt/ (builtins.lisp and builtins-3.0.lisp), on every
; vector of simd-vectors-3.0.lsp (../oracle/gen-simd-vectors.mjs 3.0):
; [VCONST a, VCONST b, (VCONST c,) op] reduces in one Step_pure step to
; [VCONST result].
; - The 2.0 ops: RESULT is V8's.
; - Relaxed SIMD: the vector has two results, DET (the deterministic profile,
;   which D4 chose: V8 running the equivalent strict instructions) and V8
;   (V8's relaxed instruction on the machine that made the vectors). The
;   generated semantics must give DET. Separately, the relaxed builtins
;   evaluated in the full profile ($ND true) with the $R_* values of
;   rt/builtins-3.0.lisp must give V8: that checks that the $R_* are V8's
;   choices, and the fused multiply-add (%fma) against V8's fused
;   relaxed_madd. Float lanes compare exactly, except that any NaN matches
;   any NaN (the spec allows a set of NaNs; rt/ returns the canonical one).
(in-package "W3T")
(include-book "../../gen/wasm-3.0/wasm3")

(program)
(set-state-ok t)

(defconst *simd-ops*
  ;; wat name -> instruction (the encoding of the generated 3.0 semantics)
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
    ("f64x2.pmax" :vbinop (:x (:f64) 2) (:pmax))
    ;; relaxed SIMD (3.0)
    ("f32x4.relaxed_madd" :vternop (:x (:f32) 4) (:relaxed_madd))
    ("f32x4.relaxed_nmadd" :vternop (:x (:f32) 4) (:relaxed_nmadd))
    ("f64x2.relaxed_madd" :vternop (:x (:f64) 2) (:relaxed_madd))
    ("f64x2.relaxed_nmadd" :vternop (:x (:f64) 2) (:relaxed_nmadd))
    ("f32x4.relaxed_min" :vbinop (:x (:f32) 4) (:relaxed_min))
    ("f32x4.relaxed_max" :vbinop (:x (:f32) 4) (:relaxed_max))
    ("f64x2.relaxed_min" :vbinop (:x (:f64) 2) (:relaxed_min))
    ("f64x2.relaxed_max" :vbinop (:x (:f64) 2) (:relaxed_max))
    ("i16x8.relaxed_q15mulr_s" :vbinop (:x (:i16) 8) (:relaxed_q15mulrs))
    ("i32x4.relaxed_trunc_f32x4_s" :vcvtop (:x (:i32) 4) (:x (:f32) 4) (:relaxed_trunc (:s) nil))
    ("i32x4.relaxed_trunc_f32x4_u" :vcvtop (:x (:i32) 4) (:x (:f32) 4) (:relaxed_trunc (:u) nil))
    ("i32x4.relaxed_trunc_f64x2_s_zero" :vcvtop (:x (:i32) 4) (:x (:f64) 2) (:relaxed_trunc (:s) ((:zero))))
    ("i32x4.relaxed_trunc_f64x2_u_zero" :vcvtop (:x (:i32) 4) (:x (:f64) 2) (:relaxed_trunc (:u) ((:zero))))
    ("i8x16.relaxed_swizzle" :vswizzlop (:x (:i8) 16) (:relaxed_swizzle))
    ("i8x16.relaxed_laneselect" :vternop (:x (:i8) 16) (:relaxed_laneselect))
    ("i16x8.relaxed_laneselect" :vternop (:x (:i16) 8) (:relaxed_laneselect))
    ("i32x4.relaxed_laneselect" :vternop (:x (:i32) 4) (:relaxed_laneselect))
    ("i64x2.relaxed_laneselect" :vternop (:x (:i64) 2) (:relaxed_laneselect))
    ("i16x8.relaxed_dot_i8x16_i7x16_s" :vextbinop (:x (:i16) 8) (:x (:i8) 16) (:relaxed_dots))
    ("i32x4.relaxed_dot_i8x16_i7x16_add_s" :vextternop (:x (:i32) 4) (:x (:i8) 16) (:relaxed_dot_adds))))

(defun relaxed-name-p (name) (search "relaxed_" name))
(defun arity-of (instr) (case (car instr) ((:vternop :vvternop :vextternop) 3) ((:vcvtop) 1) (t 2)))

(defun vc (c) (list :vconst '(:v128) c))
(defun vcs (cs) (if (atom cs) nil (cons (vc (car cs)) (vcs (cdr cs)))))

; the result shape of an instruction, for the NaN-tolerant comparison
(defun result-shape (instr)
  (case (car instr) ((:vvbinop :vvternop) '(:x (:i64) 2)) (t (cadr instr))))

(defun lanes-match (ws gs float)
  (cond ((atom ws) (atom gs))
        ((atom gs) nil)
        ((and float (%nan-p (car ws)) (%nan-p (car gs))) (lanes-match (cdr ws) (cdr gs) float))
        (t (and (equal (car ws) (car gs)) (lanes-match (cdr ws) (cdr gs) float)))))

(defun v128-match (instr want got)
  (let ((sh (result-shape instr)))
    (lanes-match ($lanes_ sh want) ($lanes_ sh got) (%float-lt-p (cadr sh)))))

; one Step_pure step: the v128 result, or :NO-STEP
(defun run-instr (instr operands)
  (let ((r (step_pure (append (vcs operands) (list instr)))))
    (if (and (consp r) (consp (car r)) (consp (caar r)) (eq (car (caar r)) :vconst))
        (caddr (caar r))
      (list :no-step r))))

; --- the full profile ($ND true, the $R_* of rt/), lane by lane ------------
(defun map3 (f n as bs cs)
  (if (atom as) nil
    (cons (car (case f
                 (:madd (%frelaxed-madd t ($r_fmadd) n (car as) (car bs) (car cs)))
                 (:nmadd (%frelaxed-madd t ($r_fmadd) n (%fneg (car as)) (car bs) (car cs)))
                 (:laneselect (%irelaxed-laneselect t ($r_laneselect) n (car as) (car bs) (car cs)))
                 (:min (%frelaxed-min t ($r_fmin) n (car as) (car bs)))
                 (:max (%frelaxed-max t ($r_fmax) n (car as) (car bs)))
                 (t (%irelaxed-q15mulr t ($r_iq15mulr) n '(:s) (car as) (car bs)))))
          (map3 f n (cdr as) (cdr bs) (if (consp cs) (cdr cs) nil)))))

(defun full-profile-op (instr)
  (let ((op (car (car (last instr)))))
    (case op (:relaxed_madd :madd) (:relaxed_nmadd :nmadd) (:relaxed_laneselect :laneselect)
      (:relaxed_min :min) (:relaxed_max :max) (:relaxed_q15mulrs :q15mulr) (t nil))))

; V8's result in the full profile: computed for the relaxed builtins; for the
; relaxed operations of the generated code (swizzle, dot products) and for
; relaxed_trunc, the generated semantics gives the deterministic result,
; which must then also be V8's
(defun run-full (instr operands)
  (let ((f (full-profile-op instr)) (sh (cadr instr)))
    (if (null f) (run-instr instr operands)
      ($inv_lanes_ sh (map3 f (%lane-size (cadr sh))
                            ($lanes_ sh (first operands)) ($lanes_ sh (second operands))
                            (and (third operands) ($lanes_ sh (third operands))))))))

; (mv nok bad nfull badfull)
(defun check-simd (vs nok bad nfull badfull)
  (if (endp vs) (mv nok (reverse bad) nfull (reverse badfull))
    (let* ((v (car vs)) (name (car v))
           (instr (cdr (assoc-equal name *simd-ops*)))
           (k (if instr (arity-of instr) 0))
           (operands (take k (cdr v)))
           (relaxed (relaxed-name-p name))
           (want (nth (1+ k) v))
           (got (and instr (run-instr instr operands)))
           (ok (and instr (natp got) (v128-match instr want got)))
           (v8 (and relaxed (nth (+ 2 k) v)))
           (full (and relaxed instr (run-full instr operands)))
           (fok (or (not relaxed) (and (natp full) (v128-match instr v8 full)))))
      (check-simd (cdr vs) (if ok (1+ nok) nok) (if ok bad (cons (list v :got got) bad))
                  (if (and relaxed fok) (1+ nfull) nfull)
                  (if fok badfull (cons (list name :v8 v8 :full-profile full) badfull))))))

(defun count-relaxed (vs) (if (endp vs) 0 (+ (if (relaxed-name-p (car (car vs))) 1 0) (count-relaxed (cdr vs)))))

(make-event
 (mv-let (channel state) (open-input-channel "simd-vectors-3.0.lsp" :object state)
   (mv-let (eofp vs state) (read-object channel state)
     (let ((state (close-input-channel channel state)))
       (if eofp (mv (msg "no vectors") nil state)
         (mv-let (nok bad nfull badfull) (check-simd vs 0 nil 0 nil)
           (prog2$ (cw "~%T3 SIMD (3.0): ~x0 of ~x1 vectors agree with the WASM engine (~x2 relaxed, deterministic profile).~%T3 SIMD (3.0) full profile: ~x3 of ~x2 relaxed vectors give V8's own result with $ND true and the $R_* of rt/.~%"
                       nok (acl2::len vs) (count-relaxed vs) nfull)
                   (if (or bad badfull)
                       (mv (msg "~x0 vectors disagree, ~x1 in the full profile; first ones:~%~x2~%~x3"
                                (acl2::len bad) (acl2::len badfull)
                                (take (min 6 (acl2::len bad)) bad) (take (min 6 (acl2::len badfull)) badfull))
                           nil state)
                     (mv nil '(value-triple :t3-simd-3.0-ok) state)))))))))
