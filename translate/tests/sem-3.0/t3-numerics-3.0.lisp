; 2.0 numerics check (wasm3 prep P4, 2.0 gate): the generated WASM 2.0 numeric
; dispatch with the shared builtins (rt/) agrees with Node/V8 on the 1.0
; scalar vectors (../sem/numeric-vectors.lsp) and on the scalar ops 2.0 adds
; (../sem-2.0/numeric-vectors-2.0.lsp: saturating truncation, sign extension; from
; ../oracle/gen-numeric-vectors.mjs 2.0).
(in-package "W3T")
(include-book "../../gen/wasm-3.0/wasm3")

(program)
(set-ignore-ok t)
(set-state-ok t)

(defconst *ops*
  ;; wasm op suffix -> (family . op term in the W1T encoding)
  '(("add" :bin :add) ("sub" :bin :sub) ("mul" :bin :mul)
    ("div_s" :bin :div (:s)) ("div_u" :bin :div (:u)) ("div" :bin :div)
    ("rem_s" :bin :rem (:s)) ("rem_u" :bin :rem (:u))
    ("and" :bin :and) ("or" :bin :or) ("xor" :bin :xor) ("shl" :bin :shl)
    ("shr_s" :bin :shr (:s)) ("shr_u" :bin :shr (:u)) ("rotl" :bin :rotl) ("rotr" :bin :rotr)
    ("min" :bin :min) ("max" :bin :max) ("copysign" :bin :copysign)
    ("clz" :un :clz) ("ctz" :un :ctz) ("popcnt" :un :popcnt)
    ("abs" :un :abs) ("neg" :un :neg) ("sqrt" :un :sqrt) ("ceil" :un :ceil)
    ("floor" :un :floor) ("trunc" :un :trunc) ("nearest" :un :nearest)
    ("eqz" :test :eqz)
    ("extend8_s" :un :extend 8) ("extend16_s" :un :extend 16) ("extend32_s" :un :extend 32)
    ("eq" :rel :eq) ("ne" :rel :ne)
    ("lt_s" :rel :lt (:s)) ("lt_u" :rel :lt (:u)) ("gt_s" :rel :gt (:s)) ("gt_u" :rel :gt (:u))
    ("le_s" :rel :le (:s)) ("le_u" :rel :le (:u)) ("ge_s" :rel :ge (:s)) ("ge_u" :rel :ge (:u))
    ("lt" :rel :lt) ("gt" :rel :gt) ("le" :rel :le) ("ge" :rel :ge)))

(defun vt-of (s) (list (intern$ (string-upcase s) "KEYWORD")))   ; "f32" -> (:F32)
(defun float-vt-p (vt) (member-eq (car vt) '(:f32 :f64)))
(defun vt-bits (vt) (if (member-eq (car vt) '(:i64 :f64)) 64 32))

; argument bits -> value in the W1T encoding
(defun to-val (vt bits) (if (float-vt-p vt) (%bitsf (vt-bits vt) bits) bits))
; result value -> bits, or :NAN for any NaN
(defun from-val (vt v exact)
  (cond ((not (float-vt-p vt)) v)
        ((and (%nan-p v) (not exact)) :nan)
        (t (%fbits (vt-bits vt) v))))

(defun search-char (c s i)
  (cond ((>= i (length s)) nil)
        ((eql (char s i) c) i)
        (t (search-char c s (1+ i)))))

; A list result (val_*) is empty for a trap; take its single element.
(defun from-list (vt r exact) (if (consp r) (from-val vt (car r) exact) :trap))

; Conversions: "i32.trunc_f32_s" etc.  Returns (mv result-vt value-list).
(defun run-cvt (dst rest arg)
  ;; rest: e.g. "trunc_f32_s", "wrap_i64", "reinterpret_f32"
  (let* ((u (search-char #\_ rest 0))
         (op (subseq rest 0 u))
         (tail (subseq rest (1+ u) (length rest)))
         (src (vt-of (subseq tail 0 3)))
         (sx (and (> (length tail) 3) (list (intern$ (string-upcase (subseq tail 4 5)) "KEYWORD"))))
         (sat (and (> (length tail) 4) (equal (subseq tail 0 4) "sat_")))
         (tail (if sat (subseq tail 4 (length tail)) tail))
         (src (vt-of (subseq tail 0 3)))
         (sx (and (> (length tail) 3) (list (intern$ (string-upcase (subseq tail 4 5)) "KEYWORD"))))
         (cvtop (cond (sat (list :trunc_sat sx))
                      ((equal op "wrap") '(:wrap))
                      ((equal op "extend") (list :extend sx))
                      ((equal op "trunc") (list :trunc sx))
                      ((equal op "convert") (list :convert sx))
                      ((equal op "demote") '(:demote))
                      ((equal op "promote") '(:promote))
                      (t '(:reinterpret)))))
    ($cvtop__ src dst cvtop (to-val src arg))))

(defun run-vector (v)
  ;; returns the computed result in the vector's notation
  (let* ((name (car v)) (vt (vt-of (subseq name 0 3)))
         (rest (subseq name 4 (length name)))
         (args (butlast (cdr v) 1))
         (entry (cdr (assoc-equal rest *ops*))))
    ;; exact-name lookup: conversions such as "trunc_f32_s" are not in *ops*
    (cond
     (entry
      (let ((kind (car entry)) (op (cdr entry)))
        (case kind
          (:bin (from-list vt ($binop_ vt op (to-val vt (first args)) (to-val vt (second args))) nil))
          (:un (from-list vt ($unop_ vt op (to-val vt (first args))) nil))
          (:test ($testop_ vt op (to-val vt (first args))))
          (t ($relop_ vt op (to-val vt (first args)) (to-val vt (second args)))))))
     (t (from-list vt (run-cvt vt rest (first args))
                     ;; reinterpret results are bit-exact (NaN payloads too)
                     (equal (subseq rest 0 (min 11 (length rest))) "reinterpret"))))))

(defun check-vectors (vs nok bad)
  (if (endp vs) (mv nok (reverse bad))
    (let* ((v (car vs)) (want (car (last v))) (got (run-vector v)))
      (if (equal got want)
          (check-vectors (cdr vs) (1+ nok) bad)
        (check-vectors (cdr vs) nok (cons (list v :got got) bad))))))

(defun read-vectors (file state)
  (mv-let (channel state) (open-input-channel file :object state)
    (mv-let (eofp vs state) (read-object channel state)
      (let ((state (close-input-channel channel state)))
        (mv (if eofp nil vs) state)))))

(make-event
 (mv-let (v1 state) (read-vectors "../sem/numeric-vectors.lsp" state)
   (mv-let (v2 state) (read-vectors "../sem-2.0/numeric-vectors-2.0.lsp" state)
     (let ((vs (append v1 v2)))
       (if (or (null v1) (null v2)) (mv (msg "no vectors") nil state)
         (mv-let (nok bad) (check-vectors vs 0 nil)
           (prog2$ (cw "~%T3 numerics (3.0): ~x0 of ~x1 vectors agree with the WASM engine (~x2 from 1.0, ~x3 2.0-only).~%"
                       nok (acl2::len vs) (acl2::len v1) (acl2::len v2))
                   (if bad
                       (mv (msg "~x0 vectors disagree; first ones:~%~x1" (acl2::len bad)
                                (take (min 12 (acl2::len bad)) bad))
                           nil state)
                     (mv nil '(value-triple :t3-numerics-3.0-ok) state)))))))))
