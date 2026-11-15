; Hand-written builtins that only WASM 3.0 has (wasm3 M1), for the generated
; W3T semantics. The translator reads this file for SPEC=3.0 only and the
; first generated 3.0 part includes it, so the 1.0 and 2.0 packages and
; their generated code do not change (il2acl2/emit.lisp rt-files-for).
; Encodings as in builtins.lisp. Semantics from the 3.0 spec text
; (document/core/exec/numerics.rst at the pinned rev) and SpecTec's
; interpreter (spectec/src/backend-interpreter/numerics.ml).
(in-package "WRT")

(include-book "builtins")

; ---------------------------------------------------------------------
; Host functions (4.0-execution.configurations): $hostcall is a hook for
; the driver. The default attachment has no result, so a call of a host
; function does not step (neither RES nor BOT). A driver attaches its own
; function of (hostfunc store vals) -> list of (:RES store result) | (:BOT).
; ACL2 uses attachments in top-level and make-event evaluation, not when it
; evaluates a defconst: a defconst whose value steps a host call fails.

(encapsulate (((%hostcall-hook * * *) => *))
  (local (defun %hostcall-hook (hf s vals) (declare (ignore hf s vals)) nil)))

(defun %hostcall-none (hf s vals)
  (declare (xargs :guard t) (ignore hf s vals))
  nil)

(defattach %hostcall-hook %hostcall-none)

(set-verify-guards-eagerness 0)

(defun $hostcall (hf s vals) (%hostcall-hook hf s vals))

; ---------------------------------------------------------------------
; Nondeterminism (decision D4: deterministic profile). $ND is false, so
; every $relaxed2/$relaxed4 of the generated code and every relaxed
; builtin below takes alternative 0, as in SpecTec's interpreter. The $R_*
; parameters are fixed to the choices V8 makes on the machine where the
; vectors were made (arm64, Node v24; tests/sem-3.0/simd-vectors-3.0.lsp):
; V8 fuses relaxed_madd/nmadd (R_fmadd = 1) and takes alternative 0 for
; the others. With $ND false these values change no result.

(defun $nd () nil)
(defun $r_fmadd () 1)
(defun $r_fmin () 0)
(defun $r_fmax () 0)
(defun $r_idot () 0)
(defun $r_idot_add () 0)
(defun $r_iq15mulr () 0)
(defun $r_trunc_u () 0)
(defun $r_trunc_s () 0)
(defun $r_swizzle () 0)
(defun $r_laneselect () 0)

; relaxed(R)[A_0, ..., A_n]: A_R in the full profile (ND), else A_0
(defun %relaxed (nd r alts)
  (if (and nd (< (nfix r) (acl2::len alts))) (nth (nfix r) alts) (car alts)))

; ---------------------------------------------------------------------
; Sequences and representation (0.3-aux.seq, 3.1-numerics.scalar)

; split l into lists of n elements; a shorter rest is dropped (numerics.ml)
(defun $inv_concatn_ (n l)
  (declare (xargs :measure (acl2::len l)))
  (if (or (zp n) (< (acl2::len l) n) (atom l)) nil
    (cons (take n l) ($inv_concatn_ n (nthcdr n l)))))

(defun %packtype-size (zt)
  (case (and (consp zt) (car zt)) (:i8 8) (:i16 16) (otherwise nil)))
(defun %v128-type-p (zt) (and (consp zt) (eq (car zt) :v128)))

; storage types: a numeric type, V128, or a packed type I8 / I16
(defun $zbytes_ (zt c)
  (cond ((%packtype-size zt) ($ibytes_ (%packtype-size zt) c))
        ((%v128-type-p zt) ($vbytes_ zt c))
        (t ($nbytes_ zt c))))
(defun $inv_zbytes_ (zt bs)
  (cond ((%packtype-size zt) ($inv_ibytes_ (%packtype-size zt) bs))
        ((%v128-type-p zt) ($inv_vbytes_ zt bs))
        (t ($inv_nbytes_ zt bs))))
; constant types: a numeric type or V128
(defun $cbytes_ (ct c) (if (%v128-type-p ct) ($vbytes_ ct c) ($nbytes_ ct c)))
(defun $inv_cbytes_ (ct bs) (if (%v128-type-p ct) ($inv_vbytes_ ct bs) ($inv_nbytes_ ct bs)))

(defun $ceilz (q) (ceiling (rfix q) 1))

; $utf8single (5.1-binary.values; config :def utf8single): the UTF-8
; bytes of one character; no clause applies to a surrogate or to a value
; above U+10FFFF, so there is no result (nil).
(defun $utf8single (ch)
  (let ((ch (nfix ch)))
    (if (or (and (<= #xD800 ch) (< ch #xE000)) (>= ch #x110000)) nil
      (%utf8-char ch))))

; ---------------------------------------------------------------------
; Relaxed integer operations (3.1-numerics.scalar)

(defun %irelaxed-q15mulr (nd r n sx a b)
  (let ((min (%pow2 (1- n))))
    (if (and (equal (%u n a) min) (equal (%u n b) min))
        (list (%relaxed nd r (list (1- min) min)))
      (list ($iq15mulr_sat_ n sx a b)))))
(defun $irelaxed_q15mulr_ (n sx a b) (%irelaxed-q15mulr ($nd) ($r_iq15mulr) n sx a b))

(defun %irelaxed-laneselect (nd r n a b c)
  (let ((spread (if (< (%u n c) (%pow2 (1- n))) 0 (1- (%pow2 n)))))
    (list ($ibitselect_ n a b (%relaxed nd r (list c spread))))))
(defun $irelaxed_laneselect_ (n a b c) (%irelaxed-laneselect ($nd) ($r_laneselect) n a b c))

; ---------------------------------------------------------------------
; Relaxed float operations

(defun %pos-nan (f) (%mk nil (%mag f)))

(defun %frelaxed-min (nd r n a b)
  (cond ((%nan-p a) (%relaxed nd r (list ($fmin_ n a b) (list (%pos-nan a)) (list b) (list b))))
        ((%nan-p b) (%relaxed nd r (list ($fmin_ n a b) (list a) (list (%pos-nan b)) (list a))))
        ((and (%zero-p n a) (%zero-p n b) (not (eq (%neg-p a) (%neg-p b))))
         (%relaxed nd r (list ($fmin_ n a b) (list a) (list b) (list (%zero t)))))
        (t ($fmin_ n a b))))
(defun %frelaxed-max (nd r n a b)
  (cond ((%nan-p a) (%relaxed nd r (list ($fmax_ n a b) (list (%pos-nan a)) (list b) (list b))))
        ((%nan-p b) (%relaxed nd r (list ($fmax_ n a b) (list a) (list (%pos-nan b)) (list a))))
        ((and (%zero-p n a) (%zero-p n b) (not (eq (%neg-p a) (%neg-p b))))
         (%relaxed nd r (list ($fmax_ n a b) (list a) (list b) (list (%zero nil)))))
        (t ($fmax_ n a b))))
(defun $frelaxed_min_ (n a b) (%frelaxed-min ($nd) ($r_fmin) n a b))
(defun $frelaxed_max_ (n a b) (%frelaxed-max ($nd) ($r_fmax) n a b))

; fused multiply-add, rounded once (alternative 1 of relaxed_madd)
(defun %fma (n a b c)
  (let ((pneg (not (eq (%neg-p a) (%neg-p b)))))
    (cond ((or (%nan-p a) (%nan-p b) (%nan-p c)) (%canon-nan n))
          ((or (%inf-p a) (%inf-p b))
           (cond ((or (%zero-p n a) (%zero-p n b)) (%canon-nan n))
                 ((and (%inf-p c) (not (eq (%neg-p c) pneg))) (%canon-nan n))
                 (t (%mk pneg (list :inf)))))
          ((%inf-p c) c)
          (t (%round n (+ (* (%val n a) (%val n b)) (%val n c))
                     ;; an exact zero is -0 only if both addends are -0
                     (and pneg (%neg-p c)
                          (or (%zero-p n a) (%zero-p n b)) (%zero-p n c)))))))

(defun %frelaxed-madd (nd r n a b c)
  (%relaxed nd r (list ($fadd_ n (car ($fmul_ n a b)) c) (list (%fma n a b c)))))
(defun $frelaxed_madd_ (n a b c) (%frelaxed-madd ($nd) ($r_fmadd) n a b c))
(defun $frelaxed_nmadd_ (n a b c) ($frelaxed_madd_ n (%fneg a) b c))

; relaxed truncation: trunc where it is defined, else
; relaxed(R)[trunc_sat, R], where the second alternative is any value
; (the prose's \mathbf{R}), so a deterministic implementation takes the
; first whatever R is
(defun $relaxed_trunc__ (m n sx f)
  (or ($trunc__ m n sx f) ($trunc_sat__ m n sx f)))

; ---------------------------------------------------------------------
; Logic mode with time limits (wasm3 M9; config (:logic ... :seconds n)).
; As %TRY-LOGIC / %TRY-GUARDS (prelude.lisp), but every attempt also runs
; under a prover time limit of SECONDS: the step limits alone do not bound
; wall time (one 3.0 guard proof ran more than 15 minutes, prep P5). An
; attempt that hits the limit falls back like one that fails. A time limit
; depends on the machine, so the mode manifest (tests/sem-3.0/modes-3.0.lsp)
; records the result on the machine that wrote it.
(defun %timed (secs ev) (list 'with-prover-time-limit secs ev))
(defun %timed-alts (secs evs) (if (atom evs) nil (cons (%timed secs (car evs)) (%timed-alts secs (cdr evs)))))

(defmacro %try-logic-t (secs ev)
  `(make-event '(:or ,@(%timed-alts secs
                         (list* (list 'with-prover-step-limit 200000 (%logic-version ev))
                                (list 'with-prover-step-limit 2000000 (%gz-version ev))
                                (and (consp ev) (eq (car ev) 'defun) (consp (cdr ev)) (consp (cddr ev))
                                     (true-listp (caddr ev))
                                     (%measure-alts ev (caddr ev)))))
                     ,(%program-version ev))))

(defmacro %try-guards-t (secs name)
  `(make-event '(:or (with-prover-time-limit ,secs (with-prover-step-limit 100000 (verify-guards ,name)))
                     (value-triple :guards-not-verified))))
