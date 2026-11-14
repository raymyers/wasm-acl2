; Hand-written SpecTec builtins (hint(builtin) in 3-numerics.spectec) and
; config overrides (il2acl2-config.lsp) for the generated W1T semantics.
; These are the ONLY hand-written semantic definitions (plan §2.4).
;
; Encoding (plan §2.2): iN/uN/byte/char are naturals; fN is (:POS mag) or
; (:NEG mag) with mag = (:NORM m e) | (:SUBNORM m) | (:INF) | (:NAN m);
; a NAN payload m is the significand; ? and * are lists.
(in-package "W1T")

(include-book "prelude")

; ---------------------------------------------------------------------
; Override: $utf8 (il2acl2-config.lsp). UTF-8 encoding of a char list,
; matching the four clauses of A-binary.spectec $utf8.

(defun %utf8-char (c)
  (declare (xargs :guard (natp c)))
  (cond ((< c #x80) (list c))
        ((< c #x800) (list (+ #xC0 (floor c 64)) (+ #x80 (mod c 64))))
        ((< c #x10000) (list (+ #xE0 (floor c 4096))
                             (+ #x80 (mod (floor c 64) 64))
                             (+ #x80 (mod c 64))))
        (t (list (+ #xF0 (floor c 262144))
                 (+ #x80 (mod (floor c 4096) 64))
                 (+ #x80 (mod (floor c 64) 64))
                 (+ #x80 (mod c 64))))))

(defun $utf8 (chs)
  (declare (xargs :guard (nat-listp chs)))
  (if (atom chs) nil (append (%utf8-char (car chs)) ($utf8 (cdr chs)))))

; ---------------------------------------------------------------------
; Builtins. TODO(T3): implement; until then each signals an error.

(defmacro %builtin-stub (name &rest formals)
  `(defun ,name ,formals
     (declare (ignore ,@formals) (xargs :guard t))
     (prog2$ (er hard? ',name "Builtin not implemented yet (T3)") nil)))

(%builtin-stub $TRUNCZ a1)
(%builtin-stub $FABS_ a1 a2)
(%builtin-stub $FCEIL_ a1 a2)
(%builtin-stub $FFLOOR_ a1 a2)
(%builtin-stub $FNEAREST_ a1 a2)
(%builtin-stub $FNEG_ a1 a2)
(%builtin-stub $FSQRT_ a1 a2)
(%builtin-stub $FTRUNC_ a1 a2)
(%builtin-stub $ICLZ_ a1 a2)
(%builtin-stub $ICTZ_ a1 a2)
(%builtin-stub $IPOPCNT_ a1 a2)
(%builtin-stub $FADD_ a1 a2 a3)
(%builtin-stub $FCOPYSIGN_ a1 a2 a3)
(%builtin-stub $FDIV_ a1 a2 a3)
(%builtin-stub $FMAX_ a1 a2 a3)
(%builtin-stub $FMIN_ a1 a2 a3)
(%builtin-stub $FMUL_ a1 a2 a3)
(%builtin-stub $FSUB_ a1 a2 a3)
(%builtin-stub $IAND_ a1 a2 a3)
(%builtin-stub $IOR_ a1 a2 a3)
(%builtin-stub $IROTL_ a1 a2 a3)
(%builtin-stub $IROTR_ a1 a2 a3)
(%builtin-stub $ISHL_ a1 a2 a3)
(%builtin-stub $ISHR_ a1 a2 a3 a4)
(%builtin-stub $IXOR_ a1 a2 a3)
(%builtin-stub $FEQ_ a1 a2 a3)
(%builtin-stub $FGE_ a1 a2 a3)
(%builtin-stub $FGT_ a1 a2 a3)
(%builtin-stub $FLE_ a1 a2 a3)
(%builtin-stub $FLT_ a1 a2 a3)
(%builtin-stub $FNE_ a1 a2 a3)
(%builtin-stub $CONVERT__ a1 a2 a3 a4)
(%builtin-stub $DEMOTE__ a1 a2 a3)
(%builtin-stub $EXTEND__ a1 a2 a3 a4)
(%builtin-stub $PROMOTE__ a1 a2 a3)
(%builtin-stub $REINTERPRET__ a1 a2 a3)
(%builtin-stub $TRUNC__ a1 a2 a3 a4)
(%builtin-stub $WRAP__ a1 a2 a3)
(%builtin-stub $IBYTES_ a1 a2)
(%builtin-stub $FBYTES_ a1 a2)
(%builtin-stub $BYTES_ a1 a2)
(%builtin-stub $INV_IBYTES_ a1 a2)
(%builtin-stub $INV_FBYTES_ a1 a2)
(%builtin-stub $INV_BYTES_ a1 a2)
(%builtin-stub $INOT_ a1 a2)
