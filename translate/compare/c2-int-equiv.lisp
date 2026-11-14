; T9 equivalence theorems, integer level: the TRANSLATED W1T dispatch
; ($binop_ from 3-numerics.spectec + rt/builtins.lisp) equals the bit-vector
; expressions the WASM1 tree uses for the same instructions
; (execution.lisp: (def-i32-binop execute-i32.add (bvplus 32 v1 v2)), ...).
; WASM1's own proofs (proofs/proof-add-spec.lisp etc.) connect its `run` to
; those same BV expressions, so these lemmas link the two semantics.
(in-package "WASM")
(include-book "../../execution")
(include-book "../gen/wasm1")
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvminus" :dir :system)
(include-book "kestrel/bv/bvmult" :dir :system)
(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))   ; unsigned-byte-p-of-logand
(local (include-book "kestrel/bv/logior" :dir :system))   ; unsigned-byte-p-of-logior-strong
(local (include-book "kestrel/bv/logxor" :dir :system))   ; unsigned-byte-p-of-logxor

; SpecTec's remainder (\) is truncating (Z.rem); on naturals it is mod.
(local (defthm rem-is-mod-on-naturals
         (implies (and (natp x) (posp y)) (equal (rem x y) (mod x y)))
         :hints (("Goal" :in-theory (enable rem mod)))))

; Logical ops: both sides meet at bvchop (our %u is mod 2^n).
(local (defthm mod-expt2-is-bvchop
         (implies (and (integerp x) (natp n))
                  (equal (mod x (expt 2 n)) (acl2::bvchop n x)))
         :hints (("Goal" :in-theory (enable acl2::bvchop)))))

(defmacro def-binop-equiv (name n vt op bv)
  `(defthm ,name
     (implies (and (unsigned-byte-p ,n a) (unsigned-byte-p ,n b))
              (equal (w1t::$binop_ ',vt ',op a b)
                     (list (,bv ,n a b))))
     :hints (("Goal" :in-theory
              ,(if (member-eq bv '(acl2::bvand acl2::bvor acl2::bvxor))
                   '(enable acl2::bvand acl2::bvor acl2::bvxor acl2::bvchop)
                 '(enable acl2::bvplus acl2::bvminus acl2::bvmult acl2::bvchop))))))

(def-binop-equiv i32-add-equiv 32 (:i32) (:add) acl2::bvplus)
(def-binop-equiv i32-sub-equiv 32 (:i32) (:sub) acl2::bvminus)
(def-binop-equiv i32-mul-equiv 32 (:i32) (:mul) acl2::bvmult)
(def-binop-equiv i32-and-equiv 32 (:i32) (:and) acl2::bvand)
(def-binop-equiv i32-or-equiv  32 (:i32) (:or)  acl2::bvor)
(def-binop-equiv i32-xor-equiv 32 (:i32) (:xor) acl2::bvxor)
(def-binop-equiv i64-add-equiv 64 (:i64) (:add) acl2::bvplus)
(def-binop-equiv i64-sub-equiv 64 (:i64) (:sub) acl2::bvminus)
(def-binop-equiv i64-mul-equiv 64 (:i64) (:mul) acl2::bvmult)
(def-binop-equiv i64-and-equiv 64 (:i64) (:and) acl2::bvand)
(def-binop-equiv i64-or-equiv  64 (:i64) (:or)  acl2::bvor)
(def-binop-equiv i64-xor-equiv 64 (:i64) (:xor) acl2::bvxor)
