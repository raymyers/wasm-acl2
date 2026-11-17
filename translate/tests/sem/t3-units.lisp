; T3 unit checks named in the plan: $iadd_, $idiv_ (trap = empty option),
; $signed_, $fadd_ with NaN / Inf / signed zero. ($iadd_ .. $irem_ and the
; signed helpers are generated from 3-numerics.spectec; $fadd_ is a builtin.)
(in-package "W1T")
(include-book "../../gen/wasm-1.0/wasm1")

(defmacro %check (name form)
  `(make-event (if ,form '(value-triple ,name)
                 (er hard ',name "check failed: ~x0" ',form))))

(%check :iadd (and (equal ($iadd_ 32 (1- (expt 2 32)) 1) 0)
                   (equal ($iadd_ 8 200 100) 44)))
(%check :idiv (and (equal ($idiv_ 32 '(:u) 7 2) '(3))
                   (equal ($idiv_ 32 '(:u) 7 0) nil)                    ; trap
                   (equal ($idiv_ 32 '(:s) (- (expt 2 32) 7) 2)         ; -7/2 = -3
                          (list (- (expt 2 32) 3)))
                   (equal ($idiv_ 32 '(:s) (expt 2 31) (1- (expt 2 32))) nil)  ; INT_MIN/-1
                   (equal ($irem_ 32 '(:s) (expt 2 31) (1- (expt 2 32))) '(0))))
(%check :signed (and (equal ($signed_ 32 (1- (expt 2 32))) -1)
                     (equal ($inv_signed_ 32 (- (expt 2 31))) (expt 2 31))))
(%check :fadd
        (let ((pz '(:pos (:subnorm 0))) (nz '(:neg (:subnorm 0)))
              (+inf '(:pos (:inf))) (-inf '(:neg (:inf))) (one '(:pos (:norm 0 0))))
          (and (equal ($fadd_ 32 nz nz) (list nz))
               (equal ($fadd_ 32 pz nz) (list pz))
               (equal ($fadd_ 32 one '(:neg (:norm 0 0))) (list pz))
               (equal ($fadd_ 64 +inf one) (list +inf))
               (%nan-p (car ($fadd_ 64 +inf -inf)))
               (%nan-p (car ($fadd_ 32 '(:pos (:nan 1)) one)))
               (equal ($fadd_ 32 one one) '((:pos (:norm 0 1)))))))
