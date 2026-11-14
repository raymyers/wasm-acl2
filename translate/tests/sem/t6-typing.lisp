; T6 check: the GENERATED typing relations (6-typing.spectec). Instr_ok and
; Instrs_ok are multi-mode: INSTRS_OK checks C |- instrs : t1* -> t2* with
; everything given; INSTRS_OK/SPLIT computes t2* from t1* (dropping only the
; stack-polymorphic rules unreachable/br/br_table/return, which the check
; variant keeps). Expr_ok and Func_ok compute their types.
(in-package "W1T")
(include-book "../../gen/wasm1")

(defmacro %check (name form)
  `(make-event (if ,form '(value-triple ,name)
                 (er hard ',name "check failed: ~x0" ',form))))

(defun i32c (n) (list :const '(:i32) n))
(defun ft (in out) (list :|%->%| in out))
; context {TYPES, FUNCS, GLOBALS, TABLES, MEMS, LOCALS, LABELS, RETURN}
(defun ctx (types locals labels ret)
  (list :%rec (cons :types types) '(:funcs) '(:globals) '(:tables) '(:mems)
        (cons :locals locals) (cons :labels labels) (cons :return ret)))
(defconst *c0* (ctx nil nil nil nil))

; straight-line code
(%check :add (instrs_ok *c0* (list (i32c 1) (i32c 2) '(:binop (:i32) (:add)))
                        (ft nil '((:i32)))))
(%check :add-split (equal (instrs_ok/split *c0* (list (i32c 1) (i32c 2) '(:binop (:i32) (:add))) nil)
                          '(((:i32)))))
(%check :ill-typed-underflow
        (not (instrs_ok *c0* (list (i32c 1) '(:binop (:i32) (:add))) (ft nil '((:i32))))))
(%check :ill-typed-mismatch
        (not (instrs_ok *c0* (list (i32c 1) '(:const (:i64) 2) '(:binop (:i32) (:add)))
                        (ft nil '((:i32))))))
(%check :wrong-result
        (not (instrs_ok *c0* (list (i32c 1)) (ft nil '((:i64))))))

; locals
(%check :local-get
        (instrs_ok (ctx nil '((:i32) (:i64)) nil nil) (list '(:local.get 1)) (ft nil '((:i64)))))
(%check :local-oob
        (not (instrs_ok (ctx nil '((:i32)) nil nil) (list '(:local.get 3)) (ft nil '((:i32))))))

; br at the end of a block body: typed by the check variant
(%check :block-br
        (instrs_ok *c0* (list (list :block '((:i32)) (list (i32c 7) '(:br 0))))
                   (ft nil '((:i32)))))
(%check :br-label-oob
        (not (instrs_ok *c0* (list (list :block nil (list '(:br 3)))) (ft nil nil))))
; unreachable: any type, in checking position
(%check :unreachable
        (instrs_ok *c0* (list '(:unreachable)) (ft '((:i64)) '((:f32) (:i32)))))

; Expr_ok is multi-mode too (it calls Instrs_ok): EXPR_OK/SPLIT computes the
; result type, EXPR_OK checks a given one
(%check :expr-ok (equal (expr_ok/split *c0* (list (i32c 1) '(:testop (:i32) (:eqz)))) '(((:i32)))))
(%check :expr-ok-check (expr_ok *c0* (list (i32c 1) '(:testop (:i32) (:eqz))) '((:i32))))

; Func_ok: factorial (locals n : i32 param, acc : i32 local) : i32 -> i32
(defconst *fact-body*
  (list (list :block nil
              (list (list :loop nil
                          (list '(:local.get 0) '(:testop (:i32) (:eqz)) '(:br_if 1)
                                '(:local.get 1) '(:local.get 0) '(:binop (:i32) (:mul)) '(:local.set 1)
                                '(:local.get 0) (i32c 1) '(:binop (:i32) (:sub)) '(:local.set 0)
                                '(:br 0)))))
        '(:local.get 1)))
(%check :func-ok-factorial
        ;; FUNC_OK/SPLIT: given C, func and t_1* (the split of t_1* -> t_2?), computes t_2?
        (equal (func_ok/split (ctx (list (ft '((:i32)) '((:i32)))) nil nil nil)
                              (list :func 0 '((:local (:i32))) *fact-body*) '((:i32)))
               '(((:i32)))))
(%check :func-ok-factorial-check
        (func_ok (ctx (list (ft '((:i32)) '((:i32)))) nil nil nil)
                 (list :func 0 '((:local (:i32))) *fact-body*) (ft '((:i32)) '((:i32)))))
(%check :func-ill-typed
        (not (func_ok (ctx (list (ft '((:i32)) '((:i64)))) nil nil nil)
                      (list :func 0 '((:local (:i32))) *fact-body*) (ft '((:i32)) '((:i64))))))
; a body ending in a stack-polymorphic instruction (return): INSTRS_OK/SPLIT
; drops return, but Func_ok binds t_2? from C.TYPES[x] before its Expr_ok
; premise, which therefore uses the check variant (multi-mode propagation)
(defconst *ret-body* (list (list :block '((:i32)) (list (i32c 1))) '(:return)))
(%check :expr-return-split          ; types via the candidate fallback (see t6 dead-code checks)
        (expr_ok/split (ctx nil nil '(((:i32))) '(((:i32)))) *ret-body*))
(%check :func-return-split
        (equal (func_ok/split (ctx (list (ft nil '((:i32)))) nil nil nil) (list :func 0 nil *ret-body*) nil)
               '(((:i32)))))
(%check :func-return-check
        (func_ok (ctx (list (ft nil '((:i32)))) nil nil nil) (list :func 0 nil *ret-body*) (ft nil '((:i32)))))
(%check :func-return-check-wrong-type
        (not (func_ok (ctx (list (ft nil '((:i64)))) nil nil nil) (list :func 0 nil *ret-body*) (ft nil '((:i64))))))

; dead code after a stack-polymorphic instruction in the middle of a sequence
; (spec-test-1 block.wast): Instrs_ok/seq needs the intermediate stack t_2*,
; which the output variant cannot compute after br. The candidate fallback
; tries t_2* from {eps, bound lists} and CHECKS each, so this stays sound.
(%check :dead-code-br-unreachable
        (instrs_ok *c0* (list (list :block nil (list '(:br 0) '(:unreachable)))) (ft nil nil)))
(%check :dead-code-br-then-locals
        (instrs_ok (ctx nil '((:i32)) nil nil)
                   (list (list :block nil (list '(:br 0) '(:local.get 0) (i32c 100) '(:binop (:i32) (:mul)) '(:local.set 0))))
                   (ft nil nil)))
(%check :dead-code-still-checked                ; ill-typed dead code is still rejected
        (not (instrs_ok *c0* (list (list :block nil (list '(:br 0) '(:local.get 0)))) (ft nil nil))))
(%check :dead-code-br_table
        (instrs_ok *c0* (list (list :block nil (list (i32c 0) '(:br_table nil 0) '(:unreachable)))) (ft nil nil)))
