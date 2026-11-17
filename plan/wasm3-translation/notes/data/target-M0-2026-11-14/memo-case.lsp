(ld "portcullis.acl2")
(include-book "2_3-validation_instructions")
(in-package "W3T")
(defconst *c* '(:%rec (:types) (:tags) (:globals) (:mems) (:tables) (:funcs) (:datas) (:elems) (:locals) (:labels) (:return) (:refs) (:recs)))
(defconst *k1* '(:const (:i32) 1))
(defconst *add* '(:binop (:i32) (:add)))
(defun ty (a x b) (list :|%->_%%| a x b))
; 17 instructions, ill-typed (one add too many): rejecting it explores every
; split of Instrs_ok/seq; ~60 s without memoization (config :memoize).
(defconst *ill* (append (make-list 8 :initial-element *k1*) (make-list 9 :initial-element *add*)))
(cw "CASE memo 8 const 9 add : eps->i32 (ill-typed, 17 instrs): expected NIL, got ~x0~%"
    (time$ (instrs_ok *c* *ill* (ty nil nil '((:i32))))))
