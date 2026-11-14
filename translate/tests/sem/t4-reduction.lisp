; T4 exit check: hand-built configurations run to completion under the
; generated reduction relations (STEP_PURE / STEP_READ / STEP, and STEPS, the
; generated refl/trans closure of STEP).
(in-package "W1T")
(include-book "../../gen/wasm1")

(program) ; STEP and STEPS are in :program mode until T8

(defmacro %check (name form)
  `(make-event (if ,form '(value-triple ,name)
                 (er hard ',name "check failed: ~x0" ',form))))

; --- configurations in the W1T encoding (plan §2.2) ---------------------
(defun i32c (n) (list :const '(:i32) n))
(defun mod-inst (funcs)
  ;; memory address 0 is the (optional) store memory 0
  (list :%rec '(:types) (cons :funcs funcs) '(:globals) '(:tables) '(:mems 0) '(:exports)))
(defun store (funcs mems)
  (list :%rec (cons :funcs funcs) '(:globals) '(:tables) (cons :mems mems)))
(defun cfg (store locals mi instrs)
  (list :|%;%| (list :|%;%| store (list :%rec (cons :locals locals) (cons :module mi))) instrs))
(defun run (instrs locals)
  ;; final instruction sequence of the normal form
  (let ((r (steps (cfg (store nil nil) locals (mod-inst nil) instrs))))
    (and r (caddr (car r)))))

; --- programs -------------------------------------------------------------
(%check :add (equal (run (list (i32c 1) (i32c 2) '(:binop (:i32) (:add))) nil)
                    (list (i32c 3))))
(%check :wrap (equal (run (list (i32c 4294967295) (i32c 2) '(:binop (:i32) (:add))) nil)
                     (list (i32c 1))))
(%check :trap (equal (run (list (i32c 1) (i32c 0) '(:binop (:i32) (:div (:u)))) nil)
                     '((:trap))))
(%check :select (equal (run (list (i32c 10) (i32c 20) (i32c 0) '(:select)) nil)
                       (list (i32c 20))))
(%check :block-br
        (equal (run (list (list :block '((:i32)) (list (i32c 7) '(:br 0) (i32c 9)))) nil)
               (list (i32c 7))))
(%check :if-else
        (equal (run (list (i32c 0) (list :ifelse '((:i32)) (list (i32c 1)) (list (i32c 2)))) nil)
               (list (i32c 2))))
(%check :nested-br
        (equal (run (list (list :block '((:i32))
                                (list (list :block nil (list (i32c 5) '(:br 1)))
                                      (i32c 6))))
                    nil)
               (list (i32c 5))))

; factorial: locals n, acc
(defconst *fact*
  (list (list :block nil
              (list (list :loop nil
                          (list '(:local.get 0) '(:testop (:i32) (:eqz)) '(:br_if 1)
                                '(:local.get 1) '(:local.get 0) '(:binop (:i32) (:mul)) '(:local.set 1)
                                '(:local.get 0) (i32c 1) '(:binop (:i32) (:sub)) '(:local.set 0)
                                '(:br 0)))))
        '(:local.get 1)))
(%check :factorial-5 (equal (run *fact* (list (i32c 5) (i32c 1))) (list (i32c 120))))
(%check :factorial-10 (equal (run *fact* (list (i32c 10) (i32c 1))) (list (i32c 3628800))))

; fibonacci: locals n, a, b, t
(defconst *fib*
  (list (list :block nil
              (list (list :loop nil
                          (list '(:local.get 0) '(:testop (:i32) (:eqz)) '(:br_if 1)
                                '(:local.get 1) '(:local.get 2) '(:binop (:i32) (:add)) '(:local.set 3)
                                '(:local.get 2) '(:local.set 1) '(:local.get 3) '(:local.set 2)
                                '(:local.get 0) (i32c 1) '(:binop (:i32) (:sub)) '(:local.set 0)
                                '(:br 0)))))
        '(:local.get 1)))
(%check :fibonacci-10
        (equal (run *fib* (list (i32c 10) (i32c 0) (i32c 1) (i32c 0))) (list (i32c 55))))

; function call: func 0 = (i32,i32)->i32 adding its locals
(defconst *add-func*
  (list :func 0 nil (list '(:local.get 0) '(:local.get 1) '(:binop (:i32) (:add)))))
(defconst *ft* '(:|%->%| ((:i32) (:i32)) ((:i32))))
(defun mi-with-add () (list :%rec (list :types *ft*) '(:funcs 0) '(:globals) '(:tables) '(:mems) '(:exports)))
(%check :call
        (let* ((mi (mi-with-add))
               (fi (list :%rec (cons :type *ft*) (cons :module mi) (cons :code *add-func*)))
               (r (steps (cfg (store (list fi) nil) nil mi
                              (list (i32c 40) (i32c 2) '(:call 0))))))
          (and r (equal (caddr (car r)) (list (i32c 42))))))

; memory: store then load (64-byte memory; the rules bounds-check against |BYTES|)
(%check :memory
        (let* ((mem (list :%rec '(:type :|[%..%]| 1 nil) (cons :bytes (make-list 64 :initial-element 0))))
               (ma '(:%rec (:align . 2) (:offset . 0)))
               (r (steps (cfg (store nil (list mem)) nil (mod-inst nil)
                              (list (i32c 8) (i32c 305419896) (list :store '(:i32) nil ma)
                                    (i32c 8) (list :load '(:i32) nil ma))))))
          (and r (equal (caddr (car r)) (list (i32c 305419896))))))

; out-of-bounds store traps
(%check :memory-oob
        (let* ((mem (list :%rec '(:type :|[%..%]| 1 nil) (cons :bytes (make-list 64 :initial-element 0))))
               (ma '(:%rec (:align . 2) (:offset . 0)))
               (r (steps (cfg (store nil (list mem)) nil (mod-inst nil)
                              (list (i32c 62) (i32c 1) (list :store '(:i32) nil ma))))))
          (and r (equal (caddr (car r)) '((:trap))))))

; return from a function body exits all labels
(%check :return
        (let* ((ft '(:|%->%| nil ((:i32))))
               (code (list :func 0 nil (list (list :block nil (list (i32c 9) '(:return))) (i32c 1))))
               (mi (list :%rec (list :types ft) '(:funcs 0) '(:globals) '(:tables) '(:mems) '(:exports)))
               (fi (list :%rec (cons :type ft) (cons :module mi) (cons :code code)))
               (r (steps (cfg (store (list fi) nil) nil mi (list '(:call 0))))))
          (and r (equal (caddr (car r)) (list (i32c 9))))))

; a full 64KiB page: memory.size = 1, and a store/load at the last word
(%check :memory-page
        (let* ((mem (list :%rec '(:type :|[%..%]| 1 nil) (cons :bytes (make-list 65536 :initial-element 0))))
               (ma '(:%rec (:align . 2) (:offset . 0)))
               (r (steps (cfg (store nil (list mem)) nil (mod-inst nil)
                              (list '(:memory.size)
                                    (i32c 65532) (i32c 7) (list :store '(:i32) nil ma)
                                    (i32c 65532) (list :load '(:i32) nil ma)
                                    '(:binop (:i32) (:add)))))))
          (and r (equal (caddr (car r)) (list (i32c 8))))))
