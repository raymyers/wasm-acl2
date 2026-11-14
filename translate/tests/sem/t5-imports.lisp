; T5/T6 check for imports: the GENERATED $instantiate checks every provided
; extern address against the module's import types with the generated
; Externaddr_ok (multi-mode: check variant with the /sub rule, which uses the
; output variant EXTERNADDR_OK/SPLIT for the exact type xt'). Module A is a
; corpus module (gcd.wasm, hash.wasm) instantiated from its bytes; module B is
; written here in the IL syntax and imports from A's instance.
(in-package "W1T")
(include-book "../../gen/wasm1")

(program)
(set-state-ok t)

(defun read-bytes-loop (channel acc state)
  (mv-let (b state) (read-byte$ channel state)
    (if (null b) (mv (reverse acc) state) (read-bytes-loop channel (cons b acc) state))))

(defun read-bytes (file state)
  (mv-let (channel state) (open-input-channel file :byte state)
    (if (null channel) (mv nil state)
      (mv-let (bs state) (read-bytes-loop channel nil state)
        (let ((state (close-input-channel channel state))) (mv bs state))))))

(defun chars (s) (if (atom s) nil (cons (char-code (car s)) (chars (cdr s)))))
(defun nm (s) (chars (coerce s 'list)))

(defun find-export (name exs)
  (cond ((atom exs) nil)
        ((equal (%get-field (car exs) :name) (nm name)) (%get-field (car exs) :addr))
        (t (find-export name (cdr exs)))))

; (store moduleinst) after instantiation and the start function, or nil
(defun inst (s m addrs)
  (let* ((c ($instantiate s m addrs)) (r (and c (steps c))))
    (and r (let ((z (cadr (car r)))) (list (cadr z) (%get-field (caddr z) :module))))))

(defun invoke (sm name args)
  (let* ((addr (find-export name (%get-field (second sm) :exports)))
         (r (and (consp addr) (steps ($invoke (first sm) (cadr addr) args)))))
    (and r (caddr (car r)))))

(defconst *s0* '(:%rec (:funcs) (:globals) (:tables) (:mems)))
(defconst *ii-i* '(:%->% ((:i32) (:i32)) ((:i32))))

; B: (import "a" "gcd" (func (param i32 i32) (result i32)))
;    (func (export "gcd1") (param i32 i32) (result i32) local.get 0 local.get 1 call 0 i32.const 1 i32.add)
(defun mod-b (import-type)
  (list :module (list (list :type *ii-i*))
        (list (list :import (nm "a") (nm "gcd") import-type))
        (list '(:func 0 nil ((:local.get 0) (:local.get 1) (:call 0) (:const (:i32) 1) (:binop (:i32) (:add)))))
        nil nil nil nil nil nil
        (list (list :export (nm "gcd1") '(:func 1)))))

; C: (import "a" "memory" (memory <limits>)) (func (export "first") (result i32) i32.const 0 i32.load8_u)
(defun mod-c (limits)
  (list :module (list '(:type (:%->% nil ((:i32)))))
        (list (list :import (nm "a") (nm "memory") (list :mem limits)))
        (list '(:func 0 nil ((:const (:i32) 0) (:load (:i32) ((:_ 8 (:u))) (:%rec (:align . 0) (:offset . 0))))))
        nil nil nil nil nil nil
        (list (list :export (nm "first") '(:func 0)))))

(defmacro %case (name want form)
  ;; FORM may use A (gcd instance), AG (its gcd address), H (hash instance), HM (its memory address)
  `(make-event
    (mv-let (bs state) (read-bytes "wasm/gcd.wasm" state)
      (mv-let (bh state) (read-bytes "wasm/hash.wasm" state)
        (let* ((a (inst *s0* (car (gram/bmodule bs)) nil))
               (ag (find-export "gcd" (%get-field (second a) :exports)))
               (h (inst (first a) (car (gram/bmodule bh)) nil))
               (hm (find-export "memory" (%get-field (second h) :exports)))
               (got ,form))
          (declare (ignorable a ag h hm))
          (if (equal got ,want) (mv nil '(value-triple ,name) state)
            (mv (msg "~x0: expected ~x1, got ~x2" ',name ,want got) nil state)))))))

(%case :import-func-call '((:const (:i32) 7))
       (invoke (inst (first a) (mod-b (list :func *ii-i*)) (list ag)) "gcd1" '((:const (:i32) 12) (:const (:i32) 18))))
(%case :import-func-wrong-type nil
       (inst (first a) (mod-b '(:func (:%->% ((:i64) (:i64)) ((:i64))))) (list ag)))
(%case :import-func-addr-out-of-range nil
       (inst (first a) (mod-b (list :func *ii-i*)) '((:func 99))))
(%case :import-kind-mismatch nil
       (inst (first a) (mod-b (list :func *ii-i*)) (list hm)))
(%case :import-count-mismatch nil
       (inst (first a) (mod-b (list :func *ii-i*)) nil))
; memories: hash.wasm's memory has limits [1..]; the data segment puts 72 at 0
(%case :import-mem-exact '((:const (:i32) 72))
       (invoke (inst (first h) (mod-c '(:[%..%] 1 nil)) (list hm)) "first" nil))
(%case :import-mem-sub '((:const (:i32) 72))            ; [1..] <: [0..] by Externaddr_ok/sub
       (invoke (inst (first h) (mod-c '(:[%..%] 0 nil)) (list hm)) "first" nil))
(%case :import-mem-min-too-large nil                     ; [1..] is not <: [2..]
       (inst (first h) (mod-c '(:[%..%] 2 nil)) (list hm)))
(%case :import-mem-max-required nil                      ; [1..] (no max) is not <: [1..1]
       (inst (first h) (mod-c '(:[%..%] 1 (1))) (list hm)))
