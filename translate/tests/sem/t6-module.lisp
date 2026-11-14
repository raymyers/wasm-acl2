; T6 exit check for Module_ok (6-typing.spectec, config :rel-override that
; breaks the C <-> ft* cycle and otherwise calls the GENERATED relations):
; every module of the shared oracle corpus (wasm/*.wasm, parsed by the
; generated GRAM/BMODULE) validates, with one external type per export; and
; deliberately ill-typed variants of a corpus module are rejected.
(in-package "W1T")
(include-book "../../gen/wasm-1.0/wasm1")

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

(defun parse-file (file state)
  (mv-let (bs state) (read-bytes (concatenate 'string "wasm/" file) state)
    (let ((p (gram/bmodule bs)))
      (mv (and p (null (cadr p)) (car p)) state))))

(defconst *corpus*
  '("call_indirect.wasm" "collatz.wasm" "edge_cases.wasm" "float_ops.wasm" "gcd.wasm"
    "hash.wasm" "inf_arith_oracle.wasm" "is_prime.wasm" "nan_oracle.wasm" "packed_mem.wasm"
    "packed_mem_i64.wasm" "signed_zero_oracle.wasm" "sum_array.wasm"))

; module_ok returns (list (:%->% ixt* xt*)): xt* has one entry per export
(defun corpus-ok (files state)
  (if (endp files) (mv nil state)
    (mv-let (m state) (parse-file (car files) state)
      (let ((r (and m (module_ok m))))
        (mv-let (bad state) (corpus-ok (cdr files) state)
          (mv (if (and r (equal (acl2::len (caddr (car r))) (acl2::len (nth 10 m)))) bad (cons (car files) bad))
              state))))))

(make-event
 (mv-let (bad state) (corpus-ok *corpus* state)
   (if bad (mv (msg "Module_ok rejects corpus modules ~x0" bad) nil state)
     (mv nil '(value-triple :corpus-validates) state))))

; mutations of hash.wasm: (:MODULE type* import* func* global* table* mem* elem* data* start? export*)
(defun set-body-last (m instr)              ; replace the function's final instruction
  (let* ((f (car (nth 3 m))) (body (cadddr f)))
    (update-nth 3 (list (list (car f) (cadr f) (caddr f) (append (butlast body 1) (list instr)))) m)))
(defun set-func-type (m x)
  (let ((f (car (nth 3 m)))) (update-nth 3 (list (list* (car f) x (cddr f))) m)))
(defun set-load-align (m a)                 ; the i32.load inside the loop
  (let* ((f (car (nth 3 m))) (body (cadddr f))
         (blk (nth 2 body)) (lp (car (caddr blk))) (ins (caddr lp))
         (ins2 (update-nth 10 (list :load '(:i32) nil (list :%rec (cons :align a) '(:offset . 0))) ins))
         (body2 (update-nth 2 (list (car blk) (cadr blk) (list (list (car lp) (cadr lp) ins2))) body)))
    (update-nth 3 (list (list (car f) (cadr f) (caddr f) body2)) m)))

(defmacro %case (name want form)
  ;; FORM computes a module from M; WANT is :ok or :reject
  `(make-event
    (mv-let (m state) (parse-file "hash.wasm" state)
      (let ((r (module_ok ,form)))
        (if (if (eq ,want :ok) r (not r))
            (mv nil '(value-triple ,name) state)
          (mv (msg "~x0: expected ~x1, Module_ok returned ~x2" ',name ,want r) nil state))))))

(%case :hash-type :ok
       (and (equal (module_ok m)
                   '((:%->% nil ((:mem (:[%..%] 1 nil))
                                 (:func (:%->% ((:i32) (:i32)) ((:i32))))))))
            m))
(%case :align-ok :ok (set-load-align m 2))
(%case :result-type-mismatch :reject (set-body-last m '(:const (:i64) 0)))
(%case :local-out-of-range :reject (set-body-last m '(:local.get 9)))
(%case :type-index-out-of-range :reject (set-func-type m 1))
(%case :func-type-wrong :reject
       (update-nth 1 (list '(:type (:%->% ((:i32)) ((:i32))))) m))
(%case :alignment-too-large :reject (set-load-align m 3))
(%case :two-memories :reject (update-nth 6 (list '(:memory (:[%..%] 1 nil)) '(:memory (:[%..%] 1 nil))) m))
(%case :memory-too-large :reject (update-nth 6 (list '(:memory (:[%..%] 65537 nil))) m))
(%case :no-memory-for-load-and-data :reject
       (update-nth 10 (list (cadr (nth 10 m))) (update-nth 6 nil m)))
(%case :no-memory-for-load :reject       ; data segment removed too: the load alone fails
       (update-nth 10 (list (cadr (nth 10 m))) (update-nth 8 nil (update-nth 6 nil m))))
(%case :duplicate-export-names :reject
       (update-nth 10 (list (list :export '(100 106 98 50) '(:mem 0)) (cadr (nth 10 m))) m))
(%case :export-func-out-of-range :reject
       (update-nth 10 (list (list :export '(100 106 98 50) '(:func 1))) m))
(%case :data-offset-not-i32 :reject
       (update-nth 8 (list '(:data ((:const (:i64) 0)) (72 105))) m))
(%case :data-offset-not-const :reject
       (update-nth 8 (list '(:data ((:const (:i32) 0) (:const (:i32) 0) (:binop (:i32) (:add))) (72 105))) m))
(%case :start-wrong-type :reject (update-nth 9 (list '(:start 0)) m))
