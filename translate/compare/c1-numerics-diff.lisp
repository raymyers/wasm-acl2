; T9 differential test, numeric level: run the hand-written/agentic WASM1
; semantics (../../execution.lisp) on the same 8015 V8 oracle vectors that the
; translated W1T semantics passes (tests/sem/t3-numerics.lisp), and report
; agreement per operation. This book is a REPORT: it certifies whatever the
; numbers are, and prints them (see the .cert.out).
;
; WASM1 encodes floats as exact rationals (:f32.const q) plus keyword atoms
; for NaN, +-Inf and +-0, so V8 results are compared as values: the bit
; pattern is decoded (with W1T's decoder) to a rational or special.
(in-package "WASM")
(include-book "../../execution")
(include-book "../gen/wasm-1.0/wasm1")

(program)

(defun ftype-p (s) (member-equal s '("f32" "f64")))

; bits -> WASM1 value for type ty ("i32" ...)
(defun w1-val (ty bits)
  (cond ((equal ty "i32") (make-i32-val bits))
        ((equal ty "i64") (make-i64-val bits))
        (t (let* ((n (if (equal ty "f32") 32 64))
                  (f (w1t::%bitsf n bits))
                  (pre (if (equal ty "f32") "F32." "F64.")))
             (cond ((w1t::%nan-p f) (intern$ (concatenate 'string pre "NAN") "KEYWORD"))
                   ((w1t::%inf-p f) (intern$ (concatenate 'string pre (if (w1t::%neg-p f) "-INF" "+INF")) "KEYWORD"))
                   ((w1t::%zero-p n f) (intern$ (concatenate 'string pre (if (w1t::%neg-p f) "-0" "+0")) "KEYWORD"))
                   (t (if (equal ty "f32") (make-f32-val (w1t::%val n f)) (make-f64-val (w1t::%val n f)))))))))

(defun result-type (name)
  ;; type of the result: prefix, except comparisons/tests give i32
  (let ((op (subseq name 4 (length name))))
    (if (member-equal op '("eq" "ne" "lt" "gt" "le" "ge" "eqz" "lt_s" "lt_u" "gt_s" "gt_u"
                           "le_s" "le_u" "ge_s" "ge_u"))
        "i32"
      (subseq name 0 3))))

(defun arg-types (name nargs)
  ;; conversions take the source type named after the '_'
  (let* ((op (subseq name 4 (length name)))
         (u (search "_" op)))
    (if (and u (member-equal (subseq op 0 u) '("wrap" "extend" "trunc" "convert" "demote" "promote" "reinterpret")))
        (list (subseq op (1+ u) (+ u 4)))
      (make-list nargs :initial-element (subseq name 0 3)))))

(defun local-gets (i n) (if (zp n) nil (cons (list :local.get i) (local-gets (1+ i) (1- n)))))

(defun w1-vals (tys args)
  (if (endp args) nil (cons (w1-val (car tys) (car args)) (w1-vals (cdr tys) (cdr args)))))

(defun get-result-1 (r)
  (cond ((and (consp r) (eq :done (first r)))
         (top-operand (frame->operand-stack (car (state->call-stack (second r))))))
        ((statep r) (top-operand (current-operand-stack r)))
        (t r)))


(defun w1-run (name args)
  (let* ((locals (w1-vals (arg-types name (len args)) args))
         (instrs (append (local-gets 0 (len args)) (list (list (intern$ (string-upcase name) "KEYWORD"))))))
    (get-result-1
     (run 10 (make-state :store nil
                         :call-stack (list (make-frame :return-arity 1 :locals locals
                                                       :operand-stack (empty-operand-stack)
                                                       :instrs instrs :label-stack nil)
                                           (make-frame :return-arity 0 :locals nil
                                                       :operand-stack (empty-operand-stack)
                                                       :instrs nil :label-stack nil))
                         :memory nil :globals nil)))))

(defun trap-p (r) (or (eq r :trap) (and (consp r) (eq (car r) :trap))))
(defun nan-val-p (v) (member-eq v '(:f32.nan :f64.nan)))

(defun agree-p (want got rty)
  (cond ((eq want :trap) (trap-p got))
        ((eq want :nan) (nan-val-p got))
        (t (equal got (w1-val rty want)))))

; per-op tally: alist name -> (ok . total)
(defun tally (vs acc bad)
  (if (endp vs) (mv acc bad)
    (let* ((v (car vs)) (name (car v)) (args (butlast (cdr v) 1)) (want (car (last v)))
           (got (w1-run name args))
           (ok (agree-p want got (result-type name)))
           (old (or (cdr (assoc-equal name acc)) (cons 0 0)))
           (acc (put-assoc-equal name (cons (+ (car old) (if ok 1 0)) (1+ (cdr old))) acc)))
      (tally (cdr vs) acc (if (or ok (> (len bad) 400)) bad (cons (list v :wasm1 got) bad))))))

(defun sum-ok (acc) (if (endp acc) 0 (+ (car (cdar acc)) (sum-ok (cdr acc)))))
(defun sum-all (acc) (if (endp acc) 0 (+ (cdr (cdar acc)) (sum-all (cdr acc)))))
(defun disagreeing (acc)
  (cond ((endp acc) nil)
        ((< (car (cdar acc)) (cdr (cdar acc))) (cons (car acc) (disagreeing (cdr acc))))
        (t (disagreeing (cdr acc)))))

(make-event
 (mv-let (channel acl2::state) (open-input-channel "../tests/sem/numeric-vectors.lsp" :object acl2::state)
   (mv-let (eofp vs acl2::state) (read-object channel acl2::state)
     (declare (ignore eofp))
     (let ((acl2::state (close-input-channel channel acl2::state)))
       (mv-let (acc bad) (tally vs nil nil)
         (prog2$
          (cw "~%T9 numeric differential (WASM1 vs V8; W1T passes all ~x0):~%  WASM1 agrees on ~x1 of ~x2 vectors.~%  Ops with disagreements, as (op ok . total):~%~x3~%  First disagreements:~%~x4~%"
              (len vs) (sum-ok acc) (sum-all acc) (disagreeing (reverse acc))
              (take (min 25 (len bad)) (reverse bad)))
          (mv nil (list 'value-triple (list 'quote (list :wasm1-ok (sum-ok acc) :total (sum-all acc)))) acl2::state)))))))
