; T5 exit check: the oracle corpus runs end to end on the GENERATED
; semantics, with no JS involved: .wasm bytes -> GRAM/BMODULE (A-binary) ->
; $instantiate (9-module: Module_ok validation, allocation, start) ->
; $invoke + STEPS (8-reduction) -> results, compared with V8 on every vector of
; invoke-vectors.lsp (../oracle/gen-invoke-vectors.mjs).
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

(defconst *s0* '(:%rec (:funcs) (:globals) (:tables) (:mems)))

(defun vt-bits (vt) (if (member-eq vt '(:i64 :f64)) 64 32))
(defun to-val (vt bits)
  (list :const (list vt) (if (member-eq vt '(:f32 :f64)) (%bitsf (vt-bits vt) bits) bits)))
(defun to-vals (ts bs) (if (atom ts) nil (cons (to-val (car ts) (car bs)) (to-vals (cdr ts) (cdr bs)))))

(defun val-bits (v)
  ;; one result value -> its bits, or :NAN
  (let ((vt (car (cadr v))) (x (caddr v)))
    (cond ((member-eq vt '(:f32 :f64)) (if (%nan-p x) :nan (%fbits (vt-bits vt) x)))
          (t x))))

(defun vals-bits (vs) (if (atom vs) nil (cons (val-bits (car vs)) (vals-bits (cdr vs)))))

(defun from-vals (vs)
  ;; result instructions -> bits list, :TRAP, or :NAN (a single NaN result)
  (cond ((equal vs '((:trap))) :trap)
        (t (let ((bs (vals-bits vs)))
             (if (and (consp bs) (eq (car bs) :nan) (null (cdr bs))) :nan bs)))))

(defun chars (s) (if (atom s) nil (cons (char-code (car s)) (chars (cdr s)))))

(defun find-export (name exs)
  (cond ((atom exs) nil)
        ((equal (%get-field (car exs) :name) (chars (coerce name 'list)))
         (%get-field (car exs) :addr))
        (t (find-export name (cdr exs)))))

; instantiate a parsed module and run its start function: (mv store moduleinst) or nil
(defun instantiate-run (m)
  (let* ((c ($instantiate *s0* m nil))
         (r (and c (steps c))))
    (and r (let* ((z (cadr (car r))) (s (cadr z)) (f (caddr z)))
             (list s (%get-field f :module))))))

(defun run-vector (v mods)
  ;; v = (file export types args want)
  (let* ((inst (cdr (assoc-equal (first v) mods))))
    (if (null inst) :no-instance
      (let* ((s (first inst)) (mi (second inst))
             (addr (find-export (second v) (%get-field mi :exports))))
        (if (not (and (consp addr) (eq (car addr) :func))) :no-export
          (let ((r (steps ($invoke s (cadr addr) (to-vals (third v) (fourth v))))))
            (if (null r) :no-normal-form (from-vals (caddr (car r))))))))))

(defun remove-if-not-cdr (al) (cond ((atom al) nil) ((cdr (car al)) (cons (car al) (remove-if-not-cdr (cdr al)))) (t (remove-if-not-cdr (cdr al)))))

(defun check-all (vs mods nok bad)
  (if (endp vs) (mv nok (reverse bad))
    (let* ((v (car vs)) (want (fifth v)) (got (run-vector v mods)))
      (if (equal got want) (check-all (cdr vs) mods (1+ nok) bad)
        (check-all (cdr vs) mods nok (cons (list v :got got) bad))))))

(defun load-modules (files acc state)
  ;; alist file -> (store moduleinst), instantiating each corpus module once
  (if (endp files) (mv acc state)
    (mv-let (bs state) (read-bytes (concatenate 'string "wasm/" (car files)) state)
      (let* ((p (gram/bmodule bs))
             (inst (and p (null (cadr p)) (instantiate-run (car p)))))
        (load-modules (cdr files) (acons (car files) inst acc) state)))))

(make-event
 (mv-let (channel state) (open-input-channel "invoke-vectors.lsp" :object state)
   (mv-let (eofp vs state) (read-object channel state)
     (declare (ignore eofp))
     (let ((state (close-input-channel channel state)))
       (mv-let (mods state) (load-modules (remove-duplicates-equal (strip-cars vs)) nil state)
         (mv-let (nok bad) (check-all vs mods 0 nil)
           (prog2$ (cw "~%T5 invoke: ~x0 of ~x1 vectors agree with V8 (modules instantiated: ~x2 of ~x3).~%  First disagreements: ~x4~%"
                       nok (acl2::len vs) (acl2::len (remove-if-not-cdr mods)) (acl2::len mods)
                       (take (min 12 (acl2::len bad)) bad))
                   (if bad (mv (msg "~x0 vectors disagree" (acl2::len bad)) nil state)
                     (mv nil '(value-triple :t5-invoke-ok) state)))))))))
