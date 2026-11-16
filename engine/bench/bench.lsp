; E0 (plan/wasm-engine): steps per second of the generated 3.0 semantics on
; the benchmark set. Each wasm/NAME-PAGES.wasm goes through the generated
; decoder (GRAM/BMODULE), $instantiate (with Module_ok) and $invoke, then
; STEP is iterated until no rule applies; only the STEP loop is timed.
; From engine/bench, inside `nix develop ../..` after `sh build.sh`:
;   acl2 < bench.lsp > ../../plan/wasm-engine/notes/data/e0-baseline/bench.out
(ld "../../translate/gen/wasm-3.0/portcullis.acl2")
(include-book "../../translate/gen/wasm-3.0/wasm3")
(in-package "W3T")
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

(defconst *s0* '(:%rec (:tags) (:globals) (:mems) (:tables) (:funcs) (:datas) (:elems) (:structs) (:arrays) (:exns)))

; (mv steps final-config): STEP until it returns nil or the fuel is used up
(defun run-steps (c k n)
  (if (zp k) (mv n c)
    (let ((r (step c))) (if (atom r) (mv n c) (run-steps (car r) (1- k) (1+ n))))))

(defun find-export (field exs)
  (cond ((atom exs) nil)
        ((equal (%get-field (car exs) :name) field) (%get-field (car exs) :addr))
        (t (find-export field (cdr exs)))))
(defun str-bytes (s) (if (atom s) nil (cons (char-code (car s)) (str-bytes (cdr s)))))

; instantiate FILE, invoke export FIELD on ARGS (3.0 values), run to the end
(defun bench1 (file field args state)
  (mv-let (bs state) (read-bytes file state)
    (let* ((p (and bs (gram/bmodule bs)))
           (m (and p (null (cadr p)) (car p)))
           (c0 (and m ($instantiate *s0* m nil))))
      (mv-let (n0 cf0) (if c0 (run-steps c0 10000000 0) (mv 0 nil))
        (let* ((s (and cf0 (cadr (cadr cf0))))
               (f (and cf0 (caddr (cadr cf0))))
               (inst (and f (%get-field f :module)))
               (addr (and inst (find-export (str-bytes (coerce field 'list)) (%get-field inst :exports))))
               (c (and addr ($invoke s (cadr addr) args))))
          (mv-let (t0 state) (read-run-time state)
            (mv-let (n cf) (if c (run-steps c 100000000 0) (mv 0 nil))
              (mv-let (t1 state) (read-run-time state)
                (let ((secs (- t1 t0)))
                  (prog2$
                   (cw "BENCH ~s0 ~s1 ~x2: inst-steps ~x3 steps ~x4 ms ~x5 steps/s ~x6 result ~x7~%"
                       file field args n0 n
                       (if (rationalp secs) (round (* 1000 secs) 1) "?")
                       (if (and (rationalp secs) (< 0 secs)) (round (/ n secs) 1) 0)
                       (and cf (caddr cf)))
                   (mv nil :ok state)))))))))))

(defun i32 (n) (list :const '(:i32) n))
(defun i64 (n) (list :const '(:i64) n))

; NAME at 1, 16 and 64 pages: export FIELD on the one argument ARG
(defun b3 (name field arg state)
  (er-progn (bench1 (concatenate 'string "wasm/" name "-1.wasm") field (list arg) state)
            (bench1 (concatenate 'string "wasm/" name "-16.wasm") field (list arg) state)
            (bench1 (concatenate 'string "wasm/" name "-64.wasm") field (list arg) state)))
