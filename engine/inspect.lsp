; The script of engine/THEOREM.md: print the engine's two theorems as ACL2
; holds them, check that no book under them has a skipped proof, an axiom or
; a trust tag, and evaluate both sides of each theorem on one small program.
; From engine/, inside nix develop, with the books certified
; (make -C engine check) and the benchmarks assembled (sh bench/build.sh):
;   acl2 < inspect.lsp
; Nothing here is part of a proof. Part 3 is a test of two theorems on one
; program: it shows what the statements mean, not that they are true.
(ld "cert.acl2")
(include-book "run")
(in-package "WE")

; ---------------------------------------------------------------------------
; 1. The statements, from the logical world (not from a source file)

:pe engine-run-is-spec-steps
:pe engine-run-is-spec-run
:pe stepn
:pe engine-run
:pe engine-config
:pe engine-result-p
:pe config-shape-p

; ---------------------------------------------------------------------------
; 2. What the books under the theorems assume

(program)
(set-state-ok t)

; "flagged": the books whose certificate records a skipped proof, an axiom
; or a trust tag
(defun flagged-books (alist)
  (cond ((atom alist) nil)
        ((let ((flags (cadddr (car alist))))
           (or (cdr (assoc-eq :skipped-proofsp flags))
               (cdr (assoc-eq :axiomsp flags))
               (cdr (assoc-eq :ttags flags))))
         (cons (car (car alist)) (flagged-books (cdr alist))))
        (t (flagged-books (cdr alist)))))

(let ((alist (acl2::global-val 'acl2::include-book-alist (w state))))
  (cw "INSPECT books ~x0 flagged ~x1~%"
      (len alist) (flagged-books alist)))
(cw "INSPECT skip-proofs-seen ~x0~%"
    (acl2::global-val 'acl2::skip-proofs-seen (w state)))
(acl2::ttags-seen)

; ---------------------------------------------------------------------------
; 3. One instance: the factorial of bench/fac.wat, run(5)

(defun read-bytes-loop (channel acc state)
  (mv-let (b state) (read-byte$ channel state)
    (if (null b) (mv (reverse acc) state) (read-bytes-loop channel (cons b acc) state))))
(defun read-bytes (file state)
  (mv-let (channel state) (open-input-channel file :byte state)
    (if (null channel) (mv nil state)
      (mv-let (bs state) (read-bytes-loop channel nil state)
        (let ((state (close-input-channel channel state))) (mv bs state))))))
(defun str-bytes (s) (if (atom s) nil (cons (char-code (car s)) (str-bytes (cdr s)))))
(defun find-export (field exs)
  (cond ((atom exs) nil)
        ((equal (wrt::%get-field (car exs) :name) field) (wrt::%get-field (car exs) :addr))
        (t (find-export field (cdr exs)))))

(defconst *s0* '(:%rec (:tags) (:globals) (:mems) (:tables) (:funcs) (:datas) (:elems) (:structs) (:arrays) (:exns)))

; Both sides of ENGINE-RUN-IS-SPEC-STEPS for a run of N engine steps from C.
; "same": (stepn spec-steps c) is (list (engine-config (engine-run n c fm))).
; ENGINE-STEPS is not executable; for a run that is not refused it is
; ENGINE-CLOCKS, which is (the list machine counts the spec steps).
(defun check-steps (n c fm)
  (declare (xargs :stobjs fm))
  (let* ((hyps (and (config-shape-p c) (fmp fm)))
         (fm (engine-run n c fm))
         (k (engine-clocks n c))
         (spec (stepn k c))
         (same (equal spec (list (engine-config fm)))))
    (prog2$ (cw "INSPECT steps ~x0 hyps ~x1 status ~x2 spec-steps ~x3 same ~x4~%"
                n hyps (fm-status fm) k same)
            fm)))

(defun check-steps-list (ns c fm)
  (declare (xargs :stobjs fm))
  (if (atom ns) fm
    (let ((fm (check-steps (car ns) c fm)))
      (check-steps-list (cdr ns) c fm))))

; Both sides of ENGINE-RUN-IS-SPEC-RUN (T3) for a run that ends with a result.
; "same": (steps/%fuel fuel c) is (list (engine-config (engine-run n c fm))).
(defun check-result (n c fm)
  (declare (xargs :stobjs fm))
  (let* ((fm (engine-run n c fm))
         (fuel (+ 1 (engine-clocks n c)))
         (spec (w3t::steps/%fuel fuel c))
         (c2 (engine-config fm)))
    (prog2$ (cw "INSPECT result ~x0 fuel ~x1 same ~x2 instrs ~x3~%"
                (engine-result-p fm) fuel (equal spec (list c2)) (caddr c2))
            fm)))

(defun inspect-fac (file arg fm state)
  (declare (xargs :stobjs (fm state)))
  (mv-let (bs state) (read-bytes file state)
    (let* ((p (w3t::gram/bmodule bs))
           (m (and p (null (cadr p)) (car p)))
           (c0 (and m (w3t::$instantiate *s0* m nil))))
      (if (null c0)
          (prog2$ (cw "INSPECT no module at ~x0: run sh bench/build.sh~%" file) (mv fm state))
        (let* ((fm (engine-run 1000000 c0 fm))
               (c1 (engine-config fm))
               (store (cadr (cadr c1)))
               (inst (wrt::%get-field (caddr (cadr c1)) :module))
               (addr (find-export (str-bytes (coerce "run" 'list)) (wrt::%get-field inst :exports)))
               (c (w3t::$invoke store (cadr addr) (list (list :const '(:i64) arg))))
               (fm (check-steps-list '(0 1 2 3 5 8 13 21 34 55 89 144 233 1000) c fm))
               (fm (check-result 1000 c fm)))
          (mv fm state))))))

(inspect-fac "bench/wasm/fac-1.wasm" 5 fm state)
