; E12 (L0): render the slides of a sent-format deck on the engine.
; (assign engine :list) runs the list machine of E6; otherwise the fast
; machine of E7 (engine/fast/fast.lisp) runs, and its final state is read
; back through FM->MS.
; The module (build.sh) goes through the generated decoder (GRAM/BMODULE)
; and the spec's $instantiate; the instantiation configuration and every
; call of render(n) are run by the list machine of E6 (MACHINE-RUN), not by
; the spec's STEP. Each slide's framebuffer is read from the machine's final
; store and written as OUTDIR/slide-N.pbm (P4: its pixel data is exactly the
; framebuffer bytes, 1 = black). From engine/slides, inside nix develop:
;   (echo '(assign wasm-file "build/sent.wasm")' '(assign out-dir "build/engine")'; \
;    cat render.lsp) | acl2
; On the list machine every run is checked against the hypotheses of T1
; (MACHINE-RESULT-IS-SPEC-RESULT, machine/spec-result.lisp; plan2.md V5): the
; loaded state has MACHINE-OK, its MACHINE-ABS is the configuration the
; spec's $instantiate or $invoke returned, and the run ends with a result.
; One line ENGINE-T1 per run says so; when all hold, the theorem says that
; the spec's STEPS/%FUEL returns, from that configuration, the final state
; the pixels are read from. The fast machine has no such theorem yet (T2).
(ld "../fast/cert.acl2")
(include-book "../fast/fast")
(include-book "../machine/ok")
(in-package "WE")
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
(defun write-bytes-loop (bs channel state)
  (if (atom bs) state
    (let ((state (write-byte$ (car bs) channel state))) (write-bytes-loop (cdr bs) channel state))))
(defun write-bytes (file bs state)
  (mv-let (channel state) (open-output-channel file :byte state)
    (let* ((state (write-bytes-loop bs channel state)))
      (close-output-channel channel state))))
(defun str-bytes (s) (if (atom s) nil (cons (char-code (car s)) (str-bytes (cdr s)))))

(defconst *s0* '(:%rec (:tags) (:globals) (:mems) (:tables) (:funcs) (:datas) (:elems) (:structs) (:arrays) (:exns)))
(defconst *fuel* 100000000)

(defun find-export (field exs)
  (cond ((atom exs) nil)
        ((equal (wrt::%get-field (car exs) :name) field) (wrt::%get-field (car exs) :addr))
        (t (find-export field (cdr exs)))))

; run configuration C on the chosen machine: (mv status final-list-state fm)
(defun mrun (c fm state)
  (declare (xargs :stobjs (fm state)))
  (if (eq (and (boundp-global 'acl2::engine state) (@ acl2::engine)) :list)
      (let* ((s0 (ms-of-config c))
             (hyp (and (machine-ok s0) (equal (machine-abs s0) c)))
             (s (machine-run *fuel* s0)))
        (prog2$ (cw "ENGINE-T1 machine-ok and abs ~x0 result ~x1~%" hyp (machine-result-p s))
                (mv (ms-status s) s fm)))
    (let* ((fm (fm-load-ms (ms-of-config c) fm))
           (fm (fast-run *fuel* fm)))
      (mv (fm-status fm) (fm->ms fm) fm))))

; call export FIELD of instance INST in STORE with ARGS on the machine:
; (mv status result-instrs final-state)
(defun call-export (store inst field args fm state)
  (declare (xargs :stobjs (fm state)))
  (let* ((addr (find-export (str-bytes (coerce field 'list)) (wrt::%get-field inst :exports)))
         (c (and addr (w3t::$invoke store (cadr addr) args))))
    (if (null c) (mv :no-call nil nil fm)
      (mv-let (st s fm) (mrun c fm state)
        (mv st (caddr (machine-abs s)) s fm)))))

(defun i32 (n) (list :const '(:i32) n))
(defun result-int (instrs) (caddr (car instrs)))

(defun mem0-bytes (store) (wrt::%get-field (car (wrt::%get-field store :mems)) :bytes))

(defun render-slides (i n store inst fb w h dir fm state)
  (declare (xargs :stobjs (fm state)))
  (if (>= i n) (mv fm state)
    (mv-let (t0 state) (read-run-time state)
      (mv-let (st res s fm) (call-export store inst "render" (list (i32 i)) fm state)
        (mv-let (t1 state) (read-run-time state)
          (let* ((store2 (ms-store s))
                 (bytes (take (* (/ w 8) h) (nthcdr fb (mem0-bytes store2))))
                 (header (str-bytes (coerce (concatenate 'string "P4" (string #\Newline)
                                                          (coerce (explode-atom w 10) 'string) " "
                                                          (coerce (explode-atom h 10) 'string)
                                                          (string #\Newline))
                                            'list)))
                 (file (concatenate 'string dir "/slide-" (coerce (explode-atom i 10) 'string) ".pbm"))
                 (state (write-bytes file (append header bytes) state)))
            (prog2$ (cw "ENGINE-SLIDE ~x0 status ~x1 scale ~x2 ms ~x3~%" i st (result-int res)
                        (round (* 1000 (- t1 t0)) 1))
                    (render-slides (1+ i) n store2 inst fb w h dir fm state))))))))

(defun render-deck (file dir fm state)
  (declare (xargs :stobjs (fm state)))
  (mv-let (bs state) (read-bytes file state)
    (let* ((p (w3t::gram/bmodule bs))
           (m (and p (null (cadr p)) (car p)))
           (c0 (and m (w3t::$instantiate *s0* m nil))))
      (if (null c0) (prog2$ (cw "ENGINE-ERROR decode or instantiate failed~%") (mv fm state))
        (mv-let (st s fm) (mrun c0 fm state)
          (let* ((store (ms-store s))
                 (inst (wrt::%get-field (ms-frame s) :module)))
            (mv-let (st1 r1 s1 fm) (call-export store inst "slide_count" nil fm state)
              (declare (ignore s1))
              (mv-let (st2 r2 s2 fm) (call-export store inst "framebuffer" nil fm state)
                (declare (ignore s2))
                (mv-let (st3 r3 s3 fm) (call-export store inst "width" nil fm state)
                  (declare (ignore s3))
                  (mv-let (st4 r4 s4 fm) (call-export store inst "height" nil fm state)
                    (declare (ignore s4))
                    (prog2$ (cw "ENGINE-DECK machine ~x6 instantiate ~x0 slides ~x1 framebuffer ~x2 size ~x3 x ~x4 (~x5)~%"
                                st (result-int r1) (result-int r2) (result-int r3) (result-int r4)
                                (list st1 st2 st3 st4)
                                (if (eq (and (boundp-global 'acl2::engine state) (@ acl2::engine)) :list) :list :fast))
                            (render-slides 0 (result-int r1) store inst (result-int r2)
                                           (result-int r3) (result-int r4) dir fm state))))))))))))

(render-deck (@ acl2::wasm-file) (@ acl2::out-dir) fm state)
