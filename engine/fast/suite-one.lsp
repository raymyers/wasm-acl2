; The spec-test-3 suite on the engine: every action command (action,
; assert_return, assert_trap, assert_exception) runs on the fast machine
; (FAST-RUN) from the spec's $invoke configuration, and its result is judged
; as the conformance driver judges the spec's (t7-lib-3.0). Where the engine
; refuses (:unsupported: an instruction outside its subset; :stuck), the
; command runs on the generated semantics instead (DO-ACTION-TIMED). Each
; result line says who decided: ENGINE or SPEC. Everything else (decoding,
; validation, instantiation) is the generated semantics, as in t7-lib-3.0.
; Run from translate/tests/spec by suite-all.sh, which prepends
; (assign t7-name "NAME").
(ld "t7-lib-3.0.acl2")
(include-book "../../../engine/fast/fast")
(in-package "W3T")
(include-book "t7-lib-3.0")
(program)
(set-state-ok t)

(defconst *es-chunk* 100000)          ; steps between two looks at the clock
(defconst *es-fuel* 2000000000)
(defconst *es-seconds* 900)

(defun es-run (fuel deadline we::fm state)
  (declare (xargs :stobjs (we::fm state)))
  (if (or (zp fuel) (not (eq (we::fm-status we::fm) :run))) (mv we::fm state)
    (let ((we::fm (we::fast-run (min fuel *es-chunk*) we::fm)))
      (mv-let (now state) (read-run-time state)
        (if (> now deadline) (mv we::fm state)
          (es-run (- fuel *es-chunk*) deadline we::fm state))))))

; (mv who result env fm state): WHO is :engine or :spec; RESULT as DO-ACTION's
(defun es-action (a e we::fm state)
  (declare (xargs :stobjs (we::fm state)))
  (let* ((inst (env-inst e (cadr a)))
         (addr (and inst (find-export (caddr a) (%get-field inst :exports)))))
    (if (or (null addr) (eq (car a) :get) (not (eq (car addr) :func)))
        (mv-let (r e state) (do-action-timed a e state) (mv :spec r e we::fm state))
      (let ((c ($invoke (env-store e) (cadr addr) (to-vals (cadddr a)))))
        (if (null c) (mv :spec :error e we::fm state)
          (mv-let (now state) (read-run-time state)
            (let ((we::fm (we::fm-load-ms (we::ms-of-config c) we::fm)))
              (mv-let (we::fm state) (es-run *es-fuel* (+ now *es-seconds*) we::fm state)
                (let ((st (we::fm-status we::fm)))
                  (cond ((eq st :run) (mv :engine :time e we::fm state))
                        ((member-eq st '(:done :trap :throw))
                         (let* ((abs (we::machine-abs (we::fm->ms we::fm)))
                                (s (cadr (cadr abs))) (instrs (caddr abs)))
                           (cond ((equal instrs '((:trap))) (mv :engine :trap (cons s (cdr e)) we::fm state))
                                 ((exn-result-p instrs) (mv :engine :exception (cons s (cdr e)) we::fm state))
                                 (t (mv :engine instrs (cons s (cdr e)) we::fm state)))))
                        (t (mv-let (r e state) (do-action-timed a e state)
                             (mv :spec r e we::fm state)))))))))))))

(defun es-cmd (c we::fm state)
  (declare (xargs :stobjs (we::fm state)))
  (let ((k (car c)) (e (@ t7-env)))
    (prog2$ (cw "T7-TRY ~x0~%" k)
      (if (member-eq k '(:action :assert_return :assert_trap :assert_exception))
          (mv-let (who r e2 we::fm state) (es-action (cadr c) e we::fm state)
            (let ((state (f-put-global 't7-env e2 state)))
             (let ((ok (case k
                        (:action (not (member-eq r '(:error :fuel :time))))
                        (:assert_return (and (true-listp r) (vals-ok (caddr c) r)))
                        (:assert_trap (eq r :trap))
                        (t (eq r :exception)))))
              (prog2$ (cw "T7-CMD ~x0 ~x1~%ES-WHO ~x0 ~x2 ~x1~%" k (and ok t) who)
                (prog2$ (and (not ok) (prog2$ (cw "T7-FAILKIND ~x0 ~x1~%" k (fail-class r))
                                              (cw "T7-FAIL ~x0 ~x1~%" c r)))
                        (mv nil :ok we::fm state))))))
        (mv-let (kind ok detail e state) (run-cmd-timed c e state)
          (let ((state (f-put-global 't7-env e state)))
            (prog2$ (and kind (cw "T7-CMD ~x0 ~x1~%" kind (and ok t)))
              (prog2$ (and kind (not ok) (not (member-eq kind '(:assert_exhaustion-skipped :assert_invalid-skipped :assert_malformed-text-skipped)))
                           (prog2$ (cw "T7-FAILKIND ~x0 ~x1~%" kind (fail-class detail))
                                   (cw "T7-FAIL ~x0 ~x1~%" c detail)))
                      (mv nil :ok we::fm state)))))))))

(defun es-forms (cmds)
  (if (atom cmds) nil (cons (list 'es-cmd (list 'quote (car cmds)) 'we::fm 'state) (es-forms (cdr cmds)))))

(defun es-setup (name state)
  (mv-let (ok-ignored ok state) (t7-setup name state)
    (declare (ignore ok-ignored))
    (mv-let (cmds state) (read-obj (concatenate 'string *data* name ".lsp") state)
      (let ((state (f-put-global 't7-forms (and ok (es-forms cmds)) state)))
        (mv nil t state)))))
(es-setup (@ acl2::t7-name) state)
(ld (@ t7-forms) :ld-error-action :continue)
(cw "T7-DONE ~s0~%" (@ acl2::t7-name))
(acl2::good-bye 0)
