; E7 differential test 3: the fast machine against the list machine over a
; spec-test-3 script. Every action command (action, assert_return,
; assert_trap, assert_exception) is run from the same $invoke configuration
; on the list machine (MACHINE-RUN) and on the fast machine (FAST-RUN), and
; the final states are compared, store and memory included (FM->MS). The
; script continues from the list machine's state (the list machine agrees
; with the spec on these scripts: E6, differential test 2). A command at
; which the fast machine stops :unsupported at a call_ref of a host function
; (plan2.md V7), after agreeing with the list machine at every step before,
; is counted apart (:host-refused). Run from
; translate/tests/spec by difftest3-all.sh, which prepends
; (assign t7-name "NAME").
(ld "t7-lib-3.0.acl2")
(include-book "../../../engine/fast/fast")
(in-package "W3T")
(include-book "t7-lib-3.0")
(program)
(set-state-ok t)

(defconst *d3-fuel* 2000000)

; on a difference: the first step at which the machines part (small runs)
(defun d3-lock (s k n we::fm)
  (declare (xargs :stobjs we::fm))
  (if (or (zp k) (not (we::machine-running s))) (mv nil we::fm)
    (let* ((i (car (we::ms-is s))) (s2 (we::machine-step s)) (we::fm (we::fast-step we::fm)))
      (if (equal (we::fm->ms we::fm) s2)
          (d3-lock s2 (1- k) (1+ n) we::fm)
        (mv (list :step n :instr i :vals (we::ms-vals s)
                  :list-is (acl2::take 3 (we::ms-is s2)) :fast-is (acl2::take 3 (we::fm-is we::fm))
                  :list-vals (acl2::take 3 (we::ms-vals s2)) :fast-vals (acl2::take 3 (we::fm-vals we::fm))
                  :list-status (we::ms-status s2) :fast-status (we::fm-status we::fm)
                  :host (we::host-ref-p (car (we::ms-vals s)) (we::ms-store s))
                  :same-store (equal (we::ms-store s2) (we::ms-store (we::fm->ms we::fm)))
                  :same-rest (equal (we::put-mem0-bytes (we::ms-store s2) nil) (we::fm-store we::fm))
                  :list-window (acl2::take 8 (nthcdr 28 (we::mem0-of-store (we::ms-store s2))))
                  :fast-window (acl2::take 8 (nthcdr 28 (we::mem-to-list we::fm)))
                  :list-len (acl2::len (we::mem0-of-store (we::ms-store s2)))
                  :fast-len (we::fm-mem-length we::fm)
                  :mems (acl2::len (%get-field (we::ms-store s2) :mems))
                  :mem0-keys (strip-cars (cdr (car (%get-field (we::ms-store s2) :mems))))
                  :same-frame (equal (we::ms-frame s2) (we::fm-frame we::fm)))
            we::fm)))))

; (mv class result env we::fm): the command on both machines
(defun do-action-2 (a e we::fm)
  (declare (xargs :stobjs we::fm))
  (let* ((inst (env-inst e (cadr a)))
         (addr (and inst (find-export (caddr a) (%get-field inst :exports)))))
    (cond ((or (null addr) (eq (car a) :get) (not (eq (car addr) :func))) (mv :not-invoke nil e we::fm))
          (t (let ((c ($invoke (env-store e) (cadr addr) (to-vals (cadddr a)))))
               (if (null c) (mv :error nil e we::fm)
                 (let* ((s0 (we::ms-of-config c))
                        (s (we::machine-run *d3-fuel* s0))
                        (we::fm (we::fm-load-ms s0 we::fm))
                        (we::fm (we::fast-run *d3-fuel* we::fm))
                        (same (equal (we::fm->ms we::fm) s))
                        (st (we::ms-status s)))
                  (mv-let (where we::fm)
                    (if same (mv nil we::fm)
                      (let ((we::fm (we::fm-load-ms s0 we::fm))) (d3-lock s0 100000 0 we::fm)))
                   (mv (cond ((and (not same) (consp where)
                                   ; plan2.md V7: the fast machine stops
                                   ; :unsupported at a call_ref of a host
                                   ; function. Up to that step the two agreed.
                                   (eq (cadr (member-eq :fast-status where)) :unsupported)
                                   (consp (cadr (member-eq :instr where)))
                                   (eq (car (cadr (member-eq :instr where))) :call_ref)
                                   (cadr (member-eq :host where)))
                              :host-refused)
                             ((not same) :differ)
                             ((member-eq st '(:done :trap :throw)) :same)
                             (t st))
                       (list st (caddr (we::machine-abs s)) where)
                       (if (member-eq st '(:done :trap :throw))
                           (cons (cadr (cadr (we::machine-abs s))) (cdr e))
                         e)
                       we::fm)))))))))

(defun d3-cmd (c we::fm state)
  (declare (xargs :stobjs (we::fm state)))
  (let ((k (car c)) (e (@ t7-env)))
    (if (member-eq k '(:action :assert_return :assert_trap :assert_exception))
        (mv-let (class r e2 we::fm) (do-action-2 (cadr c) e we::fm)
          (let ((state (f-put-global 't7-env e2 state)))
            (prog2$ (cw "D3-CMD ~x0 ~x1~%" k class)
                    (prog2$ (and (eq class :differ) (cw "D3-DIFF ~x0 list ~x1~%" (cadr c) r))
                            (mv nil :ok we::fm state)))))
      (mv-let (kind ok detail e state) (run-cmd c e state)
        (declare (ignore kind ok detail))
        (let ((state (f-put-global 't7-env e state)))
          (mv nil :ok we::fm state))))))

(defun d3-forms (cmds)
  (if (atom cmds) nil (cons (list 'd3-cmd (list 'quote (car cmds)) 'we::fm 'state) (d3-forms (cdr cmds)))))

(defun d3-setup (name state)
  (mv-let (ok-ignored ok state) (t7-setup name state)
    (declare (ignore ok-ignored))
    (mv-let (cmds state) (read-obj (concatenate 'string *data* name ".lsp") state)
      (let ((state (f-put-global 't7-forms (and ok (d3-forms cmds)) state)))
        (mv nil t state)))))
(d3-setup (@ acl2::t7-name) state)
(ld (@ t7-forms) :ld-error-action :continue)
(cw "D3-DONE ~s0~%" (@ acl2::t7-name))
(acl2::good-bye 0)
