; E6 differential test 2 (plan/wasm-engine): one spec-test-3 script, every
; action command (action, assert_return, assert_trap, assert_exception) run
; twice from the same script state: on the generated semantics (the T7
; driver's DO-ACTION, translate/tests/spec/t7-lib-3.0.lisp) and on the list
; machine (the same $invoke configuration, run by MACHINE-STEP). The result
; and the store after the command are compared. The script then continues
; from the spec's state. Modules are instantiated by the spec ($instantiate),
; as in T7. Run from translate/tests/spec (the T7 data paths are relative to
; it) by difftest2-all.sh, which prepends (assign t7-name "NAME").
(ld "t7-lib-3.0.acl2")
(include-book "../../../engine/machine/machine")
(in-package "W3T")
(include-book "t7-lib-3.0")
(program)
(set-state-ok t)

; D5 group of an instruction the machine executes as an op step (E1 census):
; 0 = S0 integer core, 1 = S1 floats and call_indirect, 2 = S2 bulk memory
; and sign extension, 3 = S3 exceptions, 4 = outside D5
(defun float-type-p (x) (member-equal x '((:f32) (:f64))))
(defun instr-group (i)
  (let ((k (car i)))
    (cond ((member-eq k '(:try_table :throw :throw_ref)) 3)
          ((member-eq k '(:memory.fill :memory.copy)) 2)
          ((and (eq k :unop) (consp (caddr i)) (eq (car (caddr i)) :extend)) 2)
          ((member-eq k '(:call_indirect :table.get :ref.cast)) 1)
          ((member-eq k '(:unop :binop :testop :relop :load :store))
           (if (float-type-p (cadr i)) 1 0))
          ((eq k :cvtop) (if (or (float-type-p (cadr i)) (float-type-p (caddr i))) 1 0))
          ((member-eq k '(:unreachable :nop :drop :select :ifelse :block :loop :br_if :br_table
                          :call :call_ref :local.get :local.set :local.tee :global.get :global.set
                          :memory.size :memory.grow)) 0)
          (t 4))))

; the machine's run with fuel K; G is the highest group met so far
(defun m-run-g (k s g)
  (if (or (zp k) (not (we::machine-running s))) (mv s g)
    (let* ((is (we::ms-is s)) (i (and (consp is) (car is)))
           (g (if (and (consp i) (not (we::value-instr-p i)) (not (we::admin-kind i))
                       (not (member-eq (car i) '(:br :return :trap))))
                  (max g (instr-group i)) g)))
      (m-run-g (1- k) (we::machine-step s) g))))

; the machine's run of a configuration, in the shape of FINAL-CONFIG, and
; the group: (mv store instrs frame group)
(defun m-final-config (c)
  (if (null c) (mv nil :fuel nil 0)
    (mv-let (s g) (m-run-g 2000000 (we::ms-of-config c) 0)
      (let ((st (we::ms-status s)))
        (cond ((member-eq st '(:done :trap :throw))
               (let* ((cf (we::machine-abs s)) (z (cadr cf)))
                 (mv (cadr z) (caddr cf) (caddr z) g)))
              ((eq st :run) (mv nil :fuel nil g))
              (t (prog2$ (cw "D2-STOP ~x0 at ~x1 depth ~x2 vals ~x3~%" st
                             (let ((i (car (we::ms-is s)))) (if (consp i) (list (car i) (cadr i)) i))
                             (acl2::len (we::ms-ctrl s))
                             (acl2::len (we::ms-vals s)))
                         (mv nil st nil g))))))))           ; :stuck or :unsupported

(defun do-action-m (a e)                       ; DO-ACTION with the machine: (mv r e group)
  (let* ((inst (env-inst e (cadr a)))
         (addr (and inst (find-export (caddr a) (%get-field inst :exports)))))
    (cond ((or (null addr) (eq (car a) :get) (not (eq (car addr) :func))) (mv :not-invoke e 0))
          (t (let ((c ($invoke (env-store e) (cadr addr) (to-vals (cadddr a)))))
               (if (null c) (mv :error e 0)
                 (mv-let (s instrs f g) (m-final-config c)
                   (declare (ignore f))
                   (cond ((member-eq instrs '(:fuel :stuck :unsupported)) (mv instrs e g))
                         ((equal instrs '((:trap))) (mv :trap (cons s (cdr e)) g))
                         ((exn-result-p instrs) (mv :exception (cons s (cdr e)) g))
                         (t (mv instrs (cons s (cdr e)) g))))))))))

(defun d2-cmd (c state)
  (let ((k (car c)) (e (@ t7-env)))
    (if (and (member-eq k '(:action :assert_return :assert_trap :assert_exception))
             (boundp-global 'acl2::d2-only state)
             (not (member-equal (caddr (cadr c)) (@ acl2::d2-only))))
        ; reproduction mode (D2-ONLY set): a command for another export runs
        ; on the machine alone, and the script continues from its state
        (mv-let (rm em g) (do-action-m (cadr c) e)
          (declare (ignore rm g))
          (let ((state (f-put-global 't7-env em state))) (mv nil :ok state)))
    (if (member-eq k '(:action :assert_return :assert_trap :assert_exception))
        (mv-let (r e2) (do-action (cadr c) e)
          (mv-let (rm em g) (do-action-m (cadr c) e)
            (let* ((class (cond ((eq rm :not-invoke) :not-invoke)
                                ((eq r :fuel) :spec-fuel)
                                ((eq rm :unsupported) :unsupported)
                                ((and (equal r rm) (equal (env-store e2) (env-store em))) :same)
                                (t :differ)))
                   (state (f-put-global 't7-env e2 state)))
              (prog2$ (cw "D2-CMD ~x0 ~x1 S~x2~%" k class g)
                      (prog2$ (and (eq class :differ)
                                   (cw "D2-DIFF ~x0 spec ~x1 machine ~x2 same-store ~x3~%"
                                       (cadr c) r rm (equal (env-store e2) (env-store em))))
                              (mv nil :ok state))))))
      (mv-let (kind ok detail e state) (run-cmd c e state)
        (declare (ignore kind ok detail))
        (let ((state (f-put-global 't7-env e state)))
          (mv nil :ok state)))))))

(defun d2-forms (cmds)
  (if (atom cmds) nil (cons (list 'd2-cmd (list 'quote (car cmds)) 'state) (d2-forms (cdr cmds)))))

(defun d2-setup (name state)
  (mv-let (ok-ignored ok state) (t7-setup name state)
    (declare (ignore ok-ignored))
    (mv-let (cmds state) (read-obj (concatenate 'string *data* name ".lsp") state)
      (let ((state (f-put-global 't7-forms (and ok (d2-forms cmds)) state)))
        (mv nil t state)))))
(d2-setup (@ acl2::t7-name) state)
(ld (@ t7-forms) :ld-error-action :continue)
(cw "D2-DONE ~s0~%" (@ acl2::t7-name))
(acl2::good-bye 0)
