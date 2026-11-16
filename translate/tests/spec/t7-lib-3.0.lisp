; T7 conformance driver for WASM 3.0 (wasm3 M4), from the 1.0 driver
; (t7-lib.lisp): run spec-test-3 (converted by `make spec-data SPEC=3.0`,
; ../oracle/gen-spec-tests.mjs) on the GENERATED 3.0 semantics only:
; .wasm bytes -> GRAM/BMODULE -> $instantiate_unchecked (imports resolved
; through `register`ed instances and the spectest module) -> $invoke + STEP.
; Differences from 1.0:
; - Instantiation uses $instantiate, which validates the module (Module_ok,
;   proposer and checker since wasm3 M7) and matches the import types
;   (Externaddr_ok); assert_invalid is checked with MODULE_OK. (Until M7 the
;   test-only $instantiate_unchecked was used.)
; - 3.0 values: v128 by lanes, references (null, i31, struct, array, func,
;   exn, host, extern), `either` results, uncaught exceptions.
; - Each command runs as its own top-level form (run-one-3.0.lsp, ld with
;   :ld-error-action :continue) with the script state in the state global
;   T7-ENV, after a T7-TRY line. A command that exhausts a Lisp resource
;   (a huge memory.grow, a segment that does not fit: the five spec-test-1
;   crashes of wasm3 prep P6) aborts alone, and summarize.sh counts it as
;   failed, kind CRASH. The state stays as before the command.
(in-package "W3T")
(include-book "../../gen/wasm-3.0/wasm3")

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

(defun read-obj (file state)
  (mv-let (channel state) (open-input-channel file :object state)
    (if (null channel) (mv nil state)
      (mv-let (eofp obj state) (read-object channel state)
        (declare (ignore eofp))
        (let ((state (close-input-channel channel state))) (mv obj state))))))

(defconst *data* "data-3.0/")

; a complete parse of DATA/FILE, or nil
(defun parse-file (file state)
  (mv-let (bs state) (read-bytes (concatenate 'string *data* file) state)
    (let ((p (and bs (gram/bmodule bs))))
      (mv (and p (null (cadr p)) (car p)) state))))

; --- values ------------------------------------------------------------

(defun vt-bits (vt) (if (member-eq vt '(:i64 :f64)) 64 32))
(defun lane-bits (lt) (case lt (:i8 8) (:i16 16) ((:i64 :f64) 64) (t 32)))
(defun lanes-nat (ls w)                         ; lane 0 in the low bits
  (if (atom ls) 0 (+ (mod (ifix (car ls)) (expt 2 w)) (* (expt 2 w) (lanes-nat (cdr ls) w)))))
(defun nat-lanes (x w k)
  (if (zp k) nil (cons (mod x (expt 2 w)) (nat-lanes (floor x (expt 2 w)) w (1- k)))))

(defun to-val (v)
  ;; a driver value -> a 3.0 value
  (let ((k (car v)))
    (case k
      ((:i32 :i64) (list :const (list k) (cadr v)))
      ((:f32 :f64) (list :const (list k) (%bitsf (vt-bits k) (cadr v))))
      (:v128 (list :vconst '(:v128) (lanes-nat (caddr v) (lane-bits (cadr v)))))
      (:externref (if (eq (cadr v) :null) '(:ref.null_addr)
                    (list :ref.extern (list :ref.host_addr (cadr v)))))
      (:hostref (list :ref.host_addr (cadr v)))
      (t '(:ref.null_addr)))))                 ; every other null reference
(defun to-vals (vs) (if (atom vs) nil (cons (to-val (car vs)) (to-vals (cdr vs)))))

(defun float-bits-ok (n want bits)
  (let ((sign (expt 2 (1- n))) (quiet (if (= n 32) #x7fc00000 #x7ff8000000000000)))
    (case want
      (:nan-canonical (= (logand bits (1- sign)) quiet))
      (:nan-arithmetic (= (logand bits quiet) quiet))
      (t (equal bits want)))))

(defun lanes-ok (want got lt)
  (if (atom want) (atom got)
    (and (consp got)
         (if (member-eq lt '(:f32 :f64))
             (float-bits-ok (lane-bits lt) (car want) (car got))
           (equal (mod (ifix (car want)) (expt 2 (lane-bits lt))) (car got)))
         (lanes-ok (cdr want) (cdr got) lt))))

(defun ref-kind (got) (and (consp got) (car got)))

(defun ref-ok (k x got)
  ;; expected reference (K X), e.g. (:FUNCREF :ANY), (:EXTERNREF 3), (:ANYREF :NULL)
  (cond ((eq x :null) (equal got '(:ref.null_addr)))
        ((eq k :externref)
         (and (eq (ref-kind got) :ref.extern)
              (or (eq x :any) (equal (cadr got) (list :ref.host_addr x)))))
        ((eq k :hostref) (equal got (list :ref.host_addr x)))
        ((eq k :funcref) (eq (ref-kind got) :ref.func_addr))     ; (:FUNCREF 0) from wabt: any function
        ((eq k :i31ref) (eq (ref-kind got) :ref.i31_num))
        ((eq k :structref) (eq (ref-kind got) :ref.struct_addr))
        ((eq k :arrayref) (eq (ref-kind got) :ref.array_addr))
        ((eq k :exnref) (eq (ref-kind got) :ref.exn_addr))
        ((eq k :eqref) (member-eq (ref-kind got) '(:ref.i31_num :ref.struct_addr :ref.array_addr)))
        ((eq k :anyref) (member-eq (ref-kind got) '(:ref.i31_num :ref.struct_addr :ref.array_addr :ref.host_addr)))
        (t nil)))

(mutual-recursion
(defun val-ok (want got)
  (let ((k (car want)))
    (case k
      ((:i32 :i64 :f32 :f64)
       (and (consp got) (eq (car got) :const) (equal (cadr got) (list k))
            (or (eq (cadr want) :any)
                (if (member-eq k '(:f32 :f64))
                    (float-bits-ok (vt-bits k) (cadr want) (%fbits (vt-bits k) (caddr got)))
                  (equal (caddr got) (cadr want))))))
      (:v128
       (and (consp got) (eq (car got) :vconst)
            (or (eq (cadr want) :any)
                (let ((lt (cadr want)))
                  (lanes-ok (caddr want) (nat-lanes (caddr got) (lane-bits lt) (floor 128 (lane-bits lt))) lt)))))
      (:either (either-ok (cadr want) got))
      (t (ref-ok k (cadr want) got)))))
(defun either-ok (alts got)
  (and (consp alts) (or (val-ok (car alts) got) (either-ok (cdr alts) got)))))

(defun vals-ok (want got)
  (if (atom want) (atom got)
    (and (consp got) (val-ok (car want) (car got)) (vals-ok (cdr want) (cdr got)))))

; --- the script state: store, instances --------------------------------
; env: (store current-inst named-alist registered-alist); instances are moduleinsts

(defun env-store (e) (first e))
(defun env-inst (e name) (if name (cdr (assoc-equal name (third e))) (second e)))
(defun chars-of (s) (if (atom s) nil (cons (char-code (car s)) (chars-of (cdr s)))))
(defun str-bytes (s) (chars-of (coerce s 'list)))

(defun find-export (field exs)
  (cond ((atom exs) nil)
        ((equal (%get-field (car exs) :name) field) (%get-field (car exs) :addr))
        (t (find-export field (cdr exs)))))

(defun registered (modname e)
  (cond ((equal modname (str-bytes "spectest")) (cdr (assoc-equal "spectest" (fourth e))))
        (t (let ((hit (assoc-equal modname (fourth e)))) (and hit (cdr hit))))))

(defun resolve-imports (ims e)
  ;; (mv ok addrs): by module and field name only (no type check, see above)
  (if (atom ims) (mv t nil)
    (let* ((im (car ims)) (inst (registered (cadr im) e))
           (addr (and inst (find-export (caddr im) (%get-field inst :exports)))))
      (if (null addr) (mv nil nil)
        (mv-let (ok rest) (resolve-imports (cdr ims) e)
          (mv ok (cons addr rest)))))))

; Step budget per action or instantiation (a step costs about 0.01-0.03 ms
; since wasm3 M3, and up to 1 ms when it stores into a page of memory); an
; action that needs more is :FUEL. 200,000 until 2026-11-16: too few for the
; `test` action of memory_copy (747,881 steps) and the return_call loops
; of 1,000,000 iterations.
(defconst *spec-fuel* 20000000)
(defun run-steps (c n)
  (if (zp n) nil
    (let ((r (step c))) (if r (run-steps (car r) (1- n)) (list c)))))

(defun final-config (c)
  ;; run a config to its normal form: (mv store instrs frame) or (mv nil :fuel nil)
  (let ((r (and c (run-steps c *spec-fuel*))))
    (if (null r) (mv nil :fuel nil)
      (let* ((cf (car r)) (z (cadr cf)))
        (mv (cadr z) (caddr cf) (caddr z))))))

; An action also has a time budget (CPU seconds, read between chunks of
; steps): one that runs out is :TIME, a failure of that command only. Before,
; a slow command ended the whole session at the script's time limit, and
; the commands after it were never tried (call and call_indirect: the
; recursion of depth 100,000 and up, where a step costs the square of the
; depth).
(defconst *spec-seconds* 900)
(defconst *spec-chunk* 200)
(defun run-chunk (c n)
  ;; (mv c done): at most n steps; done when c does not step
  (declare (xargs :mode :program))
  (if (zp n) (mv c nil)
    (let ((r (step c))) (if r (run-chunk (car r) (1- n)) (mv c t)))))
(defun run-timed (c fuel deadline state)
  ;; (mv status c state): :done with the normal form, :fuel or :time
  (declare (xargs :mode :program :stobjs state))
  (if (zp fuel) (mv :fuel nil state)
    (mv-let (c done) (run-chunk c (min fuel *spec-chunk*))
      (if done (mv :done c state)
        (mv-let (now state) (read-run-time state)
          (if (> now deadline) (mv :time nil state)
            (run-timed c (- fuel *spec-chunk*) deadline state)))))))
(defun final-config-timed (c state)
  ;; as final-config: (mv store instrs frame state), instrs :fuel or :time
  (declare (xargs :mode :program :stobjs state))
  (if (null c) (mv nil :fuel nil state)
    (mv-let (now state) (read-run-time state)
      (mv-let (st cf state) (run-timed c *spec-fuel* (+ now *spec-seconds*) state)
        (if (not (eq st :done)) (mv nil st nil state)
          (let ((z (cadr cf))) (mv (cadr z) (caddr cf) (caddr z) state)))))))

(defun exn-result-p (instrs)                   ; (REF.EXN_ADDR a) THROW_REF: an uncaught exception
  (and (consp instrs) (consp (car instrs)) (eq (caar instrs) :ref.exn_addr)
       (equal (cdr instrs) '((:throw_ref)))))

(defun instantiate (m e)
  ;; (mv status store inst): status :ok, :unlinkable, :invalid, :trap, :exception, :fuel
  (mv-let (ok addrs) (resolve-imports (nth 2 m) e)
    (if (not ok) (mv :unlinkable nil nil)
      (let ((c ($instantiate (env-store e) m addrs)))
        (if (null c) (mv :invalid nil nil)
          (mv-let (s instrs f) (final-config c)
            (cond ((eq instrs :fuel) (mv :fuel nil nil))
                  ((equal instrs '((:trap))) (mv :trap s nil))
                  ((exn-result-p instrs) (mv :exception s nil))
                  (t (mv :ok s (%get-field f :module))))))))))

(defun do-action (a e)
  ;; (mv result e): list of result vals, :trap, :exception, :fuel or :error
  ;; (no time budget: the demo's extractor and the engine's differential
  ;; tests use this one; the suite runner uses DO-ACTION-TIMED)
  (let* ((inst (env-inst e (cadr a)))
         (addr (and inst (find-export (caddr a) (%get-field inst :exports)))))
    (cond ((null addr) (mv :error e))
          ((eq (car a) :get)
           (if (eq (car addr) :global)
               (mv (list (%get-field (nth (cadr addr) (%get-field (env-store e) :globals)) :value)) e)
             (mv :error e)))
          ((not (eq (car addr) :func)) (mv :error e))
          (t (let ((c ($invoke (env-store e) (cadr addr) (to-vals (cadddr a)))))
               (if (null c) (mv :error e)            ; $invoke rejects the arguments
                 (mv-let (s instrs f) (final-config c)
                   (declare (ignore f))
                   (cond ((eq instrs :fuel) (mv :fuel e))
                         ((equal instrs '((:trap))) (mv :trap (cons s (cdr e))))
                         ((exn-result-p instrs) (mv :exception (cons s (cdr e))))
                         (t (mv instrs (cons s (cdr e))))))))))))

(defun do-action-timed (a e state)
  ;; DO-ACTION with the time budget; (mv result e state): list of result vals, :trap, :exception, :fuel, :time or :error
  (declare (xargs :mode :program :stobjs state))
  (let* ((inst (env-inst e (cadr a)))
         (addr (and inst (find-export (caddr a) (%get-field inst :exports)))))
    (cond ((null addr) (mv :error e state))
          ((eq (car a) :get)
           (if (eq (car addr) :global)
               (mv (list (%get-field (nth (cadr addr) (%get-field (env-store e) :globals)) :value)) e state)
             (mv :error e state)))
          ((not (eq (car addr) :func)) (mv :error e state))
          (t (let ((c ($invoke (env-store e) (cadr addr) (to-vals (cadddr a)))))
               (if (null c) (mv :error e state)      ; $invoke rejects the arguments
                 (mv-let (s instrs f state) (final-config-timed c state)
                   (declare (ignore f))
                   (cond ((member-eq instrs '(:fuel :time)) (mv instrs e state))
                         ((equal instrs '((:trap))) (mv :trap (cons s (cdr e)) state))
                         ((exn-result-p instrs) (mv :exception (cons s (cdr e)) state))
                         (t (mv instrs (cons s (cdr e)) state))))))))))

; --- one command ---------------------------------------------------------
; (mv kind ok detail e): KIND for the tally, DETAIL for failures

(defun run-cmd (c e state)
  (let ((k (car c)))
    (case k
      (:module
       (mv-let (m state) (parse-file (cadr c) state)
         (mv-let (st s inst) (if m (instantiate m e) (mv :malformed nil nil))
           (let* ((ok (eq st :ok))
                  (e (if ok (list s inst (if (caddr c) (acons (caddr c) inst (third e)) (third e)) (fourth e))
                       (list (first e) nil (third e) (fourth e)))))
             (mv k ok st e state)))))
      (:register
       (let ((inst (env-inst e (caddr c))))
         (mv nil t nil (list (first e) (second e) (third e) (acons (cadr c) inst (fourth e))) state)))
      ((:action :assert_return :assert_trap :assert_exception)
       (mv-let (r e) (do-action (cadr c) e)
         (let ((ok (case k
                     (:action (not (member-eq r '(:error :fuel))))
                     (:assert_return (and (true-listp r) (vals-ok (caddr c) r)))
                     (:assert_trap (eq r :trap))
                     (t (eq r :exception)))))
           (mv k ok r e state))))
      (:assert_exhaustion (mv :assert_exhaustion-skipped nil nil e state))   ; no call-stack limit in the spec
      (:assert_invalid
       (mv-let (m state) (parse-file (cadr c) state)
         (let ((r (if m (if (module_ok m) :accepted :rejected) :not-parsed)))
           (mv k (eq r :rejected) r e state))))
      (:assert_malformed
       (if (eq (cadddr c) :text)
           (mv :assert_malformed-text-skipped nil nil e state)
         (mv-let (m state) (parse-file (cadr c) state)
           (mv k (null m) (and m :parsed) e state))))
      ((:assert_unlinkable :assert_uninstantiable)
       (mv-let (m state) (parse-file (cadr c) state)
         (mv-let (st s inst) (if m (instantiate m e) (mv :malformed nil nil))
           (declare (ignore inst))
           (let* ((ok (if (eq k :assert_unlinkable) (member-eq st '(:unlinkable :invalid))
                        (member-eq st '(:trap :exception))))
                  (e (if (and (member-eq st '(:trap :exception)) s) (cons s (cdr e)) e)))
             (mv k (and ok t) st e state)))))
      (otherwise (mv :unknown nil k e state)))))

; RUN-CMD with the time budget for the commands that run an action (the
; suite runner's; RUN-CMD itself is also extracted for the demo, which has
; no state, so it stays as it is)
(defun run-cmd-timed (c e state)
  (let ((k (car c)))
    (if (member-eq k '(:action :assert_return :assert_trap :assert_exception))
        (mv-let (r e state) (do-action-timed (cadr c) e state)
          (let ((ok (case k
                      (:action (not (member-eq r '(:error :fuel :time))))
                      (:assert_return (and (true-listp r) (vals-ok (caddr c) r)))
                      (:assert_trap (eq r :trap))
                      (t (eq r :exception)))))
            (mv k ok r e state)))
      (run-cmd c e state))))

; a one-word class of a failure, for the summary: the keyword of a
; status (:FUEL :ERROR :TRAP :EXCEPTION :UNLINKABLE :INVALID :PARSED ...),
; :WRONG-RESULT for values that do not match, :STUCK for a configuration
; that no rule steps
(defun value-instr-p (x)
  (and (consp x) (member-eq (car x) (quote (:const :vconst :ref.i31_num :ref.null_addr :ref.struct_addr
                                             :ref.array_addr :ref.func_addr :ref.exn_addr :ref.host_addr :ref.extern)))))
(defun all-values-p (l) (or (atom l) (and (value-instr-p (car l)) (all-values-p (cdr l)))))
(defun fail-class (detail)
  (cond ((symbolp detail) (or detail :none))
        ((all-values-p detail) :wrong-result)
        (t :stuck)))

; one top-level form per command (run-one-3.0.lsp): prints T7-TRY, then
; T7-CMD KIND OK (and T7-FAIL with the command on failure)
(defun t7-cmd (c state)
  (prog2$ (cw "T7-TRY ~x0~%" (car c))
          (mv-let (kind ok detail e state) (run-cmd-timed c (@ t7-env) state)
            (let ((state (f-put-global 't7-env e state)))
              (prog2$ (and kind (cw "T7-CMD ~x0 ~x1~%" kind (and ok t)))
                      (prog2$ (and kind (not ok) (not (member-eq kind '(:assert_exhaustion-skipped :assert_invalid-skipped :assert_malformed-text-skipped)))
                                   (prog2$ (cw "T7-FAILKIND ~x0 ~x1~%" kind (fail-class detail))
                                          (cw "T7-FAIL ~x0 ~x1~%" c detail)))
                              (mv nil :ok state)))))))

(defconst *s0* '(:%rec (:tags) (:globals) (:mems) (:tables) (:funcs) (:datas) (:elems) (:structs) (:arrays) (:exns)))

(defun spectest-env (state)
  (mv-let (bs state) (read-bytes (concatenate 'string *data* "spectest.wasm") state)
    (let ((p (and bs (gram/bmodule bs))))
      (mv-let (st s inst) (if (and p (null (cadr p))) (instantiate (car p) (list *s0* nil nil nil)) (mv :malformed nil nil))
        (mv (and (eq st :ok) (list s nil nil (list (cons "spectest" inst)))) state)))))

(defun t7-forms (cmds)
  (if (atom cmds) nil (cons (list 't7-cmd (list 'quote (car cmds)) 'state) (t7-forms (cdr cmds)))))

; sets T7-ENV and T7-FORMS for script NAME; nil if spectest fails
(defun t7-setup (name state)
  (mv-let (e0 state) (spectest-env state)
    (mv-let (cmds state) (read-obj (concatenate 'string *data* name ".lsp") state)
      (let* ((state (f-put-global 't7-env e0 state))
             (state (f-put-global 't7-forms (and e0 (t7-forms cmds)) state)))
        (prog2$ (if e0 nil (cw "T7-ERROR spectest host module failed to instantiate~%"))
                (mv nil (and e0 t) state))))))
