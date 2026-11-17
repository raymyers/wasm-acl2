; T7 conformance driver library (wasm1 T7, finished in wasm3 prep P5): run the
; WASM 1.0 spec test suite (spec-test-1 of the pinned WebAssembly/spec,
; converted by `make spec-data`, see ../oracle/gen-spec-tests.mjs) on the
; GENERATED semantics only: .wasm bytes -> GRAM/BMODULE -> Module_ok /
; $instantiate (imports resolved through `register`ed instances and the
; spectest host module) -> $invoke + STEP. The store is threaded through every
; command of a script, as in the reference interpreter. `make spec` runs every
; script in its own ACL2 session (run-one.lsp, run-all.sh), so a crash or a
; timeout in one script costs only that script; every command prints a
; T7-CMD line as it finishes, so the commands before a crash still count.
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

(defun read-obj (file state)
  (mv-let (channel state) (open-input-channel file :object state)
    (if (null channel) (mv nil state)
      (mv-let (eofp obj state) (read-object channel state)
        (declare (ignore eofp))
        (let ((state (close-input-channel channel state))) (mv obj state))))))

; a complete parse of data/FILE, or nil (DIR, the script, is unused: file names are unique)
(defun parse-file (dir file state)
  (declare (ignore dir))
  (mv-let (bs state) (read-bytes (concatenate 'string "data/" file) state)
    (let ((p (and bs (gram/bmodule bs))))
      (mv (and p (null (cadr p)) (car p)) state))))

; --- values ------------------------------------------------------------

(defun vt-bits (vt) (if (member-eq vt '(:i64 :f64)) 64 32))
(defun to-val (v)                           ; (:I32 n) / (:F32 bits) -> (:CONST (:I32) x)
  (let ((vt (car v)))
    (list :const (list vt) (if (member-eq vt '(:f32 :f64)) (%bitsf (vt-bits vt) (cadr v)) (cadr v)))))
(defun to-vals (vs) (if (atom vs) nil (cons (to-val (car vs)) (to-vals (cdr vs)))))

(defun val-ok (want got)
  ;; want (:F32 bits|:NAN-CANONICAL|:NAN-ARITHMETIC); got (:CONST (vt) x)
  (and (consp got) (eq (car got) :const) (equal (cadr got) (list (car want)))
       (let* ((vt (car want)) (x (caddr got)) (n (vt-bits vt)))
         (if (member-eq vt '(:f32 :f64))
             (let* ((bits (%fbits n x))
                    (sign (expt 2 (1- n)))
                    (quiet (if (= n 32) #x7fc00000 #x7ff8000000000000)))
               (case (cadr want)
                 (:nan-canonical (= (logand bits (1- sign)) quiet))
                 (:nan-arithmetic (= (logand bits quiet) quiet))
                 (t (equal bits (cadr want)))))
           (equal x (cadr want))))))

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
  ;; MODNAME: byte list from an import
  (cond ((equal modname (str-bytes "spectest")) (cdr (assoc-equal "spectest" (fourth e))))
        (t (let ((hit (assoc-equal modname (fourth e)))) (and hit (cdr hit))))))

(defun resolve-imports (ims e)
  ;; (mv ok addrs)
  (if (atom ims) (mv t nil)
    (let* ((im (car ims)) (inst (registered (cadr im) e))
           (addr (and inst (find-export (caddr im) (%get-field inst :exports)))))
      (if (null addr) (mv nil nil)
        (mv-let (ok rest) (resolve-imports (cdr ims) e)
          (mv ok (cons addr rest)))))))

; The generated STEPS has fuel 10^6; spec scripts that compute a lot (fib
; through call_indirect, ...) would take hours at that budget, so the driver
; iterates the generated STEP itself with its own deterministic budget. A
; step costs ~30 ms here: the generated termination checks (%SIZE of the
; configuration, incl. 64 KiB memories as byte lists) run on every step and
; in the ctxt-instrs split search. Actions that need more are :FUEL.
(defconst *spec-fuel* 3000)
(defun run-steps (c n)
  (if (zp n) nil
    (let ((r (step c))) (if r (run-steps (car r) (1- n)) (list c)))))

(defun final-config (c)
  ;; run a config to its normal form: (mv store instrs frame) or (mv nil :fuel nil)
  (let ((r (and c (run-steps c *spec-fuel*))))
    (if (null r) (mv nil :fuel nil)
      (let* ((cf (car r)) (z (cadr cf)))
        (mv (cadr z) (caddr cf) (caddr z))))))

(defun instantiate (m e)
  ;; (mv status store inst): status :ok, :unlinkable, :invalid, :trap, :fuel
  (mv-let (ok addrs) (resolve-imports (nth 2 m) e)
    (if (not ok) (mv :unlinkable nil nil)
      (let ((c ($instantiate (env-store e) m addrs)))
        (if (null c) (mv :invalid nil nil)
          (mv-let (s instrs f) (final-config c)
            (cond ((eq instrs :fuel) (mv :fuel nil nil))
                  ((equal instrs '((:trap))) (mv :trap s nil))
                  (t (mv :ok s (%get-field f :module))))))))))

(defun do-action (a e)
  ;; (mv result e): result = list of result vals, :trap, :fuel or :error
  (let* ((inst (env-inst e (cadr a)))
         (addr (and inst (find-export (caddr a) (%get-field inst :exports)))))
    (cond ((null addr) (mv :error e))
          ((eq (car a) :get)
           (if (eq (car addr) :global)
               (mv (list (%get-field (nth (cadr addr) (%get-field (env-store e) :globals)) :value)) e)
             (mv :error e)))
          ((not (eq (car addr) :func)) (mv :error e))
          (t (mv-let (s instrs f) (final-config ($invoke (env-store e) (cadr addr) (to-vals (cadddr a))))
               (declare (ignore f))
               (cond ((eq instrs :fuel) (mv :fuel e))
                     (t (mv (if (equal instrs '((:trap))) :trap instrs)
                            (cons s (cdr e))))))))))

; --- commands -------------------------------------------------------------
; tally: alist kind -> (pass . total); fails: list of (dir line-ish cmd result)

(defun bump (kind ok tally)
  ;; one T7-CMD line per command (run-all.sh counts them)
  (let ((old (prog2$ (cw "T7-CMD ~x0 ~x1~%" kind (and ok t)) (or (cdr (assoc-eq kind tally)) (cons 0 0)))))
    (put-assoc-eq kind (cons (+ (car old) (if ok 1 0)) (1+ (cdr old))) tally)))

(defun run-cmds (cmds dir e tally fails state)
  (if (endp cmds) (mv tally fails state)
    (let* ((c (car cmds)) (k (car c)))
      (case k
        (:module
         (mv-let (m state) (parse-file dir (cadr c) state)
           (mv-let (st s inst) (if m (instantiate m e) (mv :malformed nil nil))
             (let* ((ok (eq st :ok))
                    (e (if ok (list s inst (if (caddr c) (acons (caddr c) inst (third e)) (third e)) (fourth e))
                         ;; a failed module: later commands that use it fail
                         (list (first e) nil (third e) (fourth e)))))
               (run-cmds (cdr cmds) dir e (bump :module ok tally)
                         (if ok fails (cons (list dir c st) fails)) state)))))
        (:register
         (let* ((inst (env-inst e (caddr c)))
                (e (list (first e) (second e) (third e) (acons (cadr c) inst (fourth e)))))
           (run-cmds (cdr cmds) dir e tally fails state)))
        ((:action :assert_return :assert_trap)
         (mv-let (r e) (do-action (cadr c) e)
           (let ((ok (case k
                       (:action (not (member-eq r '(:error :fuel))))
                       (:assert_return (and (true-listp r) (vals-ok (caddr c) r)))
                       (t (eq r :trap)))))
             (run-cmds (cdr cmds) dir e (bump k ok tally) (if ok fails (cons (list dir c r) fails)) state))))
        (:assert_exhaustion                 ; no call-stack limit in the spec semantics
         (run-cmds (cdr cmds) dir e (bump :assert_exhaustion-skipped nil tally) fails state))
        (:assert_invalid
         (mv-let (m state) (parse-file dir (cadr c) state)
           (let* ((r (if m (if (module_ok m) :accepted :rejected) :not-parsed)) (ok (eq r :rejected)))
             (run-cmds (cdr cmds) dir e (bump k ok tally) (if ok fails (cons (list dir c r) fails)) state))))
        (:assert_malformed
         (if (eq (cadddr c) :text)
             (run-cmds (cdr cmds) dir e (bump :assert_malformed-text-skipped nil tally) fails state)
           (mv-let (m state) (parse-file dir (cadr c) state)
             (let ((ok (null m)))
               (run-cmds (cdr cmds) dir e (bump k ok tally) (if ok fails (cons (list dir c :parsed) fails)) state)))))
        ((:assert_unlinkable :assert_uninstantiable)
         (mv-let (m state) (parse-file dir (cadr c) state)
           (mv-let (st s inst) (if m (instantiate m e) (mv :malformed nil nil))
             (declare (ignore inst))
             (let* ((ok (if (eq k :assert_unlinkable) (member-eq st '(:unlinkable :invalid)) (eq st :trap)))
                    ;; an uninstantiable module's partial effects stay in the store
                    (e (if (and (eq st :trap) s) (cons s (cdr e)) e)))
               (run-cmds (cdr cmds) dir e (bump k ok tally) (if ok fails (cons (list dir c st) fails)) state)))))
        (otherwise (run-cmds (cdr cmds) dir e (bump :unknown nil tally) fails state))))))

(defconst *s0* '(:%rec (:funcs) (:globals) (:tables) (:mems)))

(defun spectest-env (state)
  (mv-let (bs state) (read-bytes "data/spectest.wasm" state)
    (let ((p (and bs (gram/bmodule bs))))
      (mv-let (st s inst) (if p (instantiate (car p) (list *s0* nil nil nil)) (mv :malformed nil nil))
        (mv (and (eq st :ok) (list s nil nil (list (cons "spectest" inst)))) state)))))

(defun sum-pass (tally) (if (endp tally) 0 (+ (cadr (car tally)) (sum-pass (cdr tally)))))
(defun sum-total (tally) (if (endp tally) 0 (+ (cddr (car tally)) (sum-total (cdr tally)))))

(defun merge-tally (a b)
  (if (endp a) b
    (merge-tally (cdr a)
                 (let ((old (or (cdr (assoc-eq (caar a) b)) (cons 0 0))))
                   (put-assoc-eq (caar a) (cons (+ (cadr (car a)) (car old)) (+ (cddr (car a)) (cdr old))) b)))))

(defun remove-skipped (tally)
  ;; drop the skipped kinds (exhaustion, text-format malformed) from a tally
  (cond ((endp tally) nil)
        ((member-eq (caar tally) (quote (:assert_exhaustion-skipped :assert_malformed-text-skipped)))
         (remove-skipped (cdr tally)))
        (t (cons (car tally) (remove-skipped (cdr tally))))))

(defun run-files (names e0 tally per-file fails state)
  (if (endp names) (mv tally (reverse per-file) fails state)
    (mv-let (cmds state) (read-obj (concatenate 'string "data/" (car names) ".lsp") state)
      (mv-let (ft ff state) (run-cmds cmds (car names) e0 nil nil state)
        (prog2$ (cw "  ~s0: ~x1~%" (car names) ft)
                (run-files (cdr names) e0 (merge-tally ft tally)
                           (cons (list (car names) (sum-pass (remove-skipped ft)) (sum-total (remove-skipped ft))) per-file)
                           (append (take (min 8 (acl2::len ff)) (reverse ff)) fails) state))))))

; Run one script (data/NAME.lsp) from the spectest environment; prints
; T7-CMD lines, then T7-DONE with the tally and T7-FAILS with a sample.
(defun run-one-script (name state)
  (mv-let (e0 state) (spectest-env state)
    (if (null e0)
        (prog2$ (cw "T7-ERROR spectest host module failed to instantiate~%") state)
      (mv-let (cmds state) (read-obj (concatenate 'string "data/" name ".lsp") state)
        (mv-let (tally fails state) (run-cmds cmds name e0 nil nil state)
          (prog2$ (cw "T7-DONE ~s0 ~x1~%T7-FAILS ~x2~%" name (remove-skipped tally)
                      (take (min 8 (acl2::len fails)) (reverse fails)))
                  state))))))
