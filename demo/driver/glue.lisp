;;;; demo/driver/glue.lisp: the JS-facing entry points (W4). Thin wrappers
;;;; over the extracted semantics and the extracted helpers of
;;;; tests/spec/t7-lib-3.0.lisp; they only turn ACL2 multiple values into
;;;; lists, which JS can read (a direct JS call sees the first value only).
(defpackage "DEMO" (:use "COMMON-LISP"))
(in-package "DEMO")

;; (decode bytes) -> module or NIL: a complete parse (as t7's parse-file)
(defun decode (bytes)
  (let ((p (w3t::gram/bmodule bytes)))
    (and p (null (cadr p)) (car p))))

;; (instantiate module env) -> (status store inst), as t7's INSTANTIATE
(defun instantiate (m env) (multiple-value-list (w3t::instantiate m env)))

;; (do-action action env) -> (result env), as t7's DO-ACTION
(defun do-action (a env) (multiple-value-list (w3t::do-action a env)))

;; the empty store and environment of t7 (*s0*, no instances)
(defun empty-env () (list w3t::*s0* nil nil nil))

;;; W4: the conformance driver's own command runner (t7's RUN-CMD, with
;;; PARSE-FILE and SPECTEST-ENV, extracted by name). The only part supplied
;;; here is the file input they call, READ-BYTES, which asks the JS host
;;; (globalThis.DEMOIO.readBytes: path -> list of bytes, or NIL). STATE is
;;; not used by the extracted code beyond passing it to READ-BYTES.
(defun w3t::read-bytes (file state)
  (values (#j:DEMOIO:readBytes (jscl-xc::jsstring file)) state))

;; (run-cmd command env) -> (kind ok detail env), as t7's RUN-CMD
(defun run-cmd (c env)
  (multiple-value-bind (kind ok detail e) (w3t::run-cmd c env nil)
    (list kind ok detail e)))

;; the environment with the registered spectest module, or NIL
(defun spectest-env () (values (w3t::spectest-env nil)))

;;; W4 item 1 / W5: the page's entry points. An environment is t7's
;;; (store current-instance named registered).

;; (load-module bytes env) -> (status env): decode, then t7's INSTANTIATE
;; against ENV's registered modules; on :ok the module is the current
;; instance of the new env (as run-cmd :module). Status :malformed when the
;; bytes do not decode.
(defun load-module (bytes env)
  (let ((m (decode bytes)))
    (if (null m) (list :malformed env)
      (multiple-value-bind (st s inst) (w3t::instantiate m env)
        (if (eq st :ok)
            (list st (list s inst (third env) (fourth env)))
          (list st env))))))

;;; W4 item 2: host functions. The 3.0 semantics calls a host function
;;; (a function instance whose code is (:_HOSTFUNC hf)) through
;;; WRT::%HOSTCALL-HOOK (rt/builtins-3.0.lisp): (hf store vals) -> a list
;;; whose first element is (:RES store' (:_VALS results)); no element means
;;; the call does not step. The books attach %HOSTCALL-NONE; the driver
;;; attaches HOST-CALL, which asks the JS host:
;;; globalThis.DEMOHOST.call(hf, vals, none) -> a Lisp list of result values,
;;; or NONE for "no result" (driver/host.js: the default host has none).
;;; The step rules pass (:_HOSTFUNC hf) and try $HOSTCALL several times per
;;; step (a length check, then the binding, for each candidate split of the
;;; arguments, in both call_ref-hostfunc rules), so the JS host must answer
;;; as a function of (hf, vals): a host with an effect (a print) records it
;;; once per step and argument list, not once per call.
(defun host-call (hf s vals)
  (let ((r (#j:DEMOHOST:call (if (and (consp hf) (eq (car hf) :_hostfunc)) (cadr hf) hf) vals :none)))
    (if (eq r :none) nil (list (list :res s (list :_vals r))))))
(setf (symbol-function 'wrt::%hostcall-hook) #'host-call)

;; (register-host env modname bytes) -> (status env'): instantiate BYTES, a
;; module whose exported functions declare the host functions' types (so
;; their function types are the semantics' own), make every exported
;; function a host function (:_HOSTFUNC (modname field)), with MODNAME and
;; FIELD lists of character codes as in imports, and register the instance
;; under MODNAME, as t7's run-cmd :register does.
(defun register-host (env modname bytes)
  (let* ((r (load-module bytes env)) (st (first r)) (e (second r)))
    (if (not (eq st :ok)) (list st env)
      (let* ((inst (second e)) (s (first e)) (funcs (wrt::%get-field s :funcs)))
        (dolist (x (wrt::%get-field inst :exports))
          (let ((addr (wrt::%get-field x :addr)))
            (when (eq (car addr) :func)
              (setq funcs (acl2::update-nth (cadr addr)
                                            (wrt::%put-field (nth (cadr addr) funcs) :code
                                                             (list :_hostfunc (list modname (wrt::%get-field x :name))))
                                            funcs)))))
        (list :ok (list (wrt::%put-field s :funcs funcs) (second env) (third env)
                        (acons modname inst (fourth env))))))))

;; (invoke env name args fuel) -> (result env): t7's DO-ACTION on
;; (:invoke nil name args), NAME a list of character codes (as in the
;; converted spec data), ARGS a list of (:I32 n) / (:I64 n) / (:F32 bits)
;; / (:F64 bits) / ... as t7 reads them. RESULT is a list of values,
;; :trap, :exception, :fuel or :error. FUEL (steps) replaces *spec-fuel*
;; for this call when it is a positive integer.
(defun invoke (env name args fuel)
  (let ((w3t::*spec-fuel* (if (and (integerp fuel) (> fuel 0)) fuel w3t::*spec-fuel*)))
    (multiple-value-list (w3t::do-action (list :invoke nil name args) env))))
