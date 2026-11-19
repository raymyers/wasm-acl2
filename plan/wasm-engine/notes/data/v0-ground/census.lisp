; V0 item 1 (plan/wasm-engine/plan2.md): which rule functions a run of the
; fast machine executes, with counts. Raw Lisp, loaded by a driver after the
; engine books (census-slides.sh; engine/tex/texrun.lisp when TEXCENSUS is
; set). Nothing here is part of a certified book.
;
; A rule is counted when its function returns a result (it fired). The fast
; machine reaches a rule function in four ways, and each is wrapped:
;   - the rule function itself and its executable-counterpart (EC-CALL);
;   - the generated fast version of a memory rule (WE::FAST-<rule>);
;   - the six hot paths of WE::FAST-HOT-STEP, which compute a rule's result
;     without calling it: counted under the rule they stand for.
(in-package "ACL2")

(defvar *census* (make-hash-table :test 'eq))    ; rule -> (count)
(defvar *census-in* nil)                         ; inside a counted call

(defun census-cell (rule)
  (or (gethash rule *census*) (setf (gethash rule *census*) (list 0))))

(defun census-wrap (fn rule)
  (when (and fn (fboundp fn))
    (let ((cell (census-cell rule)))
      (sb-int:encapsulate fn 'census
        (lambda (f &rest args)
          (if *census-in*
              (apply f args)
            (let ((r (let ((*census-in* t)) (apply f args))))
              (when r (incf (car cell)))
              r)))))))

(defun census-*1* (sym)
  (let ((p (find-package (concatenate 'string "ACL2_*1*_" (package-name (symbol-package sym))))))
    (and p (find-symbol (symbol-name sym) p))))

(defun census-fast (sym) (find-symbol (concatenate 'string "FAST-" (symbol-name sym)) "WE"))

(dolist (rule (symbol-value 'we::*step-rules*))
  (census-wrap rule rule)
  (census-wrap (census-*1* rule) rule)
  (let ((fast (census-fast rule)))
    (when fast
      (census-wrap fast rule)
      (census-wrap (census-*1* fast) rule))))

(defun census-hot-rule (name)
  (let ((rule (find-symbol name "W3T")))
    (unless (member rule (symbol-value 'we::*step-rules*)) (error "census: no rule ~a" name))
    (census-cell rule)))

(let ((local.get (census-hot-rule "STEP_READ/SPLIT/R-LOCAL.GET"))
      (local.set (census-hot-rule "STEP/R-LOCAL.SET"))
      (local.tee (census-hot-rule "STEP_PURE/R-LOCAL.TEE"))
      (binop-val (census-hot-rule "STEP_PURE/R-BINOP-VAL"))
      (binop-trap (census-hot-rule "STEP_PURE/R-BINOP-TRAP"))
      (relop (census-hot-rule "STEP_PURE/R-RELOP"))
      (br_if-true (census-hot-rule "STEP_PURE/R-BR_IF-TRUE"))
      (br_if-false (census-hot-rule "STEP_PURE/R-BR_IF-FALSE")))
  (sb-int:encapsulate 'we::fast-hot-step 'census
    (lambda (f i fm)
      (let ((is (we::fm-is fm)))
        (multiple-value-bind (handled fm2) (funcall f i fm)
          (when handled
            (incf (car (case (car i)
                         (:local.get local.get)
                         (:local.set local.set)
                         (:local.tee local.tee)
                         (:binop (if (equal (car (we::fm-is fm)) '(:trap)) binop-trap binop-val))
                         (:relop relop)
                         (t (if (eq (we::fm-is fm) (cdr is)) br_if-false br_if-true))))))
          (values handled fm2))))))

(defun census-report ()
  (let ((rows nil) (total 0))
    (maphash (lambda (k v) (when (plusp (car v)) (push (cons k (car v)) rows) (incf total (car v)))) *census*)
    (setq rows (sort rows #'> :key #'cdr))
    (format t "~%CENSUS-TOTAL ~d rule applications, ~d of ~d rule functions~%"
            total (length rows) (length (symbol-value 'we::*step-rules*)))
    (dolist (r rows)
      (format t "CENSUS ~12d ~a~%" (cdr r) (symbol-name (car r))))
    (finish-output)))
