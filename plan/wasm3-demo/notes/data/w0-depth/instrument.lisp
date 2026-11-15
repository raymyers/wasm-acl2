; W0 item 4: deepest recursion of the generated 3.0 semantics on a run,
; measured in ACL2 (SBCL). Loaded in raw Lisp after t7-lib-3.0 (which
; includes gen/wasm-3.0/wasm3). Every defun of rt/ and of the books on the
; include chain is redefined with the same body plus a counter, so
; self-calls are counted too:
;   *depth*        nesting of instrumented calls (bound with LET)
;   *stack*        the names on the current call path (a shared cons list)
;   (get f :act)   active frames of f; (get f :max) its maximum
; At the deepest point the path is kept (*deep-stack*) and summarized by
; name. Uses the throwaway extractor's book walker (w0-slice).

(in-package "W0")

(defvar *depth* 0)
(defvar *max-depth* 0)
(defvar *stack* nil)
(defvar *deep-stack* nil)
(defvar *instrumented* nil)

;; No special bindings (a LET of a special per call exhausts SBCL's binding
;; stack at this depth): global updates, undone by UNWIND-PROTECT.
(defmacro counted (name &body body)
  `(let ((old-stack *stack*)
         (k (1+ (or (get ',name :act) 0))))
     (incf *depth*)
     (setq *stack* (cons ',name old-stack))
     (when (> *depth* *max-depth*) (setq *max-depth* *depth* *deep-stack* *stack*))
     (setf (get ',name :act) k)
     (when (> k (or (get ',name :max) 0)) (setf (get ',name :max) k))
     (unwind-protect (progn ,@body)
       (decf *depth*)
       (setq *stack* old-stack)
       (setf (get ',name :act) (1- k)))))

(defun strip-declares (body)
  (loop while (and (consp (car body)) (sym= (caar body) "DECLARE")) do (pop body))
  body)

(defun instrument-defun (d)
  ;; (defun name args [doc] decl* body)
  (destructuring-bind (name args &rest body) (cdr d)
    (push name *instrumented*)
    (let ((body (strip-declares body)))
      `(defun ,name ,args (counted ,name ,@body)))))

(defun defuns-of (form)
  (let ((h (head-name form)))
    (cond ((null h) nil)
          ((string= h "%TRY-LOGIC-T") (defuns-of (third form)))
          ((string= h "DEFUN") (list form))
          ((string= h "MUTUAL-RECURSION") (cdr form))
          (t nil))))

(defun instrument-books (root)
  (setq *seen* nil *instrumented* nil)
  (let ((forms nil))
    (labels ((walk1 (path)
               (let ((path (truename path)))
                 (unless (member path *seen* :test #'equal)
                   (push path *seen*)
                   (let ((fs (read-book path)))
                     (dolist (f fs)
                       (when (equal (head-name f) "INCLUDE-BOOK")
                         (walk1 (book-path (make-pathname :name nil :type nil :defaults path) (second f)))))
                     (dolist (f fs) (dolist (d (defuns-of f)) (push d forms))))))))
      (walk1 root))
    (setq forms (nreverse forms))
    ;; The rt/ helpers that only build ACL2 events (%try-logic etc.) and the
    ;; hostcall hook are left as they are.
    (let ((sb-ext:*evaluator-mode* :compile)
          (*error-output* (make-broadcast-stream)))
      (handler-bind ((warning #'muffle-warning))
        (dolist (d forms)
          (unless (member (symbol-name (second d)) '("%HOSTCALL-HOOK") :test #'string=)
            (eval (instrument-defun d))))))
    (format t "~&W0-DEPTH instrumented ~D defuns~%" (length *instrumented*))))

(defun reset-counts ()
  (setq *max-depth* 0 *deep-stack* nil)
  (dolist (f *instrumented*) (setf (get f :max) 0 (get f :act) 0)))

(defun report (label)
  (format t "~&W0-DEPTH ~A: max nesting ~D~%" label *max-depth*)
  (let ((counts nil))
    (dolist (f *deep-stack*)
      (let ((c (assoc f counts))) (if c (incf (cdr c)) (push (cons f 1) counts))))
    (format t "W0-DEPTH ~A: path at the deepest point, frames by function:~%" label)
    (dolist (c (subseq (sort counts #'> :key #'cdr) 0 (min 12 (length counts))))
      (format t "W0-DEPTH   ~7D ~A::~A~%" (cdr c) (package-name (symbol-package (car c))) (car c))))
  (format t "W0-DEPTH ~A: functions by own maximum active frames (top 12):~%" label)
  (let ((fs (sort (remove-if (lambda (f) (< (or (get f :max) 0) 2)) (copy-list *instrumented*))
                  #'> :key (lambda (f) (get f :max)))))
    (dolist (f (subseq fs 0 (min 12 (length fs))))
      (format t "W0-DEPTH   ~7D ~A::~A~%" (get f :max) (package-name (symbol-package f)) f))))
