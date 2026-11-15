; W0 item 2: THROWAWAY extractor for the slice (rt/ and the books 0_*, 1_*).
; W2 replaces it with demo/extract. Runs in ACL2's raw Lisp after the 3.0
; portcullis, so symbols are read with the real W3T/WRT/ACL2 packages.
;
; (w0::extract-slice ROOT-BOOK OUT-FILE STOP-PREFIXES) follows include-book
; from ROOT-BOOK (depth first, an included book before the includer), keeps
; the books whose file name starts with one of STOP-PREFIXES or lies in rt/,
; and writes every kept event, package-qualified, to OUT-FILE. Prints a
; report of events by kind.

(defpackage "W0" (:use "COMMON-LISP"))
(in-package "W0")

(defvar *kinds* nil)            ; alist kind -> count
(defvar *big-ints* 0)           ; integer literals with |n| > 2^53
(defvar *ratios* 0)
(defvar *seen* nil)

(defun bump (k) (let ((c (assoc k *kinds* :test #'equal)))
                  (if c (incf (cdr c)) (push (cons k 1) *kinds*))))

;; ---------------------------------------------------------------- printer
(defun pname (s)
  (with-output-to-string (o)
    (write-char #\| o)
    (loop for c across s do (when (member c '(#\| #\\)) (write-char #\\ o)) (write-char c o))
    (write-char #\| o)))

(defun emit (x o)
  (cond ((null x) (write-string "COMMON-LISP::NIL" o))
        ((eq x t) (write-string "COMMON-LISP::T" o))
        ((keywordp x) (write-string ":" o) (write-string (pname (symbol-name x)) o))
        ((symbolp x)
         (write-string (pname (package-name (symbol-package x))) o)
         (write-string "::" o)
         (write-string (pname (symbol-name x)) o))
        ((integerp x)
         (when (> (abs x) (expt 2 53)) (incf *big-ints*))
         (format o "~D" x))
        ((rationalp x) (incf *ratios*) (format o "~D/~D" (numerator x) (denominator x)))
        ((stringp x) (prin1 x o))
        ((characterp x) (format o "#\\~A" (if (graphic-char-p x) (string x) (char-name x))))
        ((consp x)
         (write-char #\( o)
         (loop for tail on x
               for first = t then nil
               do (unless first (write-char #\Space o))
                  (emit (car tail) o)
                  (when (and (cdr tail) (atom (cdr tail)))
                    (write-string " . " o) (emit (cdr tail) o)))
         (write-char #\) o))
        (t (error "unprintable ~S" x))))

;; ------------------------------------------------- clause-chain flattening
;; The translator compiles the clauses of a definition into
;;   (LET ((%R X1)) (DECLARE (IGNORABLE %R)) (IF %R (CAR %R) <rest>))
;; with <rest> the same shape for the next clause, so a definition with n
;; clauses nests n deep (GRAM/BINSTR/REP32: depth 1010), deeper than the JS
;; parsers of node (default stack), Chromium and Firefox accept. Each Xi is
;; NIL or (LIST v). Rewrite, the same for every chain, into one flat sequence:
;;   (LET ((%CHAIN X1)) (IF (NOT %CHAIN) (SETQ %CHAIN X2)) ...
;;        (IF %CHAIN (CAR %CHAIN) <final rest>))
;; Equivalent when %R does not occur in X2..Xn (in the nested form they see
;; the previous %R, which is NIL); the chain stops at the first Xi that
;; mentions %R. (W0 option; W2 decides.)
(defvar *flattened* 0)
(defvar *flatten* nil)
(defun occurs (s x) (if (consp x) (or (occurs s (car x)) (occurs s (cdr x))) (eq s x)))
(defun sym= (x name) (and (symbolp x) (string= (symbol-name x) name)))
(defun chain-link (x)
  "If X is one clause link, return (values Xi rest %R); NIL otherwise."
  (if (and (consp x) (sym= (car x) "LET") (null (cdr (last x)))
           (= (length x) 4)
           (consp (second x)) (null (cdr (second x))) (consp (first (second x)))
           (sym= (first (first (second x))) "%R")
           (let ((d (third x))) (and (consp d) (sym= (car d) "DECLARE")))
           (let ((i (fourth x)))
             (and (consp i) (eq (car i) (quote if)) (null (cdr (last i))) (= (length i) 4)
                  (eq (second i) (first (first (second x))))
                  (or (equal (third i) (list (quote car) (second i)))
                      (eq (third i) (second i))))))
      (values (second (first (second x))) (fourth (fourth x)) (first (first (second x)))
              (if (consp (third (fourth x))) :car :self))
      nil))
(defun flatten (x)
  (if (atom x) x
      (multiple-value-bind (x1 rest r kind) (chain-link x)
        (if (null r)
            (cons (flatten (car x)) (flatten (cdr x)))
            (let ((xs (list x1)))
              (loop (multiple-value-bind (xi rest2 r2 kind2) (chain-link rest)
                      (if (and r2 (eq r2 r) (eq kind2 kind) (not (occurs r xi)))
                          (progn (push xi xs) (setq rest rest2))
                          (return))))
              (if (< (length xs) 3)
                  (cons (flatten (car x)) (flatten (cdr x)))
                  (let ((c (intern "%CHAIN" "WRT")))
                    (incf *flattened*)
                    (setq xs (nreverse xs))
                    `(let ((,c ,(flatten (car xs))))
                       ,@(mapcar (lambda (xi) `(if (not ,c) (setq ,c ,(flatten xi)))) (cdr xs))
                       (if ,c ,(if (eq kind :car) `(car ,c) c) ,(flatten rest))))))))))

;; ---------------------------------------------------------------- events
(defun head-name (form) (and (consp form) (symbolp (car form)) (symbol-name (car form))))

(defun translate-event (form)
  "List of output forms for one top-level event (closed table: unknown = error)."
  (let ((h (head-name form)))
    (bump h)
    (cond
      ((member h '("IN-PACKAGE" "INCLUDE-BOOK" "SET-VERIFY-GUARDS-EAGERNESS"
                   "SET-BOGUS-MUTUAL-RECURSION-OK" "DEFTHM" "IN-THEORY" "PROGRAM"
                   "%TRY-GUARDS-T" "DEFMACRO" "MEMOIZE" "VALUE-TRIPLE" "TABLE"
                   "VERIFY-GUARDS")
               :test #'string=)
       nil)
      ((string= h "%TRY-LOGIC-T") (translate-event (third form)))
      ((string= h "DEFUN") (list (if *flatten* (flatten form) form)))
      ((string= h "MUTUAL-RECURSION") (list (cons 'progn (if *flatten* (mapcar #'flatten (cdr form)) (cdr form)))))
      ((string= h "ENCAPSULATE") nil)   ; the %hostcall-hook signature
      ((string= h "DEFATTACH")          ; (defattach f g): f calls g
       (let ((f (second form)) (g (third form)) (args (intern "ARGS" "WRT")))
         (list `(defun ,f (&rest ,args) (apply ',g ,args)))))
      (t (error "W0 slice: unknown event ~A" h)))))

(defun book-path (dir name) (merge-pathnames (concatenate 'string name ".lisp") dir))

(defun read-book (path)
  (with-open-file (in path)
    (let ((*package* (find-package "ACL2")) (forms nil) (eof (list :eof)))
      (loop for f = (read in nil eof)
            until (eq f eof)
            do (when (equal (head-name f) "IN-PACKAGE")
                 (setq *package* (find-package (second f))))
               (push f forms))
      (nreverse forms))))

(defun keep-book-p (path prefixes)
  (or (search "/rt/" (namestring path))
      (some (lambda (p) (eql 0 (search p (pathname-name path)))) prefixes)))

(defun walk (path prefixes out)
  (let ((path (truename path)))
    (unless (member path *seen* :test #'equal)
      (push path *seen*)
      (let ((forms (read-book path)))
        ;; included books first
        (dolist (f forms)
          (when (equal (head-name f) "INCLUDE-BOOK")
            (walk (book-path (make-pathname :name nil :type nil :defaults path) (second f))
                  prefixes out)))
        (when (keep-book-p path prefixes)
          (format t "~&; book ~A~%" (pathname-name path))
          (format out "~&;;; book ~A~%" (pathname-name path))
          (dolist (f forms)
            (dolist (o (translate-event f))
              (emit o out) (terpri out) (terpri out))))))))

(defun extract-slice (root out-file prefixes)
  (setq *kinds* nil *big-ints* 0 *ratios* 0 *seen* nil)
  (with-open-file (out out-file :direction :output :if-exists :supersede)
    (walk root prefixes out))
  (format t "~&; events by kind:~%")
  (dolist (k (sort (copy-list *kinds*) #'> :key #'cdr)) (format t ";   ~6D ~A~%" (cdr k) (car k)))
  (format t "; integer literals above 2^53: ~D; ratio literals: ~D~%" *big-ints* *ratios*)
  (format t "; clause chains flattened: ~D~%" *flattened*))
