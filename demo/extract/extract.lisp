; demo/extract: the build step of the JSCL demo (plan/wasm3-demo §3, W2).
;
; Runs in ACL2's raw Lisp after the portcullis of translate/gen/wasm-3.0, so
; every form is read with the real W3T/WRT/ACL2 packages. Reads (never
; writes) the generated books, rt/ and the conformance driver, and writes
; JSCL-ready Lisp to demo/build/lisp/:
;   NN-<book>.lisp   one file per book, in include order (rt/ first)
;   driver.lisp      the named pure helpers of tests/spec/t7-lib-3.0.lisp
;   ORDER            the file names, in load order
;   REPORT           what was kept, dropped and rewritten (also printed)
;
; Every top-level event goes through a CLOSED table (EVENT-RULE): an event
; that is not in it is an error, as `make gen` fails on a raw Lisp error.
; Every rewrite is mechanical and the same for every form; each has its
; reason next to it. Output is deterministic (no hash order, no addresses).

(defpackage "DEMO-EXTRACT" (:use "COMMON-LISP"))
(in-package "DEMO-EXTRACT")

;; ------------------------------------------------------------------ state
(defvar *report* nil)           ; alist (key . count), see BUMP
(defvar *defined* nil)          ; function names defined by the output
(defvar *called* nil)           ; (symbol . count) in call position
(defvar *trmc-done* nil)        ; self-recursive defuns rewritten into loops
(defvar *trmc-left* nil)        ; self-recursive defuns left recursive (reason)

(defun bump (key &optional (n 1))
  (let ((c (assoc key *report* :test #'equal)))
    (if c (incf (cdr c) n) (push (cons key n) *report*))))

(defun sym= (x name) (and (symbolp x) (string= (symbol-name x) name)))
(defun head (form) (and (consp form) (symbolp (car form)) (symbol-name (car form))))
(defun proper-p (x) (null (cdr (last x))))

;; ------------------------------------------------------- symbol printing
;; JSCL's CL lacks bignums and ratios and recurses on cdr in EQUAL and
;; APPEND (W0, W1). These CL functions are printed as ACL2::<name>, which
;; the shim (demo/shim) defines on the D5 number tower and as loops. The
; list is closed: W2's report lists every CL function the output calls.
(defparameter +shadowed+
  '("*" "+" "-" "/" "1+" "1-" "<" "<=" ">" ">=" "=" "/="
    "ASH" "CEILING" "DENOMINATOR" "EVENP" "ODDP" "EXPT" "FLOOR" "INTEGER-LENGTH"
    "INTEGERP" "RATIONALP" "NUMBERP" "LOGAND" "LOGBITP" "LOGCOUNT" "LOGIOR"
    "LOGNOT" "LOGXOR" "MAX" "MIN" "MOD" "NUMERATOR" "REM" "TRUNCATE" "ROUND"
    "ABS" "ZEROP" "PLUSP" "MINUSP" "SIGNUM"
    "EQUAL" "APPEND" "REVERSE"))

(defun printed-package (s)
  (let ((p (package-name (symbol-package s))))
    (if (and (string= p "COMMON-LISP") (member (symbol-name s) +shadowed+ :test #'string=))
        "ACL2"
        p)))

(defun pname (s o)
  (write-char #\| o)
  (loop for c across s do (when (member c '(#\| #\\)) (write-char #\\ o)) (write-char c o))
  (write-char #\| o))

(defun emit (x o)
  (cond ((null x) (write-string "|COMMON-LISP|::|NIL|" o))
        ((eq x t) (write-string "|COMMON-LISP|::|T|" o))
        ((keywordp x) (write-string ":" o) (pname (symbol-name x) o))
        ((symbolp x)
         (when (null (symbol-package x)) (error "uninterned symbol ~S" x))
         (pname (printed-package x) o) (write-string "::" o) (pname (symbol-name x) o))
        ((integerp x)
         (when (> (abs x) (1- (expt 2 53))) (error "unrewritten integer literal ~D" x))
         (format o "~D" x))
        ((rationalp x) (error "unrewritten ratio literal ~S" x))
        ((stringp x) (write-char #\" o)
         (loop for c across x do (when (member c '(#\" #\\)) (write-char #\\ o)) (write-char c o))
         (write-char #\" o))
        ((characterp x)
         (if (and (graphic-char-p x) (char/= x #\Space)) (format o "#\\~A" x)
             (format o "(|COMMON-LISP|::|CODE-CHAR| ~D)" (char-code x))))
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

;; ------------------------------------------------------ literal rewrite
;; JSCL reads 1/2 as a SYMBOL, silently (W0 item 2), and has no integers
;; beyond 2^53. A ratio literal becomes (ACL2::%Q n d), an integer literal
;; beyond 2^53 - 1 becomes (ACL2::%BIG "digits"): shim constructors on the
;; D5 tower. Inside quoted data such literals would need a data rewrite;
; there are none, and one would be an error.
(defun quoted-number-check (x)
  (cond ((and (rationalp x) (or (not (integerp x)) (> (abs x) (1- (expt 2 53)))))
         (error "number literal ~S inside quoted data" x))
        ((consp x) (quoted-number-check (car x)) (quoted-number-check (cdr x)))))

(defun rewrite-literals (x)
  (cond ((and (integerp x) (> (abs x) (1- (expt 2 53))))
         (bump "literal: integer beyond 2^53 -> (ACL2::%BIG ...)")
         (list (intern "%BIG" "ACL2") (format nil "~D" x)))
        ((and (rationalp x) (not (integerp x)))
         (bump "literal: ratio -> (ACL2::%Q n d)")
         (list (intern "%Q" "ACL2") (numerator x) (denominator x)))
        ((atom x) x)
        ((eq (car x) 'quote) (quoted-number-check (cdr x)) x)
        (t (cons (rewrite-literals (car x)) (rewrite-literals (cdr x))))))

;; ------------------------------------------------ clause-chain flattening
;; W0 item 3, W2 item 7. The translator compiles the clauses of a relation
;; or grammar into
;;   (LET ((%R X1)) (DECLARE (IGNORABLE %R)) (IF %R (CAR %R) <rest>))   or
;;   (LET ((%R X1)) (DECLARE (IGNORABLE %R)) (IF %R %R <rest>))
;; with <rest> the next link, so n clauses nest n deep (the decoder: 1,010),
; deeper than the JS parsers of node, Chromium and Firefox accept. Each Xi
;; is NIL or a non-NIL result. A chain of one shape with at least 3 links
;; becomes one flat sequence:
;;   (LET ((WRT::%CHAIN X1)) (IF WRT::%CHAIN NIL (SETQ WRT::%CHAIN X2)) ...
;;        (IF WRT::%CHAIN (CAR WRT::%CHAIN) <final rest>))
;; Same values, same order of evaluation. In the nested form Xi+1 sits
;; inside the previous %R binding (then NIL); the chain stops at the first
;; Xi that mentions %R, so no Xi sees a different %R.
(defun occurs (s x) (if (consp x) (or (occurs s (car x)) (occurs s (cdr x))) (eq s x)))

(defun chain-link (x)
  "(values Xi rest %R kind) if X is one link, else NIL."
  (if (and (consp x) (sym= (car x) "LET") (proper-p x) (= (length x) 4)
           (consp (second x)) (null (cdr (second x))) (consp (first (second x)))
           (proper-p (first (second x))) (= (length (first (second x))) 2)
           (sym= (first (first (second x))) "%R")
           (let ((d (third x))) (and (consp d) (sym= (car d) "DECLARE")))
           (let ((i (fourth x)) (r (first (first (second x)))))
             (and (consp i) (eq (car i) 'if) (proper-p i) (= (length i) 4)
                  (eq (second i) r)
                  (or (equal (third i) (list 'car r)) (eq (third i) r)))))
      (values (second (first (second x))) (fourth (fourth x)) (first (first (second x)))
              (if (consp (third (fourth x))) :car :self))
      nil))

(defun flatten (x)
  (if (atom x) x
      (multiple-value-bind (x1 rest r kind) (chain-link x)
        (if (null r)
            (if (eq (car x) 'quote) x (cons (flatten (car x)) (flatten (cdr x))))
            (let ((xs (list x1)))
              (loop (multiple-value-bind (xi rest2 r2 kind2) (chain-link rest)
                      (if (and r2 (eq r2 r) (eq kind2 kind) (not (occurs r xi)))
                          (progn (push xi xs) (setq rest rest2))
                          (return))))
              (if (< (length xs) 3)
                  (cons (flatten (car x)) (flatten (cdr x)))
                  (let ((c (intern "%CHAIN" "WRT")))
                    (bump "rewrite: clause chain flattened")
                    (bump "rewrite: clause chain links" (length xs))
                    (setq xs (nreverse xs))
                    `(let ((,c ,(flatten (car xs))))
                       ,@(mapcar (lambda (xi) `(if ,c nil (setq ,c ,(flatten xi)))) (cdr xs))
                       (if ,c ,(if (eq kind :car) `(car ,c) c) ,(flatten rest))))))))))

;; ----------------------------------------------- stack rewrite (W1 (b))
;; W0 item 4, W1, W2 item 6. A self-recursive defun F whose every call of
;; F is in tail position, or is the last argument of a CONS in tail
;; position, runs as a loop: the formals are reassigned (PSETQ) and the
;; CONS heads are collected, then put back in front of the final value with
;; REVAPPEND. Tail positions are followed through IF, LET, LET*, PROGN,
;; AND (last argument: (AND a b) = (IF a b NIL)) and COND clauses. Same
;; values, evaluated in the same order (a head before the new arguments).
;; A tail-position (LET ((v (F args))) post) (the call bound, then used)
;; pushes a continuation instead (see K-BINDING-P); the loop's value is
;; passed through them at the end.
;; Not rewritten: mutual recursion, a call of F anywhere else, a LET that
;; rebinds a formal of F on the way to a tail call (PSETQ would assign the
;; inner binding), &-keywords in the lambda list. The report lists them.
;; JSCL compiles DO without RETURN to a plain JS while loop (no exceptions).
(define-condition not-trmc (error) ((why :initarg :why :reader why)))
(defun give-up (why) (error 'not-trmc :why why))

(defun self-call-p (x f) (and (consp x) (eq (car x) f)))

;; A function that may return multiple values (*MV-FNS*) keeps all of them:
;; its leaves store (MULTIPLE-VALUE-LIST x) and the loop returns
;; (VALUES-LIST ...). Such a function may not collect CONS heads.
(defvar *tail-mv* nil)
(defun leaf (x val done)
  (if *tail-mv* `(setq ,val (multiple-value-list ,x) ,done t) `(setq ,val ,x ,done t)))

;; Continuations (W4: GRAM/BINSTR/REPn, the vector helpers of the decoder,
;; recurse once per element and overflow node's stack on br_table.0.wasm):
;; *TAIL-K* is set when TAIL-XFORM pushed one, *K-VAR* holds them. A
;; function may use continuations or CONS heads, not both (their order
;; would interleave).
(defvar *tail-k* nil)
(defvar *tail-acc* nil)
(defvar *k-var* nil)
(defun k-binding-p (x f)
  ;; X = (LET ((v B)) body...) or (LET* (b... (v B)) body...), F in B (which
  ;; is then rewritten in tail position), not in the other bindings or the body
  (let* ((binds (second x)) (body (cddr x)) (kb (car (last binds))))
    (and (consp binds) (consp kb) (symbolp (car kb)) (= (length kb) 2)
         (or (null (cdr binds)) (eq (car x) 'let*))
         (occurs f (second kb))
         (notany (lambda (b) (occurs f b)) (butlast binds))
         (notany (lambda (b) (occurs f b)) body))))

;; (g a1 ... an), G a function (not a macro or special operator in this
;; image; ACL2's
;; arithmetic macros count as functions: the shim's expansions evaluate
;; every argument), exactly one ai containing F. The other arguments are
;; then evaluated after the call (in the continuation): the code is pure,
;; but WRT::%RULE (W7 tags, the W8 recorder) must keep its order, so they
;; may not contain it.
(defparameter +strict-macros+ '("+" "*" "-" "/" "1+" "1-" "<" ">" "<=" ">=" "=" "/=" "APPEND" "LOGAND" "LOGIOR" "LOGXOR"))
(defun k-call-arg (x f)
  ;; -> index of the argument containing F, or NIL
  (let ((h (car x)))
    (when (and (symbolp h) (not (eq h f))
               ;; the books are not loaded here (only their packages): a
               ;; symbol without a macro definition is a function
               (or (and (not (macro-function h)) (not (special-operator-p h)))
                   (and (eq (symbol-package h) (find-package "ACL2"))
                        (member (symbol-name h) +strict-macros+ :test #'string=))))
      (let ((ks (loop for a in (cdr x) for k from 0 when (occurs f a) collect k)))
        (when (and (= (length ks) 1)
                   (notany (lambda (a) (occurs (intern "%RULE" "WRT") a))
                           (remove (nth (car ks) (cdr x)) (cdr x) :count 1 :test #'eq)))
          (car ks))))))

(defun push-k (var post-forms formals)
  ;; push (LAMBDA (var) post...) closed over the formals' current values
  `(setq ,*k-var* (cons (let ,(mapcar (lambda (v) (list v v)) formals)
                          (declare (ignorable ,@formals))
                          (lambda (,var) ,@post-forms))
                        ,*k-var*)))

;; Clause chains (W4, br_table: $SHIFT_LABELIDXS, $FREE_LIST, ...): F is
;; called inside a clause Xi of a chain, flat (FLATTEN: (LET ((%CHAIN X1))
;; (IF %CHAIN NIL (SETQ %CHAIN Xi))... (IF %CHAIN (CAR %CHAIN) final)) or
;; nested (CHAIN-LINK: (LET ((%R X1)) (DECLARE ...) (IF %R (CAR %R) final))).
;; A clause is a path through IF/AND/LET/LET* to a success value (LIST e),
;; never NIL, so a clause that reaches a success value containing F has
;; won the chain: it sets a commit flag and continues with e (kind :car,
;; the chain returns (CAR (LIST e)) = e) or with (LIST e) (kind :self) in
;; tail position. A clause path without F sets the chain variable to its
;; value as before. Every other shape gives up.
(defvar *commit-count* 0)
(defvar *tail-chain* nil)               ; set when CHAIN-XFORM was used
(defun chain-form (x f)
  ;; -> (values var clauses kind final) when some clause of the chain X calls F
  (multiple-value-bind (x1 rest r kind) (chain-link x)
    (if r
        (when (occurs f x1) (values r (list x1) kind rest))
      (when (and (consp x) (eq (car x) 'let) (proper-p x) (>= (length x) 4)
                 (consp (second x)) (null (cdr (second x))) (consp (car (second x)))
                 (sym= (car (car (second x))) "%CHAIN"))
        (let* ((c (car (car (second x)))) (links (butlast (cddr x))) (fin (car (last x))))
          (when (and (every (lambda (l) (and (consp l) (eq (car l) 'if) (eq (second l) c) (null (third l))
                                             (consp (fourth l)) (eq (car (fourth l)) 'setq) (eq (second (fourth l)) c)))
                            links)
                     (consp fin) (eq (car fin) 'if) (eq (second fin) c))
            (let ((clauses (cons (second (car (second x))) (mapcar (lambda (l) (third (fourth l))) links))))
              (when (some (lambda (xi) (occurs f xi)) clauses)
                (values c clauses (if (consp (third fin)) :car :self) (fourth fin))))))))))

(defun clause-xform (x f formals acc done val c commit kind)
  (labels ((cx (x) (clause-xform x f formals acc done val c commit kind)))
    (cond
      ((not (occurs f x)) `(setq ,c ,x))
      ((atom x) (give-up "atom?"))
      ((and (eq (car x) 'list) (= (length x) 2))
       `(progn (setq ,commit t)
               ,(tail-xform (if (eq kind :car) (second x) x) f formals acc done val)))
      ((eq (car x) 'if)
       (when (occurs f (second x)) (give-up "call in a test"))
       `(if ,(second x) ,(cx (third x)) ,(cx (fourth x))))
      ((eq (car x) 'and)
       (cond ((null (cddr x)) (cx (second x)))
             (t (when (some (lambda (a) (occurs f a)) (butlast (cdr x))) (give-up "call in a non-last AND argument"))
                `(if (and ,@(butlast (cdr x))) ,(cx (car (last x))) (setq ,c nil)))))
      ((member (car x) '(let let*))
       (let* ((binds (second x)) (body (cddr x))
              (decls (loop while (and (consp (car body)) (eq (caar body) 'declare)) collect (pop body)))
              (names (mapcar (lambda (b) (if (consp b) (car b) b)) binds)))
         (when (some (lambda (b) (occurs f (if (consp b) (second b) nil))) binds) (give-up "call in a binding"))
         (when (some (lambda (v) (or (member v formals) (eq v c) (eq v commit))) names) (give-up "LET rebinds a formal"))
         (when (some (lambda (a) (occurs f a)) (butlast body)) (give-up "call in a non-last body form"))
         `(,(car x) ,binds ,@decls ,@(butlast body) ,(cx (car (last body))))))
      (t (give-up "call in a clause, not in its success value")))))

(defun chain-xform (x f formals acc done val)
  (multiple-value-bind (c clauses kind final) (chain-form x f)
    (setq *tail-chain* t)
    (let ((commit (intern (format nil "%COMMIT~D" (incf *commit-count*)) "WRT")))
      (flet ((cx (xi) (clause-xform xi f formals acc done val c commit kind)))
        `(let ((,c nil) (,commit nil))
           ,(cx (car clauses))
           ,@(mapcar (lambda (xi) `(if (or ,commit ,c) nil ,(cx xi))) (cdr clauses))
           (if ,commit nil
               (if ,c ,(leaf (if (eq kind :car) `(car ,c) c) val done)
                   ,(tail-xform final f formals acc done val))))))))

(defun tail-xform (x f formals acc done val)
  ;; X in tail position -> a statement that either sets VAL and DONE, or
  ;; reassigns the formals (pushing a CONS head onto ACC first)
  (cond
    ((self-call-p x f)
     (when (some (lambda (a) (occurs f a)) (cdr x)) (give-up "nested call in arguments"))
     (unless (= (length (cdr x)) (length formals)) (give-up "arity"))
     `(psetq ,@(mapcan #'list formals (cdr x))))
    ((and (consp x) (eq (car x) 'cons) (= (length x) 3) (self-call-p (third x) f))
     (when (occurs f (second x)) (give-up "call in a CONS head"))
     (when *tail-mv* (give-up "CONS head in a function that may return multiple values"))
     (setq *tail-acc* t)
     `(progn (setq ,acc (cons ,(second x) ,acc))
             ,(tail-xform (third x) f formals acc done val)))
    ((not (occurs f x)) (leaf x val done))
    ((atom x) (give-up "atom?"))
    ((chain-form x f) (chain-xform x f formals acc done val))
    ((eq (car x) 'if)
     (when (occurs f (second x)) (give-up "call in a test"))
     `(if ,(second x) ,(tail-xform (third x) f formals acc done val)
          ,(tail-xform (fourth x) f formals acc done val)))
    ((eq (car x) 'and)
     (cond ((null (cdr x)) (leaf t val done))
           ((null (cddr x)) (tail-xform (second x) f formals acc done val))
           (t (when (some (lambda (a) (occurs f a)) (butlast (cdr x))) (give-up "call in a non-last AND argument"))
              `(if (and ,@(butlast (cdr x)))
                   ,(tail-xform (car (last x)) f formals acc done val)
                   ,(leaf nil val done)))))
    ((eq (car x) 'cond)
     (when (some (lambda (cl) (occurs f (car cl))) (cdr x)) (give-up "call in a COND test"))
     (when (some (lambda (cl) (null (cdr cl))) (cdr x)) (give-up "COND clause without body"))
     `(cond ,@(mapcar (lambda (cl) (list (car cl) (tail-xform (if (cddr cl) (cons 'progn (cdr cl)) (cadr cl))
                                                              f formals acc done val)))
                      (cdr x))
            (t ,(leaf nil val done))))
    ((eq (car x) 'progn)
     (when (some (lambda (a) (occurs f a)) (butlast (cdr x))) (give-up "call in a non-last PROGN form"))
     `(progn ,@(butlast (cdr x)) ,(tail-xform (car (last x)) f formals acc done val)))
    ((and (member (car x) '(let let*)) (k-binding-p x f))
     ;; continuation (W4, br_table): (LET ((v (F args))) post) in tail
     ;; position, POST not calling F. Push (LAMBDA (v) post), closed over
     ;; the current values of the formals (the loop reassigns them), then
     ;; loop on ARGS; the loop's final value goes through the pushed
     ;; continuations, last pushed first. A LET* is split after its other
     ;; bindings, which keep their order.
     (when *tail-mv* (give-up "continuation in a function that may return multiple values"))
     (when (some (lambda (b) (member (if (consp b) (car b) b) formals)) (butlast (second x)))
       (give-up "LET rebinds a formal"))
     (setq *tail-k* t)
     (let* ((binds (second x)) (body (cddr x)) (kb (car (last binds)))
            (decls (loop while (and (consp (car body)) (eq (caar body) 'declare)) collect (pop body)))
            (step `(progn ,(push-k (car kb) (append decls body) formals)
                          ,(tail-xform (second kb) f formals acc done val))))
       (if (cdr binds) `(let* ,(butlast binds) ,step) step)))
    ((member (car x) '(let let*))
     (let* ((binds (second x)) (body (cddr x))
            (decls (loop while (and (consp (car body)) (eq (caar body) 'declare)) collect (pop body))))
       (when (some (lambda (b) (occurs f (if (consp b) (second b) nil))) binds) (give-up "call in a binding"))
       (when (some (lambda (b) (member (if (consp b) (car b) b) formals)) binds) (give-up "LET rebinds a formal"))
       (when (some (lambda (a) (occurs f a)) (butlast body)) (give-up "call in a non-last body form"))
       `(,(car x) ,binds ,@decls ,@(butlast body) ,(tail-xform (car (last body)) f formals acc done val))))
    ((k-call-arg x f)
     (when *tail-mv* (give-up "continuation in a function that may return multiple values"))
     (setq *tail-k* t)
     (let* ((k (k-call-arg x f)) (v (intern "%KV" "WRT"))
            (post (append (subseq x 0 (1+ k)) (list v) (nthcdr (+ k 2) x))))
       `(progn ,(push-k v (list post) formals)
               ,(tail-xform (nth (1+ k) x) f formals acc done val))))
    (t (give-up (format nil "call under ~A" (car x))))))

(defun defun-parts (d)
  ;; (defun name formals decl* body...) -> (values name formals decls body-forms)
  (let* ((name (second d)) (formals (third d)) (rest (cdddr d))
         (decls (loop while (and (consp (car rest)) (sym= (caar rest) "DECLARE")) collect (pop rest))))
    (values name formals decls rest)))

(defvar *stack-rewrite* t)              ; NIL only to bisect a bug
(defun trmc-rewrite (d)
  (multiple-value-bind (f formals decls body) (defun-parts d)
    (if (or (not *stack-rewrite*) (not (occurs f body)))
        d
      (let ((*tail-mv* (and (member f *mv-fns*) t)) (*tail-k* nil) (*tail-acc* nil) (*tail-chain* nil)
            (*k-var* (intern "%K" "WRT")))
        (handler-case
            (progn
              (when (some (lambda (a) (member a lambda-list-keywords)) formals) (give-up "lambda keywords"))
              (when (cdr body) (give-up "several body forms"))
              (let* ((acc (intern "%ACC" "WRT")) (done (intern "%DONE" "WRT")) (val (intern "%VAL" "WRT"))
                     (step (tail-xform (car body) f formals acc done val)))
                (when (and *tail-k* *tail-acc*) (give-up "continuations and CONS heads"))
                (push f *trmc-done*)
                (bump "rewrite: self-recursive defun -> loop")
                (when *tail-mv* (bump "rewrite: ... of which keep multiple values"))
                (when *tail-k* (bump "rewrite: ... of which with continuations"))
                (when *tail-chain* (bump "rewrite: ... of which through a clause chain"))
                (if *tail-k*
                    `(defun ,f ,formals ,@decls
                       (let ((,*k-var* nil) (,done nil) (,val nil))
                         (do () (,done (progn (do () ((null ,*k-var*))
                                                (setq ,val (funcall (car ,*k-var*) ,val) ,*k-var* (cdr ,*k-var*)))
                                              ,val))
                           ,step)))
                  `(defun ,f ,formals ,@decls
                     (let ((,acc nil) (,done nil) (,val nil))
                       (do () (,done ,(if *tail-mv* `(values-list ,val) `(revappend ,acc ,val))) ,step))))))
          (not-trmc (c) (push (cons f (why c)) *trmc-left*) d))))))

;; ---------------------------------------------------------------- defuns
(defun strip-xargs (decls)
  ;; (declare (xargs ...)) is ACL2's (measure, guard, mode); JSCL ignores it,
  ;; but the measures mention prover-only functions: dropped.
  (loop for d in decls
        for kept = (remove-if (lambda (s) (and (consp s) (sym= (car s) "XARGS"))) (cdr d))
        when kept collect (cons (car d) kept)))

(defun clean-defun (d)
  (unless (and (proper-p d) (>= (length d) 4) (symbolp (second d)) (listp (third d)))
    (error "malformed defun ~S" (second d)))
  (multiple-value-bind (name formals decls body) (defun-parts d)
    (push name *defined*)
    (let* ((body (rewrite-literals body))
           (body (mapcar #'flatten body)))
      `(defun ,name ,formals ,@(strip-xargs decls) ,@body))))

;; ---------------------------------------------------------- event table
;; (EVENT-RULE form) -> list of output forms. Closed: anything else errors.
(defparameter +event-macros+ '("%TRY-LOGIC" "%TRY-GUARDS" "%TRY-LOGIC-T" "%TRY-GUARDS-T" "%RULE"))

(defun event-rule (form)
  (let ((h (head form)))
    (bump (format nil "event: ~A" h))
    (cond
      ;; symbols are printed package-qualified: no package state needed
      ((member h '("IN-PACKAGE") :test #'equal) nil)
      ;; followed by WALK (included books come first), then dropped
      ((equal h "INCLUDE-BOOK") nil)
      ;; prover settings and proof-only events
      ((member h '("SET-VERIFY-GUARDS-EAGERNESS" "SET-BOGUS-MUTUAL-RECURSION-OK" "PROGRAM"
                   "SET-STATE-OK" "DEFTHM" "IN-THEORY" "VERIFY-GUARDS" "VALUE-TRIPLE" "TABLE"
                   "LOCAL")
               :test #'equal)
       (bump (format nil "dropped: ~A" h)) nil)
      ;; guard verification only
      ((equal h "%TRY-GUARDS-T") (bump "dropped: %TRY-GUARDS-T") nil)
      ;; every alternative of the make-event admits the same definition
      ;; (logic or program mode): keep the definition
      ((equal h "%TRY-LOGIC-T") (event-rule (third form)))
      ((equal h "DEFUN") (list (clean-defun form)))
      ((equal h "MUTUAL-RECURSION")
       (list (cons 'progn (mapcar (lambda (d)
                                    (unless (equal (head d) "DEFUN") (error "mutual-recursion member ~S" (head d)))
                                    (clean-defun d))
                                  (cdr form)))))
      ;; the rt/ macros that build ACL2 events, and %RULE (W7), which the
      ;; shim defines as a recorder (W8): their definitions are dropped
      ((equal h "DEFMACRO")
       (unless (member (symbol-name (second form)) +event-macros+ :test #'string=)
         (error "unknown defmacro ~S" (second form)))
       (bump (format nil "dropped: DEFMACRO ~A" (second form))) nil)
      ;; the signature of the host-call hook; the shim defines the hook
      ((equal h "ENCAPSULATE")
       (unless (equal (car (car (car (second form)))) (intern "%HOSTCALL-HOOK" "WRT"))
         (error "unknown encapsulate ~S" (second form)))
       (bump "dropped: ENCAPSULATE %HOSTCALL-HOOK") nil)
      ;; (defattach f g) -> the shim's %DEFATTACH: F calls G until the
      ;; driver attaches its own function
      ((equal h "DEFATTACH")
       (list `(,(intern "%DEFATTACH" "ACL2") ',(second form) ',(third form))))
      ;; memoization is semantically the identity; the shim's %MEMOIZE
      ;; caches on EQUAL arguments (performance, as in ACL2)
      ((equal h "MEMOIZE")
       (list `(,(intern "%MEMOIZE" "ACL2") ,(second form))))
      ;; driver constants (named extraction only)
      ((equal h "DEFCONST")
       (push (second form) *defined*)
       (list `(defparameter ,(second form) ,(rewrite-literals (third form)))))
      (t (error "demo/extract: unknown event ~A (add it to EVENT-RULE with its reason)" h)))))

;; --------------------------------------------------------------- reading
(defun read-book (path)
  (with-open-file (in path)
    (let ((*package* (find-package "ACL2")) (forms nil) (eof (list :eof)))
      (loop for f = (read in nil eof)
            until (eq f eof)
            do (when (equal (head f) "IN-PACKAGE")
                 (setq *package* (find-package (second f))))
               (push f forms))
      (nreverse forms))))

(defun book-path (dir name) (merge-pathnames (concatenate 'string name ".lisp") dir))

(defun include-chain (root)
  ;; books in load order: depth first, an included book before its includer
  (let ((seen nil) (order nil))
    (labels ((walk (path)
               (let ((path (truename path)))
                 (unless (member path seen :test #'equal)
                   (push path seen)
                   (dolist (f (read-book path))
                     (when (equal (head f) "INCLUDE-BOOK")
                       (walk (book-path (make-pathname :name nil :type nil :defaults path) (second f)))))
                   (push path order)))))
      (walk root))
    (nreverse order)))

;; ------------------------------------------------------------ analysis
(defun note-calls (x)
  ;; symbols in call position (outside quote), for the report
  (when (consp x)
    (cond ((eq (car x) (quote quote)))
          ((eq (car x) (quote cond))
           (dolist (cl (cdr x)) (mapc #'note-calls cl)))
          ((eq (car x) (quote do))
           (mapc (function note-calls) (cdr (third x))) (mapc (function note-calls) (cdddr x)))
          ((sym= (car x) "MV-LET")
           (note-calls (third x)) (mapc #'note-calls (cdddr x)))
          ((eq (car x) (quote case))
           (note-calls (second x))
           (dolist (cl (cddr x)) (mapc #'note-calls (cdr cl))))
          ;; (LAMBDA (vars) body...): the lambda list is not a call (the
          ;; continuations of the stack rewrite)
          ((eq (car x) (quote lambda))
           (mapc #'note-calls (cddr x)))
          ((and (symbolp (car x)) (not (member (car x) '(let let*))))
           (let ((c (assoc (car x) *called*))) (if c (incf (cdr c)) (push (cons (car x) 1) *called*)))
           (mapc #'note-calls (cdr x)))
          ((member (car x) '(let let*))
           (dolist (b (second x)) (when (consp b) (note-calls (second b))))
           (mapc #'note-calls (cddr x)))
          (t (mapc #'note-calls x)))))

(defun note-defun-calls (d)
  (if (eq (car d) 'progn) (mapc #'note-defun-calls (cdr d))
      (when (eq (car d) 'defun) (mapc #'note-calls (cdddr d)))))

;; Functions that can return multiple values (ACL2 MV): the loop of the
;; rewrite keeps one value, so they are never rewritten. A function is in
;; the set if its body mentions ACL2::MV, or calls a function of the set
;; (fixpoint over all output defuns; an over-approximation, which only
;; leaves more functions recursive). Only rt/ and the driver use MV.
(defvar *mv-fns* nil)
(defun all-defuns (forms)
  (mapcan (lambda (f) (cond ((eq (car f) 'defun) (list f))
                            ((eq (car f) 'progn) (remove-if-not (lambda (d) (eq (car d) 'defun)) (copy-list (cdr f))))))
          forms))
(defun compute-mv-fns (defuns)
  (let ((mv (intern "MV" "ACL2")) (set nil) (changed t))
    (loop while changed
          do (setq changed nil)
             (dolist (d defuns)
               (unless (member (second d) set)
                 (when (or (occurs mv (cdddr d)) (some (lambda (g) (occurs g (cdddr d))) set))
                   (push (second d) set) (setq changed t)))))
    set))

(defun stack-rewrite (forms)
  (mapcar (lambda (f)
            (cond ((eq (car f) 'defun) (trmc-rewrite f))
                  ;; mutual recursion is not rewritten (W1 (b) covers self-recursion);
                  ;; members that only call themselves still are
                  ((eq (car f) 'progn) (cons 'progn (mapcar (lambda (d) (if (eq (car d) 'defun) (trmc-rewrite d) d)) (cdr f))))
                  (t f)))
          forms))

;; --------------------------------------------------------------- output
(defun write-forms (path header forms)
  (with-open-file (o path :direction :output :if-exists :supersede)
    (format o ";; GENERATED by demo/extract from ~A. Do not edit.~%" header)
    (dolist (f forms) (emit f o) (terpri o) (terpri o))))

(defun short-name (path)
  (let ((n (namestring path)))
    (subseq n (or (search "translate/" n) 0))))

;; TESTS: list of (out-name book names): the named functions of an ACL2 test
;; book (W3 item 2), written to OUTDIR/tests/out-name, not in ORDER: a test
;; bundle is the semantics plus one of them (two test books may define the
;; same name). DATA: list of (in out): ACL2 test data (.lsp) as JSON.
(defun extract (&key root driver driver-names outdir tests data units)
  (setq *report* nil *defined* nil *called* nil *trmc-done* nil *trmc-left* nil)
  (let* ((books (include-chain root)) (files nil) (k 0)
         (per-book (mapcar (lambda (b) (mapcan #'event-rule (read-book b))) books))
         (driver-forms (and driver (driver-forms driver driver-names)))
         (test-forms (mapcar (lambda (tst) (driver-forms (second tst) (third tst))) tests)))
    (setq *mv-fns* (compute-mv-fns (all-defuns (apply #'append driver-forms (append test-forms per-book)))))
    (when tests (ensure-directories-exist (merge-pathnames "tests/" outdir)))
    (loop for tst in tests for forms in test-forms
          do (let ((out (stack-rewrite forms)))
               (mapc #'note-defun-calls out)
               (bump (format nil "test file ~A: output forms" (first tst)) (length out))
               (write-forms (merge-pathnames (concatenate 'string "tests/" (first tst)) outdir)
                            (short-name (second tst)) out)))
    (when units (write-units units outdir))
    (dolist (d data)
      (lsp->json (first d) (merge-pathnames (second d) outdir))
      (bump (format nil "data ~A -> ~A" (short-name (first d)) (second d))))
    (dolist (b books)
      (let* ((forms (stack-rewrite (pop per-book)))
             (name (format nil "~2,'0D-~A.lisp" (incf k) (pathname-name b))))
        (mapc #'note-defun-calls forms)
        (bump (format nil "book ~A: output forms" (pathname-name b)) (length forms))
        (write-forms (merge-pathnames name outdir) (short-name b) forms)
        (push name files)))
    ;; W2 item 4: named extraction of the pure driver helpers
    (when driver
      (let* ((out (stack-rewrite driver-forms)))
        (mapc #'note-defun-calls out)
        (write-forms (merge-pathnames "driver.lisp" outdir) (short-name driver) out)
        (push "driver.lisp" files)))
    (with-open-file (o (merge-pathnames "ORDER" outdir) :direction :output :if-exists :supersede)
      (dolist (f (reverse files)) (write-line f o)))
    (write-report (merge-pathnames "REPORT" outdir))))

;; W2 item 4: the named pure helpers of the ACL2 conformance driver, through
;; the same event table. An unknown name is an error.
(defun driver-forms (driver driver-names)
  (let* ((all (read-book driver))
         (names-of (lambda (f)
                     (cond ((member (head f) '("DEFUN" "DEFCONST") :test #'equal)
                            (list (symbol-name (second f))))
                           ((equal (head f) "MUTUAL-RECURSION")
                            (mapcar (lambda (d) (symbol-name (second d))) (cdr f))))))
         ;; a name in a mutual-recursion brings the whole clique, once
         (by-name (lambda (n) (find-if (lambda (f) (member n (funcall names-of f) :test #'string-equal)) all)))
         (forms (remove-duplicates
                 (mapcar (lambda (n) (or (funcall by-name n)
                                         (error "demo/extract: no defun or defconst ~A in ~A" n driver)))
                         driver-names)
                 :from-end t)))
    (mapcan #'event-rule forms)))

;; ACL2 test data (one object per file, read with the ACL2 reader) as JSON,
;; for the node runners (W3 item 2): a list is an array; an integer a JSON
;; number when |n| <= 2^53 - 1, else {"big": "digits"}; a string a string;
;; a symbol {"sym": name, "pkg": package}.
(defun json-out (x o)
  (cond ((null x) (write-string "[]" o))
        ((integerp x) (if (<= (abs x) (1- (expt 2 53))) (format o "~D" x) (format o "{\"big\":\"~D\"}" x)))
        ((rationalp x) (format o "{\"q\":[\"~D\",\"~D\"]}" (numerator x) (denominator x)))
        ((stringp x) (write-char #\" o)
         (loop for c across x
               do (cond ((member c '(#\" #\\)) (write-char #\\ o) (write-char c o))
                        ((< (char-code c) 32) (format o "\\u~4,'0X" (char-code c)))
                        (t (write-char c o))))
         (write-char #\" o))
        ((symbolp x) (format o "{\"sym\":\"~A\",\"pkg\":\"~A\"}" (symbol-name x) (printed-package x)))
        ((consp x)
         (if (proper-p x)
             (progn (write-char #\[ o)
                    (loop for (e . more) on x do (json-out e o) (when more (write-char #\, o)))
                    (write-char #\] o))
             ;; improper list: {"dot": [e1, ..., en, tail]}
             (progn (write-string "{\"dot\":[" o)
                    (loop for tail on x do (json-out (car tail) o) (write-char #\, o)
                          finally (json-out (cdr (last x)) o))
                    (write-string "]}" o))))
        (t (error "test data value ~S" x))))

;; W3 item 3: shim unit tests. UNITS is a file holding a list of forms: ACL2
;; evaluates each (raw Lisp, primary value) into tests/units-expected.json,
;; and tests/units.lisp defines DEMO::UNIT-RESULTS, the list of the same
;; forms for JSCL (printed like the semantics: the shim's functions).
(defun write-units (units outdir)
  (let ((forms (with-open-file (s units) (let ((*package* (find-package "ACL2"))) (read s)))))
    (with-open-file (o (merge-pathnames "tests/units-expected.json" outdir) :direction :output :if-exists :supersede)
      (json-out (mapcar (lambda (f) (car (multiple-value-list (eval f)))) forms) o))
    (write-forms (merge-pathnames "tests/units.lisp" outdir) "demo/test/units.lsp"
                 (list `(defun ,(intern "UNIT-RESULTS" (or (find-package "DEMO") (make-package "DEMO" :use nil))) () (list ,@(mapcar #'rewrite-literals forms)))))
    (bump "test file units.lisp: forms" (length forms))))

(defun lsp->json (in out)
  (let ((obj (with-open-file (s in) (let ((*package* (find-package "ACL2"))) (read s)))))
    (with-open-file (o out :direction :output :if-exists :supersede)
      (if (consp obj)                      ; one element per line
          (progn (write-line "[" o)
                 (loop for (e . more) on obj do (json-out e o) (when more (write-char #\, o)) (terpri o))
                 (write-line "]" o))
          (json-out obj o)))))

(defun sorted-report ()
  (sort (copy-list *report*) #'string< :key #'car))

(defun write-report (path)
  (let* ((undefined (remove-if (lambda (c) (member (car c) *defined*)) *called*))
         (by-pkg (lambda (pkg) (sort (mapcar (lambda (c) (symbol-name (car c)))
                                             (remove-if-not (lambda (c) (string= (printed-package (car c)) pkg)) undefined))
                                     #'string<))))
    (with-open-file (o path :direction :output :if-exists :supersede)
      (let ((out (make-broadcast-stream o *standard-output*)))
        (format out "~&DEMO-EXTRACT report~%")
        (dolist (c (sorted-report)) (format out "  ~7D  ~A~%" (cdr c) (car c)))
        (format out "functions defined: ~D~%" (length (remove-duplicates *defined*)))
        (format out "called, not defined here, package ACL2 (the shim provides them): ~D~%  ~{~A~^ ~}~%"
                (length (funcall by-pkg "ACL2")) (funcall by-pkg "ACL2"))
        (format out "called, not defined here, package COMMON-LISP (JSCL provides them): ~D~%  ~{~A~^ ~}~%"
                (length (funcall by-pkg "COMMON-LISP")) (funcall by-pkg "COMMON-LISP"))
        (let ((other (remove-if (lambda (c) (member (printed-package (car c)) '("ACL2" "COMMON-LISP") :test #'string=)) undefined)))
          (format out "called, not defined anywhere else: ~D~%  ~{~A~^ ~}~%" (length other)
                  (sort (mapcar (lambda (c) (format nil "~A::~A" (printed-package (car c)) (car c))) other) #'string<)))
        (format out "self-recursive defuns rewritten into loops: ~D~%  ~{~A~^ ~}~%" (length *trmc-done*)
                (sort (mapcar #'symbol-name *trmc-done*) #'string<))
        (format out "self-recursive defuns left recursive: ~D~%~{  ~A~%~}" (length *trmc-left*)
                (sort (mapcar (lambda (c) (format nil "~A: ~A" (car c) (cdr c))) *trmc-left*) #'string<))))))
