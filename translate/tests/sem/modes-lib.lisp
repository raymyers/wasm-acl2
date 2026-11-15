; Mode manifest support (wasm3 prep P2, W8): the defun-mode of every
; generated function after certification. %TRY-LOGIC silently falls back to
; :program mode and %TRY-GUARDS to unverified guards, so a regression is
; invisible without a recorded table. gen/wasm-1.0/modes.lsp is that table;
; t0-modes.lisp fails when the certified modes differ from it, and
; `make modes` rewrites it (modes-write.lsp).
;
; Package ACL2; generated forms are read with the generated package current
; (W1T), so their heads are matched by symbol name.
;
; Classes: :GUARDS (logic, guards verified), :LOGIC (logic, guards not
; verified), :PROGRAM.
(in-package "ACL2")
(program)
(set-state-ok t)

(defun %modes-read-loop (channel acc state)
  (mv-let (eofp obj state) (read-object channel state)
    (if eofp (mv (reverse acc) state)
      (%modes-read-loop channel (cons obj acc) state))))

(defun %modes-read-file (file state)
  (mv-let (channel state) (open-input-channel file :object state)
    (if (null channel)
        (mv (er hard? '%modes-read-file "Cannot read ~s0" file) state)
      (mv-let (forms state) (%modes-read-loop channel nil state)
        (let ((state (close-input-channel channel state)))
          (mv forms state))))))

(defun %modes-include (forms)
  ;; the book named by the last include-book among forms
  (cond ((endp forms) nil)
        ((and (consp (car forms)) (symbolp (car (car forms))) (equal (symbol-name (car (car forms))) "INCLUDE-BOOK")
              (null (%modes-include (cdr forms))))
         (cadr (car forms)))
        (t (%modes-include (cdr forms)))))

(mutual-recursion
(defun %modes-defun-names (x acc)
  ;; names of the defuns in a generated event (inside %TRY-LOGIC, %TRY-LOGIC-T, MUTUAL-RECURSION)
  (cond ((atom x) acc)
        ((and (symbolp (car x)) (equal (symbol-name (car x)) "DEFUN") (consp (cdr x)) (symbolp (cadr x)))
         (if (member-eq (cadr x) acc) acc (cons (cadr x) acc)))
        ((and (symbolp (car x)) (member-equal (symbol-name (car x)) '("%TRY-LOGIC" "%TRY-LOGIC-T" "MUTUAL-RECURSION")))
         (%modes-defun-names-list (cdr x) acc))
        (t acc)))

(defun %modes-defun-names-list (l acc)
  (if (atom l) acc (%modes-defun-names-list (cdr l) (%modes-defun-names (car l) acc))))
)

(defun %modes-class (name wrld)
  (case (getpropc name 'symbol-class nil wrld)
    (:common-lisp-compliant :guards)
    (:ideal :logic)
    (otherwise :program)))

(defun %modes-classes (names wrld)
  (if (endp names) nil
    (cons (cons (car names) (%modes-class (car names) wrld))
          (%modes-classes (cdr names) wrld))))

; Walk the part chain back from the top book; (mv parts state) with parts
; = (("part" (name . class) ...) ...) in IL order.
(defun %modes-parts (dir book acc state)
  (if (or (null book) (not (stringp book)) (search "/" book))
      (mv acc state)                    ; reached ../../rt/builtins
    (mv-let (forms state) (%modes-read-file (concatenate 'string dir book ".lisp") state)
      (%modes-parts dir (%modes-include forms)
                    (cons (cons book (%modes-classes (reverse (%modes-defun-names-list forms nil))
                                                     (w state)))
                          acc)
                    state))))

; The manifest of the generated book dir/top: (mv parts state). The top book
; itself holds no events, so it is not listed.
(defun %modes-manifest (dir top state)
  (mv-let (forms state) (%modes-read-file (concatenate 'string dir top ".lisp") state)
    (%modes-parts dir (%modes-include forms) nil state)))

(defun %modes-of-class (entries class)
  (cond ((endp entries) nil)
        ((eq (cdr (car entries)) class) (cons (car entries) (%modes-of-class (cdr entries) class)))
        (t (%modes-of-class (cdr entries) class))))

(defun %modes-count (parts class)
  (cond ((endp parts) 0)
        (t (+ (len (%modes-of-class (cdr (car parts)) class)) (%modes-count (cdr parts) class)))))

(defun %modes-flat (parts)
  (if (endp parts) nil (append (cdr (car parts)) (%modes-flat (cdr parts)))))

(defun %modes-diff-1 (expected actual)
  (cond ((endp expected) nil)
        (t (let ((a (assoc-eq (car (car expected)) actual)))
             (if (and a (eq (cdr a) (cdr (car expected))))
                 (%modes-diff-1 (cdr expected) actual)
               (cons (list (car (car expected)) (cdr (car expected)) (and a (cdr a)))
                     (%modes-diff-1 (cdr expected) actual)))))))

(defun %modes-missing (actual expected)
  (cond ((endp actual) nil)
        ((assoc-eq (car (car actual)) expected) (%modes-missing (cdr actual) expected))
        (t (cons (list (car (car actual)) nil (cdr (car actual)))
                 (%modes-missing (cdr actual) expected)))))

(defun %modes-diff (expected actual)
  ;; ((name expected actual) ...) for names whose class differs or that
  ;; appear on only one side
  (append (%modes-diff-1 expected actual) (%modes-missing actual expected)))

