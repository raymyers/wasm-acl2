; IL reader: read every top-level form of spectec --ast output with the
; ACL2 reader. Identifiers are strings in the IL; node heads are symbols and
; are compared by symbol-name only, so the reading package does not matter.
(in-package "IL2ACL2")
(program)
(set-state-ok t)

(defun read-objects-loop (channel acc state)
  (mv-let (eofp obj state)
    (read-object channel state)
    (if eofp
        (mv (reverse acc) state)
      (read-objects-loop channel (cons obj acc) state))))

; (mv erp forms state)
(defun read-il-file (filename state)
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (if (null channel)
        (mv (msg "Cannot open IL file ~s0" filename) nil state)
      (mv-let (forms state)
        (read-objects-loop channel nil state)
        (let ((state (close-input-channel channel state)))
          (mv nil forms state))))))

; Node-head helpers.
(defun head (x)
  (and (consp x) (symbolp (car x)) (car x) (symbol-name (car x))))

(defun is (x name) (equal (head x) name))

(defun atom-is (x name)
  (and (symbolp x) x (equal (symbol-name x) name)))
