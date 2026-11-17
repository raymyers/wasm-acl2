;; W0 item 4: stack capacity probes, compiled with JSCL.
;; W0-ITER has the shape of $ALLOCMEM/ITER2: (CONS 0 (rec (+ 1 k) n)).
(defun w0-iter (k n) (if (>= k n) nil (cons 0 (w0-iter (+ 1 k) n))))
(defun w0-list (n) (let ((l nil)) (dotimes (i n) (push 0 l)) l))
(defun w0-equal (n) (equal (w0-list n) (w0-list n)))
(defun w0-append (n) (length (append (w0-list n) (list 1))))
