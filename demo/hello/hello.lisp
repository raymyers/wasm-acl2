;; W0 item 1: the smallest JSCL application. It sets one global string, so
;; the node and browser checks can read it, and prints it.
(defun hello () (format nil "hello from JSCL: ~a" (+ 1 2)))
(setf #j:jsclHello (jscl-xc::jsstring (hello)))
(#j:console:log #j:jsclHello)
