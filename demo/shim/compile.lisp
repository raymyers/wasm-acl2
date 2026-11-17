;; Compile the files in $IN (space separated) into $OUT with the jscl-xc
;; image, in one compilation unit (macros of earlier files apply to later
;; ones). Prints the compile time.
(let* ((out (sb-posix:getenv "OUT"))
       (in (let ((s (sb-posix:getenv "IN")) (r nil) (start 0))
             (loop for p = (position #\Space s :start start)
                   do (let ((w (subseq s start p))) (when (plusp (length w)) (push w r)))
                   while p do (setq start (1+ p)))
             (nreverse r)))
       (t0 (get-internal-real-time)))
  (let ((*package* (find-package "JSCL-XC")))
    (jscl-xc::compile-application in out))
  (format t "~&DEMO-COMPILE ~D files, ~,2F s~%" (length in)
          (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
