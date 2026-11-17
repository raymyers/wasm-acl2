;; W0 item 2: compile FILES (env IN, space separated) to OUT with jscl-xc,
;; and print the compile time.
(let* ((out (sb-posix:getenv "OUT"))
       (in (let ((s (sb-posix:getenv "IN")) (r nil) (start 0))
             (loop for p = (position #\Space s :start start)
                   do (push (subseq s start p) r)
                   while p do (setq start (1+ p)))
             (nreverse r)))
       (t0 (get-internal-real-time)))
  (let ((*package* (find-package "JSCL-XC")))
    (jscl-xc::compile-application in out))
  (format t "~&W0-COMPILE-SECONDS ~,2F~%"
          (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
