;; W0 item 5: a prototype of option A (shim number tower) for the cost
;; sample. Integers are a JS number when |n| <= 2^53 - 1 and a JS BigInt
;; otherwise (always normalized back); the BigInt paths call the JS helpers
;; of big.js (globalThis.W0BIG). Only the fast paths run in the sample (all
;; operands are fixnums); the slow paths are here so that the fast path pays
;; for the same checks it would pay in the real shim.
(defconstant +safe+ 9007199254740991)
(defconstant +i31+ 1073741823)

(defun t-fix-p (x) (numberp x))               ; typeof x === "number"
(defun t-norm (b) (#j:W0BIG:norm b))          ; BigInt -> canonical integer

(defun t+ (a b)
  (if (and (numberp a) (numberp b))
      (let ((r (+ a b))) (if (<= (- +safe+) r +safe+) r (t-norm (#j:W0BIG:add a b))))
      (t-norm (#j:W0BIG:add a b))))

(defun t* (a b)
  (if (and (numberp a) (numberp b))
      (let ((r (* a b))) (if (<= (- +safe+) r +safe+) r (t-norm (#j:W0BIG:mul a b))))
      (t-norm (#j:W0BIG:mul a b))))

;; ACL2 floor is single valued; exact with doubles when both are below 2^31
(defun t-floor (a b)
  (if (and (numberp a) (numberp b) (<= (- +i31+) a +i31+) (<= (- +i31+) b +i31+) (/= b 0))
      (jscl-xc::%floor (/ a b))
      (t-norm (#j:W0BIG:floor a b))))

(defun t-logand (a b)
  (if (and (numberp a) (numberp b) (<= (- +i31+) a +i31+) (<= (- +i31+) b +i31+))
      (jscl-xc::%logand a b)
      (t-norm (#j:W0BIG:logand a b))))

(defun t-ash (x y)
  (if (and (numberp x) (numberp y) (<= (- +i31+) x +i31+) (<= -31 y 21))
      (if (< y 0) (jscl-xc::%ash-right x (- y)) (* x (jscl-xc::%ash-left 1 y)))
      (t-norm (#j:W0BIG:ash x y))))

;; the benchmark loops: plain JSCL against the tower, same operands
(defmacro defbench (name op k)
  `(defun ,name (n) (let ((s 0)) (dotimes (i n) (setq s (,op i ,k))) s)))
(defbench plain-+ + 12345)        (defbench tower-+ t+ 12345)
(defbench plain-* * 3)            (defbench tower-* t* 3)
(defbench plain-floor floor 7)    (defbench tower-floor t-floor 7)
(defbench plain-logand logand 255) (defbench tower-logand t-logand 255)
(defbench plain-ash ash 3)        (defbench tower-ash t-ash 3)
(defbench plain-ash-r ash -2)     (defbench tower-ash-r t-ash -2)
