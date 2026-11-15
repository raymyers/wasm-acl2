;;;; demo/shim/acl2.lisp: the ACL2 layer that the extracted semantics needs
;;;; under JSCL (plan/wasm3-demo §3, W3). Hand-written, so every part is
;;;; checked against ACL2 output (W3 vectors and unit tests, W4 conformance).
;;;;
;;;; The extractor prints every symbol package-qualified, and prints the CL
;;;; functions JSCL gets wrong for ACL2 (numbers: no bignums or ratios;
;;;; EQUAL and APPEND: recursive on CDR) as ACL2::<name> (W2, +SHADOWED+ in
;;;; demo/extract/extract.lisp). This file defines, in the package ACL2:
;;;;  - the numeric functions, on the D5 tower of num.js (macros that expand
;;;;    to the FFI call, so no extra Lisp frame on the hot path);
;;;;  - EQUAL, APPEND, REVERSE and the ACL2 list functions as loops (W0 item
;;;;    4: a Chromium Worker holds about 1,600 frames of JSCL's EQUAL);
;;;;  - ACL2-COUNT (the generated size checks run it), MV / MV-LET,
;;;;    HONS-COPY, and the hooks the extractor emits: %Q, %BIG, %DEFATTACH,
;;;;    %MEMOIZE. WRT::%RULE (W7 tags) is defined in rule.lisp.
;;;; Semantics follow the ACL2 definitions (cited per function); where ACL2
;;;; would signal a guard violation, the shim signals an error.

(defpackage "ACL2" (:use))
(defpackage "WRT" (:use))
(defpackage "W3T" (:use))
(defpackage "ACL2-SHIM" (:use "COMMON-LISP"))
(in-package "ACL2-SHIM")

(#j:ACL2N:init t nil)

;;; ------------------------------------------------------------ numbers
;;; ACL2's + and * take any number of arguments (macros over binary-+ and
;;; binary-*); - and / take one or two; the comparisons, MIN, MAX, FLOOR,
;;; MOD, ... are binary. Exact rational arithmetic, on num.js.

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun fold (fn xs)
    (let ((acc (car xs)))
      (dolist (x (cdr xs) acc) (setq acc (list fn acc x))))))

(defmacro acl2::+ (&rest xs)
  (cond ((null xs) 0)
        ((null (cdr xs)) `(#j:ACL2N:add 0 ,(car xs)))
        (t (fold '%add xs))))
(defmacro %add (a b) `(#j:ACL2N:add ,a ,b))
(defmacro acl2::* (&rest xs)
  (cond ((null xs) 1)
        ((null (cdr xs)) `(#j:ACL2N:mul 1 ,(car xs)))
        (t (fold '%mul xs))))
(defmacro %mul (a b) `(#j:ACL2N:mul ,a ,b))
(defmacro acl2::- (a &optional (b nil bp))
  (if bp `(#j:ACL2N:sub ,a ,b) `(#j:ACL2N:neg ,a)))
(defmacro acl2::/ (a &optional (b nil bp))
  (if bp `(#j:ACL2N:div ,a ,b) `(#j:ACL2N:div 1 ,a)))
(defmacro acl2::1+ (a) `(#j:ACL2N:add ,a 1))
(defmacro acl2::1- (a) `(#j:ACL2N:sub ,a 1))

(defmacro acl2::< (a b) `(#j:ACL2N:lt ,a ,b))
(defmacro acl2::> (a b) `(#j:ACL2N:gt ,a ,b))
(defmacro acl2::<= (a b) `(#j:ACL2N:le ,a ,b))
(defmacro acl2::>= (a b) `(#j:ACL2N:ge ,a ,b))
(defmacro acl2::= (a b) `(#j:ACL2N:eq ,a ,b))
(defmacro acl2::/= (a b) `(not (#j:ACL2N:eq ,a ,b)))
(defmacro acl2::min (a b) `(#j:ACL2N:min ,a ,b))
(defmacro acl2::max (a b) `(#j:ACL2N:max ,a ,b))
(defmacro acl2::abs (a) `(#j:ACL2N:abs ,a))
(defmacro acl2::signum (a) `(#j:ACL2N:signum ,a))

(defmacro acl2::floor (a b) `(#j:ACL2N:floor ,a ,b))
(defmacro acl2::ceiling (a b) `(#j:ACL2N:ceiling ,a ,b))
(defmacro acl2::truncate (a b) `(#j:ACL2N:truncate ,a ,b))
(defmacro acl2::round (a b) `(#j:ACL2N:round ,a ,b))
(defmacro acl2::mod (a b) `(#j:ACL2N:mod ,a ,b))
(defmacro acl2::rem (a b) `(#j:ACL2N:rem ,a ,b))
(defmacro acl2::expt (a b) `(#j:ACL2N:expt ,a ,b))
(defmacro acl2::ash (a b) `(#j:ACL2N:ash ,a ,b))

;; LOGAND, LOGIOR, LOGXOR are macros over binary versions in ACL2
(defmacro acl2::logand (&rest xs) (if xs (fold '%logand xs) -1))
(defmacro %logand (a b) `(#j:ACL2N:logand ,a ,b))
(defmacro acl2::logior (&rest xs) (if xs (fold '%logior xs) 0))
(defmacro %logior (a b) `(#j:ACL2N:logior ,a ,b))
(defmacro acl2::logxor (&rest xs) (if xs (fold '%logxor xs) 0))
(defmacro %logxor (a b) `(#j:ACL2N:logxor ,a ,b))
(defmacro acl2::lognot (a) `(#j:ACL2N:lognot ,a))
(defmacro acl2::logbitp (i j) `(#j:ACL2N:logbitp ,i ,j))
(defmacro acl2::logcount (a) `(#j:ACL2N:logcount ,a))
(defmacro acl2::integer-length (a) `(#j:ACL2N:integerLength ,a))

(defmacro acl2::numerator (a) `(#j:ACL2N:numerator ,a))
(defmacro acl2::denominator (a) `(#j:ACL2N:denominator ,a))
(defmacro acl2::integerp (a) `(#j:ACL2N:integerp ,a))
(defmacro acl2::rationalp (a) `(#j:ACL2N:rationalp ,a))
(defmacro acl2::numberp (a) `(#j:ACL2N:rationalp ,a))   ; no complex numbers here
(defmacro acl2::evenp (a) `(#j:ACL2N:evenp ,a))
(defmacro acl2::oddp (a) `(#j:ACL2N:oddp ,a))
(defmacro acl2::zerop (a) `(#j:ACL2N:zerop ,a))
(defmacro acl2::plusp (a) `(#j:ACL2N:plusp ,a))
(defmacro acl2::minusp (a) `(#j:ACL2N:minusp ,a))

;; literals the extractor rewrote (W0 item 2: JSCL reads 1/2 as a symbol)
(defun acl2::%q (n d) (#j:ACL2N:q n d))
(defun acl2::%big (s) (#j:ACL2N:big (jscl-xc::jsstring s)))

;; ACL2 fixers and recognizers (axioms.lisp)
(defun acl2::natp (x) (and (acl2::integerp x) (acl2::<= 0 x)))
(defun acl2::posp (x) (and (acl2::integerp x) (acl2::< 0 x)))
(defun acl2::zp (x) (if (acl2::integerp x) (acl2::<= x 0) t))
(defun acl2::nfix (x) (if (acl2::natp x) x 0))
(defun acl2::ifix (x) (if (acl2::integerp x) x 0))
(defun acl2::rfix (x) (if (acl2::rationalp x) x 0))

;;; ------------------------------------------------------------- loops
;;; JSCL compiles LOOP/RETURN to a TAGBODY whose GO throws a JS exception
;;; on every iteration (measured: LEN over a 64 KiB memory, 41 s for a
;;; 16-instruction run). WHILE is the JS while loop (DO expands to it too).
(defmacro while (test &body body) `(jscl-xc::%while ,test ,@body))

;;; -------------------------------------------- EQUAL and the hot list ops
;;; In list.js (JS loops; why: see there). Definitions as in axioms.lisp:
;;;  (equal x y)            loop on CDR, recursion on CAR; numbers canonical
;;;  (len x)                number of conses
;;;  (true-listp x)         ends in NIL
;;;  (binary-append x y)    (if (endp x) y (cons (car x) (binary-append (cdr x) y)))
;;;  (take n l)             first n elements, NIL-padded
;;;  (update-nth n v l)     element n replaced, NIL-padded
;;;  (member-equal x l), (member-eq x l), (assoc-equal x l)
;;;  (acl2-count x)         conses 1 + car + cdr; integers |i|; ratios
;;;                         |num| + den; strings their length; else 0
(#j:ACL2L:init t nil (cons nil nil))
(defun acl2::equal (a b) (#j:ACL2L:equal a b))
(defun acl2::len (x) (#j:ACL2L:len x))
(defun acl2::true-listp (x) (#j:ACL2L:trueListp x))
(defun %append2 (x y) (#j:ACL2L:append2 x y))
(defmacro acl2::append (&rest xs)
  (cond ((null xs) nil)
        ((null (cdr xs)) (car xs))
        (t `(%append2 ,(car xs) (acl2::append ,@(cdr xs))))))
;; (reverse x): strings too (axioms.lisp)
(defun acl2::reverse (x) (if (stringp x) (reverse x) (#j:ACL2L:revappend x nil)))
(defun acl2::take (n l) (#j:ACL2L:take (acl2::nfix n) l))
(defun acl2::update-nth (n v l) (#j:ACL2L:updateNth (acl2::nfix n) v l))
(defun acl2::member-equal (x l) (#j:ACL2L:memberEqual x l))
(defun acl2::member-eq (x l) (#j:ACL2L:memberEq x l))
(defun acl2::assoc-equal (x l) (#j:ACL2L:assocEqual x l))
(defun acl2::acl2-count (x) (#j:ACL2L:count x))

;;; ------------------------------------------------ other list functions
;; (put-assoc-equal name val alist): replace the first binding, else add at the end
(defun acl2::put-assoc-equal (name val alist)
  (let* ((head (list nil)) (tail head))
    (while (and (consp alist) (null (acl2::equal name (car (car alist)))))
      (setq tail (setf (cdr tail) (list (car alist))) alist (cdr alist)))
    (setf (cdr tail) (cons (cons name val) (if (consp alist) (cdr alist) nil)))
    (cdr head)))
(defun acl2::alistp (l)
  (while (and (consp l) (consp (car l))) (setq l (cdr l)))
  (null l))
;; keeps the LAST occurrence of each element (axioms.lisp)
(defun acl2::remove-duplicates-equal (l)
  (let ((acc nil))
    (while (consp l)
      (unless (acl2::member-equal (car l) (cdr l)) (push (car l) acc))
      (setq l (cdr l)))
    (nreverse acc)))
(defun acl2::subsetp-equal (x y)
  (while (and (consp x) (acl2::member-equal (car x) y)) (setq x (cdr x)))
  (atom x))
(defun acl2::iff (p q) (if p (if q t nil) (if q nil t)))
(defun acl2::hons-copy (x) x)                         ; sharing only, same value
(defun acl2::make-ord (fe fco rst) (cons (cons fe fco) rst))

;;; ---------------------------------------------------- multiple values
(defmacro acl2::mv (&rest xs) `(values ,@xs))
(defmacro acl2::mv-let (vars form &body body) `(multiple-value-bind ,vars ,form ,@body))

;;; ------------------------------------------------ events the extractor maps
;; (defattach f g): F calls G until the driver attaches another function
(defun acl2::%defattach (f g)
  (setf (symbol-function f) (lambda (&rest args) (apply (symbol-function g) args)))
  f)
;; memoization is semantically the identity; not done yet (performance only)
(defun acl2::%memoize (f) f)

;; (intern$ name pkg): intern in package PKG (the test books make keywords)
(defun acl2::intern$ (s p) (intern s p))
