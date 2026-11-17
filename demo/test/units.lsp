; W3 item 3: shim unit tests. Each form is evaluated by ACL2 (demo/extract,
; raw Lisp after the 3.0 portcullis: the expected values) and compiled into
; the JSCL test bundle through the extractor's printer (so the numeric and
; list functions are the shim's). demo/test/units.js compares the printed
; values. Read in package ACL2. Only inputs within the guards of the ACL2
; functions: outside them ACL2 signals a guard violation, and its raw Lisp
; definitions (which the expected values come from) may differ from the
; logical ones, e.g. (zp -1) is NIL in raw Lisp and T in the logic.
(
 ;; integers around 2^53 (the number/BigInt boundary) and 2^64
 (+ 9007199254740991 1) (+ 9007199254740991 2) (- -9007199254740991 1)
 (- 9007199254740993 2) (* 4294967296 4294967296) (* -4294967296 4294967297)
 (expt 2 53) (expt 2 64) (- (expt 2 64) 1) (expt 2 -3) (expt 3/2 3) (expt -2 63)
 ;; floor, mod, rem, truncate, ceiling, round: signs, BigInts, ratios
 (floor -7 2) (floor 7 -2) (floor -7 -2) (mod -7 2) (mod 7 -2) (mod -7 -2)
 (rem -7 2) (rem 7 -2) (truncate -7 2) (ceiling -7 2) (ceiling 7 2)
 (round 5 2) (round 7 2) (round -5 2) (round 1/2 1) (round 3/2 1)
 (floor (expt 2 64) 3) (mod (- (expt 2 64)) 7) (floor -1/2 1) (floor 7/2 1) (mod 7/2 1)
 (floor (- (expt 2 70)) (expt 2 40)) (mod (expt 2 70) -3) (truncate (- (expt 2 64)) 3)
 ;; ash both ways, logical ops
 (ash 1 64) (ash -1 -70) (ash (expt 2 64) -63) (ash -5 -1) (ash 5 3) (ash -3 60) (ash 7 -3)
 (logand -1 (- (expt 2 64) 1)) (logand -256 4095) (logior (expt 2 63) 1) (logxor -1 255)
 (lognot (expt 2 64)) (lognot -1) (logbitp 63 (expt 2 63)) (logbitp 3 -9)
 (logcount -8) (logcount (- (expt 2 64) 1)) (integer-length (expt 2 64)) (integer-length -1)
 (integer-length -129) (integer-length 0)
 ;; ratios
 (+ 1/3 1/6) (* 2/3 3/2) (/ 1 3) (/ -6 4) (- 1/2) (/ 1/2) (+ 1/2 (expt 2 64))
 (< 1/3 1/2) (< (expt 2 64) (expt 2 65)) (< -1/2 -1/3) (= 1/2 2/4) (= (expt 2 64) (expt 2 64))
 (numerator -6/4) (denominator -6/4) (numerator 5) (denominator 5)
 (integerp (expt 2 64)) (integerp 1/2) (rationalp 1/2) (rationalp "1") (evenp (expt 2 64))
 (min 1/2 1/3) (max (expt 2 64) 3)
 ;; EQUAL
 (equal (list 1 (expt 2 64) 1/2 "ab") (list 1 (expt 2 64) 1/2 "ab"))
 (equal 1/2 1/3) (equal (expt 2 64) (expt 2 64)) (equal 9007199254740992 (expt 2 53))
 (equal "ab" "abc") (equal '(1 . 2) '(1 . 2)) (equal '(1 2) '(1 2 3))
 ;; ACL2-COUNT
 (acl2-count (list 1 -2 (expt 2 64) 1/2 -3/4 "abc" 'x)) (acl2-count (take 70000 nil))
 (acl2-count '((1 . 2) . 3))
 ;; list functions (long lists: loops, not recursion)
 (len (take 70000 nil)) (true-listp (take 70000 nil)) (true-listp '(1 . 2))
 (take 3 '(1 2)) (take 0 '(1 2)) (update-nth 4 'a '(1 2)) (update-nth 0 'a '(1 2))
 (nfix -3) (nfix (expt 2 64)) (ifix 1/2) (rfix "x") (zp 0) (zp 5) (zp (expt 2 64)) (natp (expt 2 64)) (posp 0)
 (put-assoc-equal 'b 9 '((a . 1) (b . 2))) (put-assoc-equal 'c 9 '((a . 1)))
 (remove-duplicates-equal '(1 2 1 3 2)) (append '(1 2) '(3) nil '(4))
 (reverse '(1 2 3)) (member-equal 1/2 (list 1 1/2 3)) (member-eq 'b '(a b c))
 (assoc-equal (expt 2 64) (list (cons (expt 2 64) 'big))) (alistp '((a . 1) 2))
 (subsetp-equal '(1 2) '(2 3 1)) (iff 1 nil)
 (len (append (take 70000 nil) (take 70000 nil)))
 (equal (take 70000 nil) (take 70000 nil))
)
