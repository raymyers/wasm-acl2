; Hand-written SpecTec builtins (hint(builtin) in 3-numerics.spectec) and
; config overrides (il2acl2-config.lsp) for the generated W1T semantics.
; These are the ONLY hand-written semantic definitions (plan §2.4).
;
; Encoding (plan §2.2): iN/uN/byte/char are naturals; fN is (:POS mag) or
; (:NEG mag) with mag = (:NORM m e) | (:SUBNORM m) | (:INF) | (:NAN m);
; a NAN payload m is the significand; ? and * are lists.
(in-package "W1T")

(include-book "prelude")

; ---------------------------------------------------------------------
; Override: $utf8 (il2acl2-config.lsp). UTF-8 encoding of a char list,
; matching the four clauses of A-binary.spectec $utf8.

(defun %utf8-char (c)
  (declare (xargs :guard (natp c)))
  (cond ((< c #x80) (list c))
        ((< c #x800) (list (+ #xC0 (floor c 64)) (+ #x80 (mod c 64))))
        ((< c #x10000) (list (+ #xE0 (floor c 4096))
                             (+ #x80 (mod (floor c 64) 64))
                             (+ #x80 (mod c 64))))
        (t (list (+ #xF0 (floor c 262144))
                 (+ #x80 (mod (floor c 4096) 64))
                 (+ #x80 (mod (floor c 64) 64))
                 (+ #x80 (mod c 64))))))

(defun $utf8 (chs)
  (declare (xargs :guard (nat-listp chs)))
  (if (atom chs) nil (append (%utf8-char (car chs)) ($utf8 (cdr chs)))))

; Its inverse (config :inverse "utf8"): decode a UTF-8 byte list. On invalid
; input the result does not re-encode to the input, so the generated check
; $utf8(x) = bytes rejects it.
(defun %cont (b) (mod (nfix b) 64))
(defun $inv_utf8 (bs)
  (declare (xargs :measure (acl2::len bs)))
  (if (atom bs) nil
    (let ((b (nfix (car bs))))
      (cond ((< b #x80) (cons b ($inv_utf8 (cdr bs))))
            ((and (< b #xE0) (consp (cdr bs)))
             (cons (+ (* 64 (- b #xC0)) (%cont (cadr bs))) ($inv_utf8 (cddr bs))))
            ((and (< b #xF0) (consp (cdr bs)) (consp (cddr bs)))
             (cons (+ (* 4096 (- b #xE0)) (* 64 (%cont (cadr bs))) (%cont (caddr bs)))
                   ($inv_utf8 (cdddr bs))))
            ((and (consp (cdr bs)) (consp (cddr bs)) (consp (cdddr bs)))
             (cons (+ (* 262144 (- b #xF0)) (* 4096 (%cont (cadr bs)))
                      (* 64 (%cont (caddr bs))) (%cont (cadddr bs)))
                   ($inv_utf8 (cddddr bs))))
            (t (list #x110000))))))                    ; not a char: rejected

; ---------------------------------------------------------------------
; Builtins (plan §2.4). Written from the WASM 1.0 spec text, in pure ACL2
; (no community books), independently of WASM1. Logic mode; guards are not
; verified (T8). Float results are lists (fN* in SpecTec: the spec allows a
; set of results for NaNs); we return exactly one, using the canonical NaN.

(set-verify-guards-eagerness 0)

(defun %pow2 (n) (expt 2 (nfix n)))
(defun %u (n i) (mod (ifix i) (%pow2 n)))                    ; wrap to N bits
(defun %s (n i)                                              ; signed view
  (let ((i (%u n i))) (if (< i (%pow2 (1- n))) i (- i (%pow2 n)))))
(defun %sx-signed-p (sx) (and (consp sx) (eq (car sx) :s)))  ; sx = (:U) | (:S)

; --- conversions -----------------------------------------------------

(defun $truncz (q) (truncate (rfix q) 1))
(defun $wrap__ (m n i) (declare (ignore m)) (%u n i))
(defun $extend__ (m n sx i)
  (%u n (if (%sx-signed-p sx) (%s m i) (%u m i))))

; --- integer operations ----------------------------------------------

(defun $inot_ (n i) (%u n (lognot (ifix i))))
(defun $iand_ (n a b) (%u n (logand (ifix a) (ifix b))))
(defun $ior_ (n a b) (%u n (logior (ifix a) (ifix b))))
(defun $ixor_ (n a b) (%u n (logxor (ifix a) (ifix b))))
(defun $ishl_ (n i k) (%u n (ash (ifix i) (mod (ifix k) (nfix n)))))
(defun $ishr_ (n sx i k)
  (let ((k (mod (ifix k) (nfix n))))
    (%u n (ash (if (%sx-signed-p sx) (%s n i) (%u n i)) (- k)))))
(defun $irotl_ (n i k)
  (let ((k (mod (ifix k) (nfix n))) (i (%u n i)))
    (%u n (logior (ash i k) (ash i (- k (nfix n)))))))
(defun $irotr_ (n i k)
  (let ((k (mod (ifix k) (nfix n))) (i (%u n i)))
    (%u n (logior (ash i (- k)) (ash i (- (nfix n) k))))))
(defun $iclz_ (n i) (- (nfix n) (integer-length (%u n i))))
(defun %ctz (i k n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix k)))))
  (if (or (>= (nfix k) (nfix n)) (logbitp (nfix k) i)) (nfix k)
    (%ctz i (1+ (nfix k)) n)))
(defun $ictz_ (n i) (%ctz (%u n i) 0 n))
(defun $ipopcnt_ (n i) (logcount (%u n i)))

; --- floats: representation -------------------------------------------
; fN = (:POS mag) | (:NEG mag); mag = (:NORM m e) | (:SUBNORM m) | (:INF) | (:NAN m)
; value(NORM m e) = (1 + m/2^M) 2^e, value(SUBNORM m) = (m/2^M) 2^emin.

(defun %fm (n) (if (equal n 32) 23 52))           ; $M(N)
(defun %fe (n) (if (equal n 32) 8 11))            ; $E(N)
(defun %emax (n) (1- (%pow2 (1- (%fe n)))))
(defun %emin (n) (- 2 (%pow2 (1- (%fe n)))))

(defun %neg-p (f) (and (consp f) (eq (car f) :neg)))
(defun %mag (f) (and (consp f) (cadr f)))
(defun %kind (f) (let ((m (%mag f))) (and (consp m) (car m))))
(defun %nan-p (f) (eq (%kind f) :nan))
(defun %inf-p (f) (eq (%kind f) :inf))
(defun %mk (neg mag) (list (if neg :neg :pos) mag))
(defun %canon-nan (n) (list :pos (list :nan (%pow2 (1- (%fm n))))))
(defun %zero (neg) (%mk neg (list :subnorm 0)))

; Absolute value of a finite float, as a rational.
(defun %absval (n f)
  (let ((m (%mag f)) (mm (%fm n)))
    (case (%kind f)
      (:norm (* (+ 1 (/ (nfix (cadr m)) (%pow2 mm))) (expt 2 (ifix (caddr m)))))
      (:subnorm (* (/ (nfix (cadr m)) (%pow2 mm)) (expt 2 (%emin n))))
      (t 0))))
(defun %val (n f) (if (%neg-p f) (- (%absval n f)) (%absval n f)))
(defun %zero-p (n f) (and (eq (%kind f) :subnorm) (equal (%absval n f) 0)))

; floor(log2 q) for rational q > 0.
(defun %ilog2 (q)
  (let* ((num (numerator q)) (den (denominator q))
         (e (- (integer-length num) (integer-length den))))
    ;; 2^(e-1) < q < 2^(e+1); fix up
    (if (< q (expt 2 e)) (1- e) e)))

(defun %round-even (q)                             ; nearest integer, ties to even
  (let* ((fl (floor q 1)) (d (- q fl)))
    (cond ((< d 1/2) fl) ((> d 1/2) (1+ fl)) ((evenp fl) fl) (t (1+ fl)))))

; Round a nonzero rational magnitude q > 0 to an fN magnitude (nearest-even).
(defun %round-mag (n q)
  (let* ((mm (%fm n)) (e (max (%ilog2 q) (%emin n)))
         (quantum (expt 2 (- e mm)))
         (r (%round-even (/ q quantum))))         ; significand incl. hidden bit
    (cond ((>= r (%pow2 (1+ mm)))                  ; carry into next binade
           (if (> (1+ e) (%emax n)) (list :inf) (list :norm 0 (1+ e))))
          ((> e (%emax n)) (list :inf))
          ((< r (%pow2 mm)) (list :subnorm r))     ; only when e = emin
          (t (list :norm (- r (%pow2 mm)) e)))))

; Round a rational to fN; ZERO-NEG gives the sign of an exact-zero result.
(defun %round (n q zero-neg)
  (cond ((equal q 0) (%zero zero-neg))
        ((< q 0) (%mk t (%round-mag n (- q))))
        (t (%mk nil (%round-mag n q)))))

; --- floats: arithmetic ------------------------------------------------

(defun $fadd_ (n a b)
  (cond ((or (%nan-p a) (%nan-p b)) (list (%canon-nan n)))
        ((and (%inf-p a) (%inf-p b))
         (if (eq (%neg-p a) (%neg-p b)) (list a) (list (%canon-nan n))))
        ((%inf-p a) (list a))
        ((%inf-p b) (list b))
        (t (list (%round n (+ (%val n a) (%val n b))
                         (and (%neg-p a) (%neg-p b)))))))   ; -0 + -0 = -0, else +0

(defun %fneg (f) (%mk (not (%neg-p f)) (%mag f)))
(defun $fneg_ (n f) (declare (ignore n)) (list (%fneg f)))
(defun $fabs_ (n f) (declare (ignore n)) (list (%mk nil (%mag f))))
(defun $fcopysign_ (n a b) (declare (ignore n)) (list (%mk (%neg-p b) (%mag a))))
(defun $fsub_ (n a b) ($fadd_ n a (%fneg b)))

(defun $fmul_ (n a b)
  (let ((neg (not (eq (%neg-p a) (%neg-p b)))))
    (cond ((or (%nan-p a) (%nan-p b)) (list (%canon-nan n)))
          ((or (%inf-p a) (%inf-p b))
           (if (or (%zero-p n a) (%zero-p n b)) (list (%canon-nan n))
             (list (%mk neg (list :inf)))))
          (t (list (%round n (* (%val n a) (%val n b)) neg))))))

(defun $fdiv_ (n a b)
  (let ((neg (not (eq (%neg-p a) (%neg-p b)))))
    (cond ((or (%nan-p a) (%nan-p b)) (list (%canon-nan n)))
          ((and (%inf-p a) (%inf-p b)) (list (%canon-nan n)))
          ((%inf-p a) (list (%mk neg (list :inf))))
          ((%inf-p b) (list (%zero neg)))
          ((%zero-p n b)
           (if (%zero-p n a) (list (%canon-nan n)) (list (%mk neg (list :inf)))))
          (t (list (%round n (/ (%val n a) (%val n b)) neg))))))

; ordering on non-NaN floats, with infinities
(defun %lt (n a b)
  (cond ((and (%inf-p a) (%inf-p b)) (and (%neg-p a) (not (%neg-p b))))
        ((%inf-p a) (%neg-p a))
        ((%inf-p b) (not (%neg-p b)))
        (t (< (%val n a) (%val n b)))))
(defun %feq (n a b)
  (and (not (%nan-p a)) (not (%nan-p b))
       (or (equal a b) (and (%zero-p n a) (%zero-p n b))
           (and (not (%inf-p a)) (not (%inf-p b)) (equal (%val n a) (%val n b))))))

(defun $fmin_ (n a b)
  (cond ((or (%nan-p a) (%nan-p b)) (list (%canon-nan n)))
        ((and (%zero-p n a) (%zero-p n b)) (list (%zero (or (%neg-p a) (%neg-p b)))))
        ((%lt n b a) (list b))
        (t (list a))))
(defun $fmax_ (n a b)
  (cond ((or (%nan-p a) (%nan-p b)) (list (%canon-nan n)))
        ((and (%zero-p n a) (%zero-p n b)) (list (%zero (and (%neg-p a) (%neg-p b)))))
        ((%lt n a b) (list b))
        (t (list a))))

(defun %bool (x) (if x 1 0))
(defun $feq_ (n a b) (%bool (%feq n a b)))
(defun $fne_ (n a b) (%bool (not (%feq n a b))))
(defun $flt_ (n a b) (%bool (and (not (%nan-p a)) (not (%nan-p b)) (not (%feq n a b)) (%lt n a b))))
(defun $fgt_ (n a b) (%bool (and (not (%nan-p a)) (not (%nan-p b)) (not (%feq n a b)) (%lt n b a))))
(defun $fle_ (n a b) (%bool (and (not (%nan-p a)) (not (%nan-p b)) (or (%feq n a b) (%lt n a b)))))
(defun $fge_ (n a b) (%bool (and (not (%nan-p a)) (not (%nan-p b)) (or (%feq n a b) (%lt n b a)))))

; integer square root: largest s with s*s <= x (Newton iteration)
(defun %isqrt-iter (x s fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) s
    (let ((s2 (floor (+ s (floor x s)) 2)))
      (if (>= s2 s) s (%isqrt-iter x s2 (1- fuel))))))
(defun %isqrt (x)
  (let ((x (nfix x)))
    (if (< x 2) x
      (let* ((s (%isqrt-iter x (%pow2 (1+ (floor (integer-length x) 2))) (+ 8 (integer-length x)))))
        (cond ((> (* s s) x) (1- s)) ((<= (* (1+ s) (1+ s)) x) (1+ s)) (t s))))))

(defun $fsqrt_ (n f)
  (cond ((%nan-p f) (list (%canon-nan n)))
        ((%zero-p n f) (list f))                                  ; sqrt(+-0) = +-0
        ((%neg-p f) (list (%canon-nan n)))
        ((%inf-p f) (list f))
        (t (let* ((q (%val n f))
                  (k (+ (%fm n) 4 (max 0 (- (%ilog2 q)))))      ; >= M+3 bits in s
                  (x (* q (expt 4 k)))
                  (s (%isqrt (floor x 1)))
                  (exact (and (integerp x) (equal (* s s) x)))
                  (proxy (/ (if exact s (+ s 1/2)) (%pow2 k))))  ; sticky bit
             (list (%round n proxy nil))))))

; rounding to an integral value; the sign of a zero result is the input's
(defun %fint (n f mode)
  (cond ((%nan-p f) (list (%canon-nan n)))
        ((or (%inf-p f) (%zero-p n f)) (list f))
        (t (let* ((q (%val n f))
                  (r (case mode
                       (:ceil (ceiling q 1)) (:floor (floor q 1))
                       (:trunc (truncate q 1)) (t (%round-even q)))))
             (list (%round n r (%neg-p f)))))))
(defun $fceil_ (n f) (%fint n f :ceil))
(defun $ffloor_ (n f) (%fint n f :floor))
(defun $ftrunc_ (n f) (%fint n f :trunc))
(defun $fnearest_ (n f) (%fint n f :nearest))

; --- float conversions -------------------------------------------------

(defun $trunc__ (m n sx f)
  (if (or (%nan-p f) (%inf-p f)) nil
    (let ((tq (truncate (%val m f) 1)))
      (if (%sx-signed-p sx)
          (if (and (<= (- (%pow2 (1- n))) tq) (< tq (%pow2 (1- n)))) (list (%u n tq)) nil)
        (if (and (<= 0 tq) (< tq (%pow2 n))) (list tq) nil)))))

(defun $convert__ (m n sx i)
  (%round n (if (%sx-signed-p sx) (%s m i) (%u m i)) nil))

(defun %fconv (m n f)
  (cond ((%nan-p f) (list (%canon-nan n)))
        ((%inf-p f) (list f))
        ((%zero-p m f) (list (%zero (%neg-p f))))
        (t (list (%round n (%val m f) (%neg-p f))))))
(defun $promote__ (m n f) (%fconv m n f))
(defun $demote__ (m n f) (%fconv m n f))

; --- bit patterns and bytes ---------------------------------------------

(defun %fbits (n f)                                    ; fN -> N-bit pattern
  (let* ((mm (%fm n)) (bias (%emax n)) (mag (%mag f))
         (sign (if (%neg-p f) (%pow2 (1- n)) 0))
         (allones (1- (%pow2 (%fe n)))))
    (+ sign
       (case (%kind f)
         (:norm (+ (* (+ (ifix (caddr mag)) bias) (%pow2 mm)) (nfix (cadr mag))))
         (:subnorm (nfix (cadr mag)))
         (:inf (* allones (%pow2 mm)))
         (t (+ (* allones (%pow2 mm)) (nfix (cadr mag))))))))

(defun %bitsf (n i)                                    ; N-bit pattern -> fN
  (let* ((i (%u n i)) (mm (%fm n)) (bias (%emax n))
         (neg (>= i (%pow2 (1- n))))
         (ex (mod (floor i (%pow2 mm)) (%pow2 (%fe n))))
         (frac (mod i (%pow2 mm)))
         (allones (1- (%pow2 (%fe n)))))
    (%mk neg (cond ((equal ex 0) (list :subnorm frac))
                   ((equal ex allones) (if (equal frac 0) (list :inf) (list :nan frac)))
                   (t (list :norm frac (- ex bias)))))))

(defun %int-vt-p (vt) (and (consp vt) (member-eq (car vt) '(:i32 :i64)) t))
(defun %vt-size (vt) (if (and (consp vt) (member-eq (car vt) '(:i64 :f64))) 64 32))

(defun $reinterpret__ (vt1 vt2 v)
  (declare (ignore vt2))
  (if (%int-vt-p vt1) (%bitsf (%vt-size vt1) v) (%fbits (%vt-size vt1) v)))

(defun %le-bytes (k i)                                 ; k bytes, little endian
  (if (zp k) nil (cons (mod (ifix i) 256) (%le-bytes (1- k) (floor (ifix i) 256)))))
(defun %le-int (bs)
  (if (atom bs) 0 (+ (nfix (car bs)) (* 256 (%le-int (cdr bs))))))

(defun $ibytes_ (n i) (%le-bytes (floor (nfix n) 8) (%u n i)))
(defun $fbytes_ (n f) (%le-bytes (floor (nfix n) 8) (%fbits n f)))
(defun $bytes_ (vt v)
  (if (%int-vt-p vt) ($ibytes_ (%vt-size vt) v) ($fbytes_ (%vt-size vt) v)))
(defun $inv_ibytes_ (n bs) (%u n (%le-int bs)))
(defun $inv_fbytes_ (n bs) (%bitsf n (%le-int bs)))
(defun $inv_bytes_ (vt bs)
  (if (%int-vt-p vt) ($inv_ibytes_ (%vt-size vt) bs) ($inv_fbytes_ (%vt-size vt) bs)))
