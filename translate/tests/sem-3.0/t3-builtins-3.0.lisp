; 3.0 builtins without an engine oracle (wasm3 M1; the oracle column of
; plan/wasm3-translation-prep/notes/P3-builtin-inventory.md): byte
; encodings of storage and constant types, $ceilz, $inv_concatn_,
; $utf8single, the $hostcall hook and the choice parameters. Each case is
; a known value or an inverse property; the book fails if one is false.
(in-package "W3T")
(include-book "../../gen/wasm-3.0/wasm3")

(program)
(set-state-ok t)

(defun ints-upto (n) (if (zp n) (list 0) (cons n (ints-upto (1- n)))))

; inv_zbytes(zt, zbytes(zt, c)) = c for every c in L, and the byte length
(defun zbytes-roundtrip (zt len l)
  (or (atom l)
      (and (equal ($inv_zbytes_ zt ($zbytes_ zt (car l))) (car l))
           (equal (acl2::len ($zbytes_ zt (car l))) len)
           (zbytes-roundtrip zt len (cdr l)))))

(defun utf8single-agrees (l)                   ; = 1.0's utf8 of one character
  (or (atom l)
      (and (equal ($utf8single (car l)) ($utf8 (list (car l))))
           (utf8single-agrees (cdr l)))))

(defconst *big*                                 ; samples of 8 to 128 bits
  '(0 1 127 128 255 256 32767 32768 65535 #x12345678 #xffffffff #x123456789abcdef0
    #xffffffffffffffff #x0123456789abcdef0123456789abcdef))

(defun take-below (l bound) (cond ((atom l) nil) ((< (car l) bound) (cons (car l) (take-below (cdr l) bound))) (t (take-below (cdr l) bound))))

(defun cases ()
  `(("zbytes i8 little endian" ,($zbytes_ '(:i8) #xab) (#xab))
    ("zbytes i16 little endian" ,($zbytes_ '(:i16) #x1234) (#x34 #x12))
    ("zbytes i32 = nbytes" ,($zbytes_ '(:i32) #x01020304) ,($nbytes_ '(:i32) #x01020304))
    ("zbytes v128 = vbytes" ,($zbytes_ '(:v128) #x0102) ,($vbytes_ '(:v128) #x0102))
    ("zbytes f32 1.0" ,($zbytes_ '(:f32) (%bitsf 32 #x3f800000)) (0 0 #x80 #x3f))
    ("cbytes i64 = nbytes" ,($cbytes_ '(:i64) 5) ,($nbytes_ '(:i64) 5))
    ("cbytes v128 = vbytes" ,($cbytes_ '(:v128) 7) ,($vbytes_ '(:v128) 7))
    ("inv_cbytes f64" ,(%fbits 64 ($inv_cbytes_ '(:f64) '(0 0 0 0 0 0 #xf0 #x3f))) #x3ff0000000000000)
    ("roundtrip i8" ,(zbytes-roundtrip '(:i8) 1 (ints-upto 255)) t)
    ("roundtrip i16" ,(zbytes-roundtrip '(:i16) 2 (take-below *big* 65536)) t)
    ("roundtrip i32" ,(zbytes-roundtrip '(:i32) 4 (take-below *big* (expt 2 32))) t)
    ("roundtrip i64" ,(zbytes-roundtrip '(:i64) 8 (take-below *big* (expt 2 64))) t)
    ("roundtrip v128" ,(zbytes-roundtrip '(:v128) 16 *big*) t)
    ("ceilz 7/2" ,($ceilz 7/2) 4)
    ("ceilz -7/2" ,($ceilz -7/2) -3)
    ("ceilz 3" ,($ceilz 3) 3)
    ("ceilz -1/3" ,($ceilz -1/3) 0)
    ("inv_concatn 2" ,($inv_concatn_ 2 '(1 2 3 4 5 6)) ((1 2) (3 4) (5 6)))
    ("inv_concatn 3, rest dropped" ,($inv_concatn_ 3 '(1 2 3 4)) ((1 2 3)))
    ("inv_concatn empty" ,($inv_concatn_ 4 nil) nil)
    ("utf8single = utf8" ,(utf8single-agrees '(0 #x41 #x7f #x80 #x7ff #x800 #xd7ff #xe000 #xffff #x10000 #x10ffff)) t)
    ("utf8single surrogate" ,($utf8single #xd800) nil)
    ("utf8single above U+10FFFF" ,($utf8single #x110000) nil)
    ("hostcall default: no result" ,($hostcall '(:_hostfunc "f") nil nil) nil)
    ("ND false" ,($nd) nil)
    ("R parameters" ,(list ($r_fmadd) ($r_fmin) ($r_fmax) ($r_idot) ($r_idot_add) ($r_iq15mulr)
                           ($r_trunc_u) ($r_trunc_s) ($r_swizzle) ($r_laneselect))
     (1 0 0 0 0 0 0 0 0 0))))

(defun failing (cs) (cond ((atom cs) nil) ((equal (cadr (car cs)) (caddr (car cs))) (failing (cdr cs))) (t (cons (car cs) (failing (cdr cs))))))

; the cases are evaluated in make-event, where the $hostcall attachment is
; used (ACL2 does not use attachments when it evaluates a defconst)
(make-event
 (let* ((cs (cases)) (bad (failing cs)))
   (prog2$ (cw "~%T3 builtins (3.0): ~x0 of ~x1 cases hold.~%" (- (acl2::len cs) (acl2::len bad)) (acl2::len cs))
           (if bad (mv (msg "failing: ~x0" bad) nil state)
             (mv nil '(value-triple :t3-builtins-3.0-ok) state)))))
