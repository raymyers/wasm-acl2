; T2 exit check: generated recognizers accept/reject concrete values in the
; encoding of plan §2.2, and the generated book is in logic mode.
(in-package "W1T")
(include-book "../../gen/wasm1")

(defmacro %check (name form)
  `(make-event (if ,form '(value-triple ,name)
                 (er hard ',name "check failed: ~x0" ',form))))

; numbers and newtypes (elided "%" variants are their payload)
(%check :byte (and (byte-p 0) (byte-p 255) (not (byte-p 256)) (not (byte-p -1))))
(%check :un (and (un-p 4294967295 32) (not (un-p 4294967296 32))))
(%check :sn (and (sn-p -128 8) (sn-p 127 8) (not (sn-p 128 8))))
(%check :i32 (and (i32-p 7) (not (i32-p (expt 2 32)))))

; floats: (:POS|:NEG mag), mag = (:NORM m e) | (:SUBNORM m) | (:INF) | (:NAN m)
(%check :fn (and (fn-p '(:pos (:inf)) 32)
                 (fn-p '(:neg (:nan 1)) 32)
                 (not (fn-p '(:neg (:nan 0)) 32))      ; NaN payload must be >= 1
                 (fn-p '(:pos (:norm 0 0)) 32)
                 (fn-p '(:pos (:subnorm 5)) 64)
                 (not (fn-p '(:pos (:norm 0 128)) 32))  ; exponent out of range
                 (not (fn-p '(:zero) 32))))

; records: (:%REC (:FIELD . v) ...) in declaration order
(%check :memarg (and (memarg-p '(:%rec (:align . 0) (:offset . 16)))
                     (not (memarg-p '(:%rec (:offset . 16) (:align . 0))))))

; names: char* with |utf8(char*)| < 2^32 (uses the $utf8 override)
(%check :name (and (name-p '(97 98 99)) (name-p '(955))
                   (not (name-p '(#xD800)))))             ; surrogate is not a char
(%check :utf8 (and (equal ($utf8 '(97)) '(97))
                   (equal ($utf8 '(955)) '(#xCE #xBB))
                   (equal ($utf8 '(#x1F600)) '(#xF0 #x9F #x98 #x80))))

; type families indexed by a value: val_(valtype)
(%check :val_ (and (val_-p 7 '(:i32)) (val_-p '(:pos (:inf)) '(:f64))
                   (not (val_-p '(:pos (:inf)) '(:i32)))))

; instructions (plan T2 exit criterion). loadop_ is mixop "%_%" -> tag :_
(%check :instr (and (instr-p '(:const (:i32) 7))
                    (not (instr-p '(:const (:i32) -1)))
                    (instr-p '(:block nil ((:nop) (:const (:i64) 0) (:drop))))
                    (instr-p '(:loop ((:i32)) ((:br 0))))
                    (instr-p '(:binop (:i32) (:div (:s))))
                    (not (instr-p '(:binop (:i32) (:copysign))))     ; float-only op
                    (instr-p '(:load (:i32) ((:_ 8 (:u))) (:%rec (:align . 0) (:offset . 0))))
                    (not (instr-p '(:load (:i32) ((:_ 32 (:u))) (:%rec (:align . 0) (:offset . 0)))))
                    ; STORE: the Inn? premise output (?-iteration with outputs)
                    (instr-p '(:store (:i64) (32) (:%rec (:align . 0) (:offset . 0))))
                    (not (instr-p '(:store (:i32) (32) (:%rec (:align . 0) (:offset . 0)))))
                    (not (instr-p '(:store (:f32) (8) (:%rec (:align . 0) (:offset . 0)))))
                    (not (instr-p '(:frob)))))

; generated functions
(%check :size (and (equal ($size '(:i32)) 32) (equal ($size '(:f64)) 64)))
(%check :signed (and (equal ($signed_ 8 255) -1) (equal ($signed_ 8 127) 127)
                     (equal ($inv_signed_ 8 -1) 255)))

; everything generated was admitted in logic mode (no :program fallback)
(%check :logic-mode
        (and (acl2::logicp 'instr-p (acl2::w state)) (acl2::logicp '$size (acl2::w state))
             (acl2::logicp 'fn-p (acl2::w state))))
