; License: MIT. See the file LICENSE at the top of the repository.
;
; E7, part 2 of the design in notes/E6-list-machine.md: the memory rules
; as functions of what the stobj machine can read from its byte array.
; First lemmas: a load reads only its window, and the bounds rule depends
; only on the memory's length (with one memory, which MuPDF has).
(in-package "WE")
(include-book "frame")

; The load rule with the byte window as a parameter: what the stobj
; machine computes after reading N bytes at ADDR from its array.
(defun load-num-val-of-window (l win)
  (and (true-listp l) (equal (len l) 2)
       (let ((c0 (car l)) (ld (cadr l)))
         (and (consp c0) (eq (car c0) :const) (true-listp (cdr c0)) (equal (len (cdr c0)) 2)
              (w3t::addrtype-p (cadr c0))
              (consp ld) (eq (car ld) :load) (true-listp (cdr ld)) (equal (len (cdr ld)) 4)
              (null (caddr ld))
              (let* ((nt (cadr ld)) (c (w3t::$inv_nbytes_ nt win)))
                (and (equal (w3t::$nbytes_ nt c) win)
                     (list (list (list :const nt c)))))))))

(defun load-window (z l)                ; the bytes the load rule reads
  (let* ((c0 (car l)) (ld (cadr l)) (nt (cadr ld)) (x (cadddr ld)) (ao (car (cddddr ld))))
    (take (/ (w3t::$size nt) 8)
          (nthcdr (+ (caddr c0) (wrt::%get-field ao :offset))
                  (wrt::%get-field (w3t::$mem z x) :bytes)))))

(defthm load-num-val-is-window
  (equal (w3t::step_read/split/r-load-num-val (list :|%;%| z l))
         (load-num-val-of-window l (load-window z l)))
  :hints (("Goal" :in-theory (enable w3t::step_read/split/r-load-num-val))))

; One memory: the store has one, and the instruction's memory index maps
; to it.
(defun single-memory-p (z l)
  (and (consp (wrt::%get-field (cadr z) :mems))
       (atom (cdr (wrt::%get-field (cadr z) :mems)))
       (equal (nth (cadddr (cadr l)) (wrt::%get-field (wrt::%get-field (caddr z) :module) :mems)) 0)))

(defthm load-num-oob-depends-on-length
  (implies (and (equal (len b1) (len b2))
                (single-memory-p z l) (true-listp z) (equal (len z) 3))
           (equal (w3t::step_read/split/r-load-num-oob (list :|%;%| (put-z-bytes z b1) l))
                  (w3t::step_read/split/r-load-num-oob (list :|%;%| (put-z-bytes z b2) l))))
  :hints (("Goal" :in-theory (enable w3t::step_read/split/r-load-num-oob) :do-not-induct t)))

; The store rule writes a splice of the byte list: the same as the rule on
; a store with no bytes, with the splice of the real bytes put back. The
; stobj machine writes the N new bytes into the array at ADDR.
(defun store-splice (l b)                ; l = (const at i) (const nt c) (store nt nil x ao)
  (let* ((i (caddr (car l))) (st (caddr l)) (nt (cadr st)) (c (caddr (cadr l)))
         (addr (+ i (wrt::%get-field (car (cddddr st)) :offset))))
    (append (take addr b) (w3t::$nbytes_ nt c) (nthcdr (+ addr (/ (w3t::$size nt) 8)) b))))

(defun single-memory-store-p (z l)       ; as SINGLE-MEMORY-P, for the store's position
  (and (consp (wrt::%get-field (cadr z) :mems))
       (atom (cdr (wrt::%get-field (cadr z) :mems)))
       (equal (nth (cadddr (caddr l)) (wrt::%get-field (wrt::%get-field (caddr z) :module) :mems)) 0)))

(defthm store-num-val-is-splice
  (implies (and (single-memory-store-p z l) (true-listp z) (equal (len z) 3) (store-fields-p (cadr z)))
           (equal (w3t::step/r-store-num-val (list :|%;%| (put-z-bytes z b) l))
                  (put-result-bytes (w3t::step/r-store-num-val (list :|%;%| (put-z-bytes z nil) l))
                                    (store-splice l b))))
  :hints (("Goal" :in-theory (enable w3t::step/r-store-num-val) :do-not-induct t)))

; One memory, for the whole state: the store has one memory and every
; memory index of the current module is 0.
(defun all-zero-p (l)
  (if (atom l) t (and (equal (car l) 0) (all-zero-p (cdr l)))))

(defun one-memory-p (z)
  (and (consp (wrt::%get-field (cadr z) :mems))
       (atom (cdr (wrt::%get-field (cadr z) :mems)))
       (all-zero-p (wrt::%get-field (wrt::%get-field (caddr z) :module) :mems))))

(defthm nth-of-all-zero
  (implies (all-zero-p l) (equal (nth k l) (if (< (nfix k) (len l)) 0 nil))))

(defthm nth-of-one-element
  (equal (nth k (list x)) (if (zp k) x nil)))

; The bounds rules and memory.size read only the memory's length.
(defun length-lemma (fn)
  (declare (xargs :mode :program))
  (let ((name (intern-in-package-of-symbol
               (concatenate 'string (symbol-name fn) "-DEPENDS-ON-LENGTH") 'we::here)))
    `(make-event
      '(:or (defthm ,name
              ,(if (eq (rule-kind fn) :step)
                   ; a step rule's result holds the store: its bytes are the input's
                   `(implies (and (equal (len b1) (len b2)) (one-memory-p z) (true-listp z) (equal (len z) 3)
                                  (store-fields-p (cadr z)))
                             (equal (,fn (list :|%;%| (put-z-bytes z b1) l))
                                    (put-result-bytes (,fn (list :|%;%| (put-z-bytes z b2) l)) b1)))
                 `(implies (and (equal (len b1) (len b2)) (one-memory-p z) (true-listp z) (equal (len z) 3))
                           (equal (,fn (list :|%;%| (put-z-bytes z b1) l))
                                  (,fn (list :|%;%| (put-z-bytes z b2) l)))))
              :hints (("Goal" :in-theory (enable ,fn) :do-not-induct t)))
            (value-triple (cw "LENGTH-FAILED ~x0~%" ',fn))))))

(defun length-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (length-lemma (car fns)) (length-lemmas (cdr fns)))))

(make-event
 `(progn ,@(length-lemmas '(w3t::step_read/split/r-load-pack-oob w3t::step/r-store-num-oob
                            w3t::step/r-store-pack-oob w3t::step_read/split/r-memory.size
                            ; memory.fill and memory.copy expand into loads, stores and a
                            ; smaller fill or copy: they read only the length
                            w3t::step_read/split/r-memory.fill-oob w3t::step_read/split/r-memory.fill-zero
                            w3t::step_read/split/r-memory.fill-succ
                            w3t::step_read/split/r-memory.copy-oob w3t::step_read/split/r-memory.copy-zero
                            w3t::step_read/split/r-memory.copy-le w3t::step_read/split/r-memory.copy-gt))))

; The packed load reads only its window: two byte lists that agree on it
; give the same result. l = (const at i) (load inn ((:_ n sx)) x ao).
(defun pack-load-addr (l)
  (+ (caddr (car l)) (wrt::%get-field (car (cddddr (cadr l))) :offset)))
(defun pack-load-size (l)
  (/ (cadr (car (caddr (cadr l)))) 8))

(defthm load-pack-val-reads-its-window
  (implies (and (one-memory-p z) (true-listp z) (equal (len z) 3)
                (equal (take (pack-load-size l) (nthcdr (pack-load-addr l) b1))
                       (take (pack-load-size l) (nthcdr (pack-load-addr l) b2))))
           (equal (w3t::step_read/split/r-load-pack-val (list :|%;%| (put-z-bytes z b1) l))
                  (w3t::step_read/split/r-load-pack-val (list :|%;%| (put-z-bytes z b2) l))))
  :hints (("Goal" :in-theory (enable w3t::step_read/split/r-load-pack-val) :do-not-induct t)))

; The packed store writes a splice too: l = (const at i) (const inn c) (store inn (n) x ao).
(defun store-pack-splice (l b)
  (let* ((i (caddr (car l))) (st (caddr l)) (inn (cadr st)) (n (car (caddr st)))
         (c (caddr (cadr l)))
         (addr (+ i (wrt::%get-field (car (cddddr st)) :offset))))
    (append (take addr b)
            (w3t::$ibytes_ n (w3t::$wrap__ (w3t::$size inn) n c))
            (nthcdr (+ addr (/ n 8)) b))))

(defthm store-pack-val-is-splice
  (implies (and (single-memory-store-p z l) (true-listp z) (equal (len z) 3) (store-fields-p (cadr z)))
           (equal (w3t::step/r-store-pack-val (list :|%;%| (put-z-bytes z b) l))
                  (put-result-bytes (w3t::step/r-store-pack-val (list :|%;%| (put-z-bytes z nil) l))
                                    (store-pack-splice l b))))
  :hints (("Goal" :in-theory (enable w3t::step/r-store-pack-val) :do-not-induct t)))
