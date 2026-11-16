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
