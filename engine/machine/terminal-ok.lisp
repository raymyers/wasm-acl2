; License: MIT. See the file LICENSE at the top of the repository.
;
; Constraint C3 of E3 for the list machine: a machine state with a result
; (:done, :trap, :throw) and the invariant abstracts to a configuration
; that the specification does not step. From the facts about the spec in
; ../rules/terminal.lisp and the shape that MACHINE-OK ties to each result
; status.
(in-package "WE")
(include-book "ok")
(include-book "../rules/terminal")

(defthm vals-p-of-rev-onto
  (implies (and (val-list-p a) (vals-p b)) (vals-p (rev-onto a b))))

(local (defthm true-list-of-len-1
  (implies (and (true-listp x) (equal (len x) 1)) (equal (list (car x)) x))))

(defthm exn-value-shape
  (implies (and (w3t::val-p v) (equal (car v) :ref.exn_addr))
           (equal v (list :ref.exn_addr (cadr v))))
  :hints (("Goal" :in-theory (enable w3t::val-p)))
  :rule-classes nil)

(defthm machine-abs-of-empty-ctrl
  (implies (atom (ms-ctrl s))
           (equal (machine-abs s)
                  (list :|%;%| (list :|%;%| (ms-store s) (ms-frame s))
                        (rev-onto (ms-vals s) (ms-is s)))))
  :hints (("Goal" :in-theory (enable machine-abs abs-ctrl))))

(defthm status-ok-of-machine-ok
  (implies (machine-ok s) (status-ok (ms-status s) (ms-vals s) (ms-is s) (ms-ctrl s)))
  :hints (("Goal" :in-theory (enable machine-ok))))

(local (in-theory (disable w3t::step machine-ok machine-abs)))

(defthm status-ok-done
  (implies (and (true-listp is) (status-ok :done vals is ctrl))
           (and (equal is nil) (atom ctrl)))
  :rule-classes nil)

(defthm status-ok-trap
  (implies (status-ok :trap vals is ctrl)
           (and (equal is '((:trap))) (atom vals) (atom ctrl)))
  :rule-classes nil)

(defthm status-ok-throw
  (implies (status-ok :throw vals is ctrl)
           (and (equal is '((:throw_ref))) (consp vals) (atom (cdr vals))
                (equal (car (car vals)) :ref.exn_addr) (atom ctrl)))
  :hints (("Goal" :in-theory (enable entry-kind)))
  :rule-classes nil)

(defthm val-list-p-car
  (implies (and (val-list-p l) (consp l)) (w3t::val-p (car l)))
  :hints (("Goal" :in-theory (enable value-instr-p))))

(defthm machine-done-is-terminal
  (implies (and (machine-ok s) (equal (ms-status s) :done))
           (not (w3t::step (machine-abs s))))
  :hints (("Goal" :use ((:instance status-ok-of-machine-ok)
                        (:instance status-ok-done (vals (ms-vals s)) (is (ms-is s)) (ctrl (ms-ctrl s)))
                        (:instance step-of-vals (z (list :|%;%| (ms-store s) (ms-frame s)))
                                   (l (rev-onto (ms-vals s) nil)))))))

(defthm machine-trap-is-terminal
  (implies (and (machine-ok s) (equal (ms-status s) :trap))
           (not (w3t::step (machine-abs s))))
  :hints (("Goal" :use ((:instance status-ok-of-machine-ok)
                        (:instance status-ok-trap (vals (ms-vals s)) (is (ms-is s)) (ctrl (ms-ctrl s)))
                        (:instance step-of-trap-alone (z (list :|%;%| (ms-store s) (ms-frame s)))))
                  :in-theory (disable step-of-trap-alone))))

(defthm machine-throw-is-terminal
  (implies (and (machine-ok s) (equal (ms-status s) :throw))
           (not (w3t::step (machine-abs s))))
  :hints (("Goal" :use ((:instance status-ok-of-machine-ok)
                        (:instance status-ok-throw (vals (ms-vals s)) (is (ms-is s)) (ctrl (ms-ctrl s)))
                        (:instance exn-value-shape (v (car (ms-vals s))))
                        (:instance step-of-uncaught-exception
                                   (z (list :|%;%| (ms-store s) (ms-frame s)))
                                   (a (cadr (car (ms-vals s))))))
                  :in-theory (disable step-of-uncaught-exception))))

; C3 of E3 for the list machine
(defthm machine-result-is-terminal
  (implies (and (machine-ok s) (machine-result-p s))
           (not (w3t::step (machine-abs s))))
  :hints (("Goal" :in-theory (enable machine-result-p))))
