; License: MIT. See the file LICENSE at the top of the repository.
;
; The invariant of the list machine and constraint C1 of E3 for it: a step
; keeps the invariant (plan/wasm-engine E6 item 2). The invariant is the
; one of notes/E5-machine.md: the operand stacks are true lists of values,
; the instruction lists are true lists, and every control entry has one of
; the three shapes with a natural arity. Nothing about types.
(in-package "WE")
(include-book "machine")

(defun val-list-p (l)
  (declare (xargs :guard t))
  (if (atom l) (null l) (and (value-instr-p (car l)) (val-list-p (cdr l)))))

(defun entry-ok (e)
  (declare (xargs :guard t))
  (and (true-listp e) (equal (len-t e) 5)
       (sym-member (entry-kind e) '(:l :h :f))
       (natp (entry-n e))
       (or (not (eq (entry-kind e) :l)) (true-listp (entry-x e)))
       (val-list-p (entry-v e))
       (true-listp (entry-r e))))

(defun ctrl-ok (c)
  (declare (xargs :guard t))
  (if (atom c) (null c) (and (entry-ok (car c)) (ctrl-ok (cdr c)))))

; A result status goes with the shape of the configuration that is the
; result, which constraint C3 needs: values alone, TRAP alone, or an
; exception reference and THROW_REF, each with no control entry.
(defun status-ok (status vals is ctrl)
  (declare (xargs :guard t))
  (case status
    (:done (and (atom is) (atom ctrl)))
    (:trap (and (equal is '((:trap))) (atom vals) (atom ctrl)))
    (:throw (and (equal is '((:throw_ref))) (consp vals) (atom (cdr vals))
                 (eq (entry-kind (car vals)) :ref.exn_addr) (atom ctrl)))
    (otherwise t)))

(defun machine-ok (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len-t s) 6)
       (val-list-p (ms-vals s))
       (true-listp (ms-is s))
       (ctrl-ok (ms-ctrl s))
       (status-ok (ms-status s) (ms-vals s) (ms-is s) (ms-ctrl s))))

; --- lemmas ---------------------------------------------------------------

(defthm val-list-p-true-listp
  (implies (val-list-p l) (true-listp l))
  :rule-classes :forward-chaining)

(defthm val-list-p-drop-n
  (implies (val-list-p l) (val-list-p (drop-n n l))))

(defthm true-listp-app
  (equal (true-listp (app a b)) (true-listp b)))

(defthm true-listp-drop-n
  (implies (true-listp l) (true-listp (drop-n n l))))

(defthm len-t-is-len
  (equal (len-t l) (len l)))

(defthm machine-ok-of-ms
  (equal (machine-ok (ms store frame vals is ctrl status))
         (and (val-list-p vals) (true-listp is) (ctrl-ok ctrl) (status-ok status vals is ctrl)))
  :hints (("Goal" :in-theory (enable ms))))

(defthm ms-accessors
  (and (equal (ms-store (ms store frame vals is ctrl status)) store)
       (equal (ms-frame (ms store frame vals is ctrl status)) frame)
       (equal (ms-vals (ms store frame vals is ctrl status)) vals)
       (equal (ms-is (ms store frame vals is ctrl status)) is)
       (equal (ms-ctrl (ms store frame vals is ctrl status)) ctrl)
       (equal (ms-status (ms store frame vals is ctrl status)) status)))

(in-theory (disable ms ms-store ms-frame ms-vals ms-is ms-ctrl ms-status machine-ok))

(defthm machine-ok-of-ms-with-status
  (implies (and (machine-ok s) (status-ok st (ms-vals s) (ms-is s) (ms-ctrl s)))
           (machine-ok (ms-with-status st s)))
  :hints (("Goal" :in-theory (enable machine-ok ms-with-status ms ms-vals ms-is ms-ctrl
                                     ms-store ms-frame ms-status))))

(in-theory (disable ms-with-status))

(defthm machine-ok-forward
  (implies (machine-ok s)
           (and (val-list-p (ms-vals s)) (true-listp (ms-is s)) (ctrl-ok (ms-ctrl s))
                (status-ok (ms-status s) (ms-vals s) (ms-is s) (ms-ctrl s))))
  :hints (("Goal" :in-theory (enable machine-ok)))
  :rule-classes :forward-chaining)

(defthm entry-accessors-of-list
  (and (equal (entry-kind (list k n x v r)) k)
       (equal (entry-n (list k n x v r)) n)
       (equal (entry-x (list k n x v r)) x)
       (equal (entry-v (list k n x v r)) v)
       (equal (entry-r (list k n x v r)) r)))

(defthm entry-of-car-ctrl
  (implies (and (ctrl-ok c) (consp c))
           (and (entry-ok (car c))
                (val-list-p (entry-v (car c)))
                (true-listp (entry-r (car c)))
                (natp (entry-n (car c)))
                (implies (equal (entry-kind (car c)) :l) (true-listp (entry-x (car c)))))))

(in-theory (disable entry-kind entry-n entry-x entry-v entry-r))

(defthm ctrl-ok-atom
  (implies (and (ctrl-ok c) (not (consp c))) (equal c nil))
  :rule-classes :forward-chaining)

(defthm ctrl-ok-cdr
  (implies (ctrl-ok c) (ctrl-ok (cdr c))))

(local (in-theory (disable try-rules)))

(defthm enter-step-ok
  (implies (machine-ok s) (machine-ok (enter-step s))))

(defthm exit-step-ok
  (implies (and (machine-ok s) (consp (ms-ctrl s))) (machine-ok (exit-step s))))

(defthm anyprefix-step-ok
  (implies (machine-ok s) (machine-ok (anyprefix-step s))))

(defthm op-step-ok
  (implies (machine-ok s) (machine-ok (op-step s)))
  :hints (("Goal" :in-theory (disable redex-arity drop-n take-n rev-onto app))))

(in-theory (disable enter-step exit-step anyprefix-step op-step))

; C1 of E3 for the list machine
(defthm machine-step-preserves-ok
  (implies (and (machine-ok s) (machine-running s))
           (machine-ok (machine-step s))))
