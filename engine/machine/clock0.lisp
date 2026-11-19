; License: MIT. See the file LICENSE at the top of the repository.
;
; Constraint C2 of E3 for the clock-0 steps of the list machine (plan E11,
; S0 and every group): a step whose clock is 0 leaves MACHINE-ABS
; unchanged. These are the steps that move a value to the operand stack,
; enter a LABEL_, HANDLER_ or FRAME_ term, or stop the machine. With
; (stepn 0 c) = (list c), this is C2 for them. No fact about the
; specification is used.
(in-package "WE")
(include-book "ok")
(include-book "../theorem/simulation")

(local (in-theory (disable try-rules apply-rule redex-arity)))

(defthm abs-ctrl-of-cons-entry
  (equal (abs-ctrl (cons e ctrl) cur fr)
         (abs-ctrl ctrl
                   (rev-onto (entry-v e)
                             (cons (admin-term (entry-kind e) (entry-n e)
                                               (if (eq (entry-kind e) :f) fr (entry-x e)) cur)
                                   (entry-r e)))
                   (if (eq (entry-kind e) :f) (entry-x e) fr)))
  :hints (("Goal" :expand ((abs-ctrl (cons e ctrl) cur fr)))))

(defthm rev-onto-of-cons
  (equal (rev-onto (cons a l) acc) (rev-onto l (cons a acc))))

(defthm machine-abs-of-ms-with-status
  (equal (machine-abs (ms-with-status st s)) (machine-abs s))
  :hints (("Goal" :in-theory (enable machine-abs ms-with-status))))

; pushing a value: rev(vals) ++ is is unchanged
(defthm machine-abs-of-value-push
  (implies (consp (ms-is s))
           (equal (machine-abs (ms (ms-store s) (ms-frame s) (cons (car (ms-is s)) (ms-vals s))
                                   (cdr (ms-is s)) (ms-ctrl s) st))
                  (machine-abs s)))
  :hints (("Goal" :in-theory (enable machine-abs))))

(defthm rebuild-4-list
  (implies (and (true-listp i) (equal (len i) 4) (equal (car i) k))
           (equal (list k (car-t (drop-n 1 i)) (car-t (drop-n 2 i)) (car-t (drop-n 3 i))) i))
  :hints (("Goal" :expand ((drop-n 1 i) (drop-n 2 i) (drop-n 3 i) (drop-n 2 (cdr i))
                           (drop-n 1 (cdr i)) (drop-n 1 (cddr i))))))

(defthm car-t-of-consp
  (implies (consp x) (equal (car-t x) (car x))))

(defthm cons-car-cdr-of-consp
  (implies (consp x) (equal (cons (car x) (cdr x)) x)))

; entering an administrative term: the entry rebuilds exactly that term
(defthm machine-abs-of-enter-step
  (implies (and (consp (ms-is s)) (enterable-p (car (ms-is s))))
           (equal (machine-abs (enter-step s)) (machine-abs s)))
  :hints (("Goal" :in-theory (e/d (machine-abs enter-step enterable-p admin-term admin-kind
                                     entry-kind entry-n entry-x entry-v entry-r)
                                  (car-t)))))

; a step that does not keep running only changed the status
(defthm op-step-stopped-keeps-abs
  (implies (not (equal (ms-status (op-step s)) :run))
           (equal (machine-abs (op-step s)) (machine-abs s)))
  :hints (("Goal" :in-theory (enable op-step))))

(defthm exit-step-stopped-keeps-abs
  (implies (not (equal (ms-status (exit-step s)) :run))
           (equal (machine-abs (exit-step s)) (machine-abs s)))
  :hints (("Goal" :in-theory (enable exit-step))))

(defthm anyprefix-step-stopped-keeps-abs
  (implies (not (equal (ms-status (anyprefix-step s)) :run))
           (equal (machine-abs (anyprefix-step s)) (machine-abs s)))
  :hints (("Goal" :in-theory (enable anyprefix-step))))

(defthm enter-step-not-enterable
  (implies (not (enterable-p (car-t (ms-is s))))
           (equal (enter-step s) (ms-with-status :stuck s)))
  :hints (("Goal" :in-theory (enable enter-step))))

(defthm enter-step-keeps-abs
  (implies (consp (ms-is s))
           (equal (machine-abs (enter-step s)) (machine-abs s)))
  :hints (("Goal" :cases ((enterable-p (car (ms-is s))))
                  :in-theory (disable enter-step enterable-p))))

(defthm value-instr-head
  (implies (value-instr-p i)
           (member-equal (entry-kind i)
                         '(:const :vconst :ref.null_addr :ref.i31_num :ref.struct_addr :ref.array_addr
                           :ref.func_addr :ref.exn_addr :ref.host_addr :ref.extern)))
  :hints (("Goal" :in-theory (enable value-instr-p w3t::val-p entry-kind)))
  :rule-classes nil)

(defthm value-instr-not-head
  (implies (and (value-instr-p i) (syntaxp (quotep k))
                (not (member-equal k '(:const :vconst :ref.null_addr :ref.i31_num :ref.struct_addr
                                       :ref.array_addr :ref.func_addr :ref.exn_addr :ref.host_addr
                                       :ref.extern))))
           (and (not (equal (entry-kind i) k)) (not (equal k (entry-kind i)))))
  :hints (("Goal" :use value-instr-head)))

(defthm list-car-of-one-element
  (implies (and (consp x) (not (consp (cdr x))) (true-listp x))
           (equal (list (car x)) x)))

; MACHINE-ABS as a function of the five parts of a state
(defun abs-of (store frame vals is ctrl)
  (mv-let (instrs fr) (abs-ctrl ctrl (rev-onto vals is) frame)
    (list :|%;%| (list :|%;%| store fr) instrs)))

(defthm machine-abs-of-ms
  (equal (machine-abs (ms store frame vals is ctrl st)) (abs-of store frame vals is ctrl))
  :hints (("Goal" :in-theory (enable machine-abs))))

(defthm machine-abs-of-state-variable
  (implies (syntaxp (symbolp s))
           (equal (machine-abs s) (abs-of (ms-store s) (ms-frame s) (ms-vals s) (ms-is s) (ms-ctrl s))))
  :hints (("Goal" :in-theory (enable machine-abs))))

(in-theory (disable op-step exit-step anyprefix-step enter-step value-instr-p
                    ms-with-status machine-abs))

; C2 for the clock-0 steps
(defthm machine-clock-0-keeps-abs
  (implies (and (machine-ok s) (machine-running s) (equal (machine-clock s) 0))
           (equal (machine-abs (machine-step s)) (machine-abs s)))
  :hints (("Goal" :in-theory (enable machine-step machine-clock machine-running))))

(defthm machine-clock-0-simulates
  (implies (and (machine-ok s) (machine-running s) (equal (machine-clock s) 0))
           (equal (stepn (machine-clock s) (machine-abs s))
                  (list (machine-abs (machine-step s))))))
