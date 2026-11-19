; License: MIT. See the file LICENSE at the top of the repository.
;
; E7 Phase B, the fast paths: when FAST-HOT-STEP handles an instruction
; (local.get, local.set, local.tee, binop, relop, br_if), the state it gives
; is the state the general path (FAST-OP-STEP) gives. And the value test of
; FAST-STEP (FAST-VAL-P) is VALUE-INSTR-P.
(in-package "WE")
(include-book "fast")

(defthm fast-val-p-is-val-p
  (equal (fast-val-p v) (and (consp v) (w3t::val-p v) t))
  :hints (("Goal" :use i32-const-p-is-val-p :in-theory (disable i32-const-p-is-val-p w3t::val-p))))

(defthm fast-val-p-is-value-instr-p
  (equal (fast-val-p v) (value-instr-p v))
  :hints (("Goal" :in-theory (disable w3t::val-p))))

; --- the stobj as a list ---------------------------------------------------

(defthm update-nth-same-value
  (implies (< (nfix n) (len l)) (equal (update-nth n (nth n l) l) l)))

(defthm update-nth-update-nth-diff
  (implies (and (natp a) (natp b) (< a b))
           (equal (update-nth b y (update-nth a x l)) (update-nth a x (update-nth b y l)))))

(defthm update-nth-update-nth-same
  (equal (update-nth a y (update-nth a x l)) (update-nth a y l)))

(defthm update-nth-known-value-under
  (implies (and (equal (nth a l) x) (not (equal (nfix a) (nfix b))) (< (nfix a) (len l)))
           (equal (update-nth a x (update-nth b v l)) (update-nth b v l))))

(defthm update-nth-known-value
  (implies (and (equal (nth a l) x) (< (nfix a) (len l)))
           (equal (update-nth a x l) l)))

; --- list helpers of the machine --------------------------------------------

(defthm take-n-open
  (implies (and (not (zp n)) (consp l)) (equal (take-n n l) (cons (car l) (take-n (1- n) (cdr l))))))
(defthm take-n-zero (implies (zp n) (equal (take-n n l) nil)))
(defthm rev-onto-cons (equal (rev-onto (cons a l) acc) (rev-onto l (cons a acc))))
(defthm rev-onto-nil (equal (rev-onto nil acc) acc))
(defthm drop-n-open
  (implies (and (not (zp n)) (consp l)) (equal (drop-n n l) (drop-n (1- n) (cdr l)))))
(defthm drop-n-zero (implies (zp n) (equal (drop-n n l) l)))
(defthm len-pos-when-consp (implies (consp x) (< 0 (len x))) :rule-classes (:linear :rewrite))

; --- each fast path equals the general path --------------------------------

(defmacro hot-thm (name kw rules)
  `(defthm ,name
     (implies (and (fmp fm) (equal (fm-status fm) :run)
                   (consp (fm-is fm)) (equal (car (fm-is fm)) i) (equal (car i) ,kw)
                   (mv-nth 0 (fast-hot-step i fm)))
              (equal (mv-nth 1 (fast-hot-step i fm)) (fast-op-step fm)))
     :hints (("Goal" :in-theory (e/d ,rules (w3t::val-p fast-val-p w3t::$binop_ w3t::$relop_ w3t::$with_local))
                     :do-not-induct t))))

(hot-thm hot-local.get :local.get (w3t::step_read/split/r-local.get))
(hot-thm hot-local.set :local.set (w3t::step/r-local.set))
(hot-thm hot-local.tee :local.tee (w3t::step_pure/r-local.tee))
(hot-thm hot-binop :binop (w3t::step_pure/r-binop-val w3t::step_pure/r-binop-trap))
(hot-thm hot-relop :relop (w3t::step_pure/r-relop))
(hot-thm hot-br_if :br_if (w3t::step_pure/r-br_if-true w3t::step_pure/r-br_if-false))
