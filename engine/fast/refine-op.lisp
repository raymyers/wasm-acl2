; License: MIT. See the file LICENSE at the top of the repository.
;
; E7 Phase B, layer 4: the step theorem.
;   FAST-STEP-REFINES: one step of the fast machine, seen through FM->MS, is
;   one step of the list machine (MACHINE-STEP), when
;     - the stobj is well formed (FMP) and its store is the fast store
;       (FAST-INV-STORE: memory 0 a record without its bytes, all fields);
;     - every control entry is a label, a handler or a frame (CTRL-KINDS-OK);
;     - the instruction is not call_ref (its two host-call rules have no
;       lemma: refine-step.lisp, *U-NOT-YET*);
;     - the fast step does not stop :unsupported (an opcode without rules, or
;       a fallback result the fast machine cannot hold).
; Not here: that a step keeps FMP, FAST-INV-STORE and CTRL-KINDS-OK (needed to
; chain steps into a run), and FM-LOAD-MS.
(in-package "WE")
(include-book "refine-step")
(include-book "refine-hot")
(set-prover-step-limit 20000000)        ; a runaway proof stops instead of running for hours

; --- a rule application and the array ---------------------------------------
; the array stays a byte list, and no other field of the stobj changes

(defthm byte-list-p-of-update-nth
  (implies (and (byte-list-p l) (natp i) (< i (len l)) (natp v) (< v 256))
           (byte-list-p (update-nth i v l))))
(defthm byte-list-p-of-mem-write
  (implies (byte-list-p (nth *fm-memi* fm))
           (byte-list-p (nth *fm-memi* (mem-write i b fm))))
  :hints (("Goal" :induct (mem-write i b fm))))
(defthm fast-apply-fallback-keeps-bytes
  (implies (byte-list-p (nth *fm-memi* fm))
           (byte-list-p (nth *fm-memi* (cadddr (fast-apply-fallback fn z redex fm)))))
  :hints (("Goal" :in-theory (e/d (fast-apply-fallback) (apply-rule list-to-mem put-z-bytes mem-to-list)))))
(defthm fast-apply-rule-keeps-bytes
  (implies (byte-list-p (nth *fm-memi* fm))
           (byte-list-p (nth *fm-memi* (cadddr (fast-apply-rule fn z redex fm)))))
  :hints (("Goal" :in-theory (e/d (fast-apply-rule) (apply-rule fast-apply-fallback fast-memory-rule mem-write
                                                     rule-may-match fast-one-memory-p sym-member frame-safe-p mem-write-array)))))
(defthm fast-try-rules-keeps-bytes
  (implies (byte-list-p (nth *fm-memi* fm))
           (byte-list-p (nth *fm-memi* (cadddr (fast-try-rules rules z redex fm)))))
  :hints (("Goal" :induct (fast-try-rules rules z redex fm) :in-theory (disable fast-apply-rule))))
(defthm mem-write-other
  (implies (not (equal k *fm-memi*))
           (equal (nth k (mem-write i b fm)) (nth k fm)))
  :hints (("Goal" :induct (mem-write i b fm))))
(defthm fast-apply-fallback-other
  (implies (not (equal k *fm-memi*))
           (equal (nth k (cadddr (fast-apply-fallback fn z redex fm))) (nth k fm)))
  :hints (("Goal" :in-theory (e/d (fast-apply-fallback) (apply-rule list-to-mem put-z-bytes mem-to-list nth)))))
(defthm fast-apply-rule-other
  (implies (not (equal k *fm-memi*))
           (equal (nth k (cadddr (fast-apply-rule fn z redex fm))) (nth k fm)))
  :hints (("Goal" :in-theory (e/d (fast-apply-rule) (apply-rule fast-apply-fallback fast-memory-rule mem-write nth
                                                     rule-may-match fast-one-memory-p sym-member frame-safe-p mem-write-array)))))
(defthm fast-try-rules-other
  (implies (not (equal k *fm-memi*))
           (equal (nth k (cadddr (fast-try-rules rules z redex fm))) (nth k fm)))
  :hints (("Goal" :induct (fast-try-rules rules z redex fm) :in-theory (disable fast-apply-rule nth))))
(defthm mem-to-list-of-bytes
  (implies (byte-list-p (nth *fm-memi* fm)) (equal (mem-to-list fm) (nth *fm-memi* fm))))

; --- the stobj as a list state; the op step ---------------------------------

(defthm fast-try-op-is-try-rules
  (implies (and (op-has-rules kw) (not (equal kw :call_ref)))
           (equal (fast-try-op kw z redex fm)
                  (fast-try-rules (rules-for (list :op kw)) z redex fm)))
  :hints (("Goal" :in-theory (e/d (fast-try-op op-has-rules rules-for) (fast-try-rules)))))
(defthm all-u-holds-of-op
  (implies (and (op-has-rules kw) (not (equal kw :call_ref)))
           (all-u-holds (rules-for (list :op kw)) s f redex fm))
  :hints (("Goal" :in-theory (e/d (op-has-rules rules-for) (all-u-holds)))))
(defthm fm-memp-is-byte-list-p
  (implies (fm-memp l) (byte-list-p l)))
(defthm fmp-gives-bytes
  (implies (fmp fm) (byte-list-p (nth *fm-memi* fm))))
(defthm fm->ms-of-update-fm-status
  (equal (fm->ms (update-fm-status st fm)) (ms-with-status st (fm->ms fm)))
  :hints (("Goal" :in-theory (enable fm->ms ms-with-status))))
(defthm fm->ms-of-fm-set
  (implies (byte-list-p (nth *fm-memi* fm))
           (equal (fm->ms (fm-set s f v is c st fm))
                  (ms (put-mem0-bytes s (nth *fm-memi* fm)) f v is c st)))
  :hints (("Goal" :in-theory (e/d (fm->ms fm-set) (put-mem0-bytes)))))
(defthm car-t-is-car (equal (car-t x) (car x)) :hints (("Goal" :in-theory (enable car-t))))
(defthm cdr-t-is-cdr (equal (cdr-t x) (cdr x)) :hints (("Goal" :in-theory (enable cdr-t))))
(defthm car-drop-n-is-cadr
  (and (equal (car (drop-n 1 x)) (cadr x))
       (equal (car (drop-n 2 x)) (caddr x)))
  :hints (("Goal" :expand ((drop-n 1 x) (drop-n 2 x) (drop-n 1 (cdr x))))))
(defthm redex-arity-full-is-fast-inv
  (implies (fast-inv-store s)
           (equal (redex-arity i (list :|%;%| (put-mem0-bytes s b) f) vals)
                  (redex-arity i (list :|%;%| s f) vals)))
  :hints (("Goal" :in-theory (disable redex-arity put-mem0-bytes fast-store-ok mem0-record-p))))
(in-theory (disable fm->ms-of-update-fm-status))
(defthm fast-op-step-refines
  (implies (and (fmp fm) (fast-inv-store (fm-store fm))
                (not (equal (entry-kind (car (fm-is fm))) :call_ref))
                (not (equal (fm-status (fast-op-step fm)) :unsupported)))
           (equal (fm->ms (fast-op-step fm)) (op-step (fm->ms fm))))
  :hints (("Goal" :in-theory (e/d (fast-op-step op-step fm->ms ms-z fm-z fm->ms-of-update-fm-status put-z-bytes)
                                  (fast-try-op fast-try-rules try-rules apply-rule fast-apply-rule
                                   put-mem0-bytes op-has-rules rules-for all-u-holds
                                   entry-kind redex-arity fm-set fmp fast-inv-store fast-try-rules-refines
                                   take-n drop-n rev-onto app mem-to-list))
                  :use ((:instance fast-try-rules-refines
                                   (rules (rules-for (list :op (entry-kind (car (fm-is fm))))))
                                   (s (fm-store fm)) (f (fm-frame fm))
                                   (redex (rev-onto (take-n (redex-arity (car (fm-is fm)) (fm-z fm) (fm-vals fm))
                                                            (fm-vals fm))
                                                    (list (car (fm-is fm)))))))
                  :do-not-induct t)))

; --- control entries, trap/throw propagation --------------------------------

(defun ctrl-kinds-ok (ctrl)
  (declare (xargs :guard t))
  (or (atom ctrl)
      (and (sym-member (entry-kind (car ctrl)) '(:l :h :f)) (ctrl-kinds-ok (cdr ctrl)))))
(defthm fast-try-entry-is-try-rules
  (implies (sym-member k '(:l :h :f))
           (equal (fast-try-entry k z redex fm)
                  (fast-try-rules (rules-for (list :entry k)) z redex fm)))
  :hints (("Goal" :in-theory (e/d (fast-try-entry rules-for) (fast-try-rules)))))
(defthm all-u-holds-of-entry
  (implies (sym-member k '(:l :h :f))
           (all-u-holds (rules-for (list :entry k)) s f redex fm))
  :hints (("Goal" :in-theory (e/d (rules-for) (all-u-holds)))))
(defthm fast-try-anyprefix-is-try-rules-for
  (equal (fast-try-anyprefix z redex fm)
         (fast-try-rules (rules-for :anyprefix) z redex fm))
  :hints (("Goal" :in-theory (e/d (rules-for) (fast-try-rules fast-try-anyprefix)))))
(defthm all-u-holds-of-anyprefix
  (all-u-holds (rules-for :anyprefix) s f redex fm)
  :hints (("Goal" :in-theory (e/d (rules-for) (all-u-holds)))))

; trap and throw_ref among other instructions: both rules are frame-safe, so
; the stobj is not touched (needed when the result is not a true list and
; the machine stops :stuck with the state it had)
(defthm fast-apply-rule-frame-safe-keeps-fm
  (implies (and (frame-safe-p fn) (not (sym-member fn *fast-memory-rules*)))
           (equal (cadddr (fast-apply-rule fn z redex fm)) fm))
  :hints (("Goal" :in-theory (e/d (fast-apply-rule) (apply-rule frame-safe-p sym-member)))))
(make-event
 `(defthm fast-try-anyprefix-rules-keep-fm
    (equal (cadddr (fast-try-rules ',(rules-for :anyprefix) z redex fm)) fm)
    :hints (("Goal" :in-theory (e/d (fast-try-rules) (fast-apply-rule))))))

; --- the parts of a step ------------------------------------------------------

(defthm fast-exit-step-refines
  (implies (and (fmp fm) (fast-inv-store (fm-store fm))
                (sym-member (entry-kind (car (fm-ctrl fm))) '(:l :h :f))
                (not (equal (fm-status (fast-exit-step fm)) :unsupported)))
           (equal (fm->ms (fast-exit-step fm)) (exit-step (fm->ms fm))))
  :hints (("Goal" :in-theory (e/d (fast-exit-step exit-step fm->ms ms-z fm-z fm->ms-of-update-fm-status put-z-bytes)
                                  (fast-try-entry fast-try-rules try-rules apply-rule fast-apply-rule
                                   put-mem0-bytes rules-for all-u-holds admin-term sym-member
                                   entry-kind entry-n entry-x entry-v entry-r fm-set fmp fast-inv-store
                                   fast-try-rules-refines take-n drop-n rev-onto app mem-to-list))
                  :use ((:instance fast-try-rules-refines
                                   (rules (rules-for (list :entry (entry-kind (car (fm-ctrl fm))))))
                                   (s (fm-store fm))
                                   (f (if (eq (entry-kind (car (fm-ctrl fm))) :f)
                                          (entry-x (car (fm-ctrl fm))) (fm-frame fm)))
                                   (redex (list (admin-term (entry-kind (car (fm-ctrl fm)))
                                                            (entry-n (car (fm-ctrl fm)))
                                                            (if (eq (entry-kind (car (fm-ctrl fm))) :f)
                                                                (fm-frame fm) (entry-x (car (fm-ctrl fm))))
                                                            (rev-onto (fm-vals fm) (fm-is fm)))))))
                  :do-not-induct t)))
(defthm fast-anyprefix-step-refines
  (implies (and (fmp fm) (fast-inv-store (fm-store fm))
                (not (equal (fm-status (fast-anyprefix-step fm)) :unsupported)))
           (equal (fm->ms (fast-anyprefix-step fm)) (anyprefix-step (fm->ms fm))))
  :hints (("Goal" :in-theory (e/d (fast-anyprefix-step anyprefix-step fm->ms ms-z fm-z fm->ms-of-update-fm-status put-z-bytes)
                                  (fast-try-anyprefix fast-try-rules try-rules apply-rule fast-apply-rule
                                   put-mem0-bytes rules-for all-u-holds
                                   fm-set fmp fast-inv-store
                                   fast-try-rules-refines take-n drop-n rev-onto app mem-to-list))
                  :use ((:instance fast-try-rules-refines
                                   (rules (rules-for :anyprefix))
                                   (s (fm-store fm)) (f (fm-frame fm))
                                   (redex (rev-onto (fm-vals fm) (fm-is fm)))))
                  :do-not-induct t)))
(defthm fast-enter-step-refines
  (implies (fmp fm)
           (equal (fm->ms (fast-enter-step fm)) (enter-step (fm->ms fm))))
  :hints (("Goal" :in-theory (e/d (fast-enter-step enter-step fm->ms fm->ms-of-update-fm-status)
                                  (put-mem0-bytes enterable-p admin-kind entry-n entry-x entry-v
                                   fm-set fmp mem-to-list))
                  :do-not-induct t)))

; --- the step -----------------------------------------------------------------

(defthm ms-fields-of-fm->ms
  (and (equal (ms-is (fm->ms fm)) (fm-is fm))
       (equal (ms-vals (fm->ms fm)) (fm-vals fm))
       (equal (ms-ctrl (fm->ms fm)) (fm-ctrl fm))
       (equal (ms-status (fm->ms fm)) (fm-status fm))
       (equal (ms-frame (fm->ms fm)) (fm-frame fm)))
  :hints (("Goal" :in-theory (e/d (fm->ms) (put-mem0-bytes mem-to-list)))))

(defthm fm->ms-of-push
  (equal (fm->ms (update-fm-is a (update-fm-vals b fm)))
         (ms (ms-store (fm->ms fm)) (ms-frame (fm->ms fm)) b a (ms-ctrl (fm->ms fm)) (ms-status (fm->ms fm))))
  :hints (("Goal" :in-theory (e/d (fm->ms) (put-mem0-bytes)))))

(defthm ctrl-kinds-ok-top
  (implies (and (ctrl-kinds-ok c) (consp c))
           (sym-member (entry-kind (car c)) '(:l :h :f)))
  :hints (("Goal" :in-theory (disable sym-member entry-kind))))

(defthm fast-exit-step-refines-ctrl-kinds-ok
  (implies (and (fmp fm) (fast-inv-store (fm-store fm))
                (ctrl-kinds-ok (fm-ctrl fm)) (consp (fm-ctrl fm))
                (not (equal (fm-status (fast-exit-step fm)) :unsupported)))
           (equal (fm->ms (fast-exit-step fm)) (exit-step (fm->ms fm))))
  :hints (("Goal" :use (fast-exit-step-refines (:instance ctrl-kinds-ok-top (c (fm-ctrl fm))))
                  :in-theory (disable fast-exit-step-refines ctrl-kinds-ok-top fast-exit-step exit-step fm->ms ctrl-kinds-ok
                                      sym-member entry-kind fmp fast-inv-store))))

; the fast paths (refine-hot.lisp): a handled instruction is the op step; a
; declined one leaves the stobj as it was; none of them is a value
(defthm hot-instr-not-value
  (implies (member-equal (car i) '(:local.get :local.set :local.tee :binop :relop :br_if))
           (not (value-instr-p i)))
  :hints (("Goal" :in-theory (enable value-instr-p w3t::val-p))))

(defthm hot-step-is-op-step
  (implies (and (fmp fm) (equal (fm-status fm) :run) (consp (fm-is fm))
                (member-equal (car (car (fm-is fm))) '(:local.get :local.set :local.tee :binop :relop :br_if))
                (car (fast-hot-step (car (fm-is fm)) fm)))
           (equal (cadr (fast-hot-step (car (fm-is fm)) fm)) (fast-op-step fm)))
  :hints (("Goal" :use ((:instance hot-local.get (i (car (fm-is fm)))) (:instance hot-local.set (i (car (fm-is fm))))
                        (:instance hot-local.tee (i (car (fm-is fm)))) (:instance hot-binop (i (car (fm-is fm))))
                        (:instance hot-relop (i (car (fm-is fm)))) (:instance hot-br_if (i (car (fm-is fm)))))
                  :in-theory (disable hot-local.get hot-local.set hot-local.tee hot-binop hot-relop hot-br_if
                                      fast-hot-step fast-op-step fmp))))

(defthm hot-case-handled
  (implies (and (fmp fm) (fast-inv-store (fm-store fm))
                (equal (fm-status fm) :run) (consp (fm-is fm))
                (member-equal (car (car (fm-is fm))) '(:local.get :local.set :local.tee :binop :relop :br_if))
                (car (fast-hot-step (car (fm-is fm)) fm))
                (not (equal (fm-status (cadr (fast-hot-step (car (fm-is fm)) fm))) :unsupported)))
           (equal (fm->ms (cadr (fast-hot-step (car (fm-is fm)) fm))) (op-step (fm->ms fm))))
  :hints (("Goal" :use (hot-step-is-op-step fast-op-step-refines)
                  :in-theory (disable hot-step-is-op-step fast-op-step-refines fast-hot-step fast-op-step op-step
                                      fm->ms fmp fast-inv-store))))

(defthm hot-step-declined-keeps-fm
  (implies (not (car (fast-hot-step i fm)))
           (equal (cadr (fast-hot-step i fm)) fm))
  :hints (("Goal" :in-theory (e/d (fast-hot-step)
                                  (w3t::val-p fast-val-p w3t::$binop_ w3t::$relop_ w3t::$with_local w3t::$local)))))

(defthm fast-step-refines
  (implies (and (fmp fm) (fast-inv-store (fm-store fm)) (ctrl-kinds-ok (fm-ctrl fm))
                (not (equal (entry-kind (car (fm-is fm))) :call_ref))
                (not (equal (fm-status (fast-step fm)) :unsupported)))
           (equal (fm->ms (fast-step fm)) (machine-step (fm->ms fm))))
  :hints (("Goal" :use (hot-case-handled)
                  :in-theory (e/d (fast-step machine-step fm->ms-of-update-fm-status)
                                  (hot-case-handled hot-step-is-op-step
                                   hot-local.get hot-local.set hot-local.tee hot-binop hot-relop hot-br_if
                                   fast-op-step op-step fast-exit-step exit-step fast-anyprefix-step anyprefix-step
                                   fast-enter-step enter-step fast-hot-step fmp fast-inv-store fm->ms
                                   put-mem0-bytes mem-to-list fast-val-p value-instr-p ctrl-kinds-ok
                                   update-fm-status update-fm-vals update-fm-is ms-with-status
                                   ms-is ms-vals ms-ctrl ms-status ms-frame ms-store))
                  :do-not-induct t)))
