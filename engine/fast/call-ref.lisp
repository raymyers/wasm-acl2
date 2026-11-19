; License: MIT. See the file LICENSE at the top of the repository.
;
; V7 of plan/wasm-engine/plan2.md: call_ref on the fast machine.
;
; The step theorem of refine-op.lisp (FAST-STEP-REFINES) excludes call_ref:
; two of its four rules, the host calls, have no (U) lemma (refine-step.lisp,
; *U-NOT-YET*), so the place (:op :call_ref) has none (*PLACES-NOT-YET*).
; Since V7 the fast machine does not make host calls (plan2.md P1): FAST-STEP
; stops :unsupported at a call_ref whose reference is a host function
; (HOST-REF-P, fast.lisp). Here:
;   - a host rule fails on a redex whose reference is not a host function,
;     so (U) holds for it there (both machines do not fire it);
;   - the place lemma of (:op :call_ref) under that hypothesis;
;   - FAST-STEP-IS-MACHINE-STEP: the step theorem with no hypothesis about
;     the instruction;
;   - FAST-STEP-REFUSES-HOST-CALL and HOST-RULES-FAIL-AT-FAST-STEP: the fast
;     machine applies no host rule;
;   - the check that what refine.lisp and refine-step.lisp record as not
;     proved is exactly the two host rules and their place.
;
; Normal forms: as in refine-op.lisp, the results of APPLY-RULE,
; FAST-APPLY-RULE and FAST-TRY-RULES are taken with CAR, CADR, CADDR, CADDDR
; where a lemma has to match U-HOLDS and FAST-TRY-RULES-REFINES, which are
; stated that way.
(in-package "WE")
(include-book "refine-op")

(set-prover-step-limit 2000000)

; local: the books above this one keep the theory they had
(local
 (in-theory (disable drop-n take-n rev-onto app sym-member
                     value-instr-p w3t::val-p fast-val-p exit-instr-p admin-kind enterable-p
                     fmp fm-set fm->ms fast-inv-store host-ref-p
                     apply-rule fast-apply-rule fast-apply-fallback fast-memory-rule
                     fast-try-rules try-rules rule-may-match frame-safe-p
                     list-to-mem mem-write mem-to-list put-mem0-bytes
                     redex-arity entry-kind entry-n
                     machine-step op-step
                     fast-step fast-op-step fast-exit-step fast-anyprefix-step
                     fast-enter-step fast-hot-step
                     u-holds all-u-holds
                     ; openers of refine-hot.lisp: the redex stays (rev-onto (take-n k vals) (list i))
                     rev-onto-cons take-n-open)))

(defconst *host-rules*
  '(w3t::step/r-call_ref-hostfunc-res w3t::step/r-call_ref-hostfunc-div))

; ---------------------------------------------------------------------------
; 1. A host rule fails unless the reference is a host function

(defthm nth-t-is-nth
  (equal (nth-t n l) (nth n l))
  :hints (("Goal" :induct (nth-t n l) :in-theory (enable nth-t nth))))

; the reference of a redex val* ref (call_ref y): its last element but one
(defun redex-ref (redex)
  (car (nthcdr (- (len redex) 2) redex)))

(defthm step/r-call_ref-hostfunc-res-fails-when-not-host-ref
  (implies (not (host-ref-p (redex-ref l) s))
           (not (w3t::step/r-call_ref-hostfunc-res (list :|%;%| (list :|%;%| s f) l))))
  :hints (("Goal" :in-theory (e/d (w3t::step/r-call_ref-hostfunc-res host-ref-p entry-kind entry-n)
                                  (w3t::$hostcall w3t::expand w3t::$lift_result
                                   w3t::step/match71 wrt::%get-field nth len nthcdr take))
                  :do-not-induct t)))

(defthm step/r-call_ref-hostfunc-div-fails-when-not-host-ref
  (implies (not (host-ref-p (redex-ref l) s))
           (not (w3t::step/r-call_ref-hostfunc-div (list :|%;%| (list :|%;%| s f) l))))
  :hints (("Goal" :in-theory (e/d (w3t::step/r-call_ref-hostfunc-div host-ref-p entry-kind entry-n)
                                  (w3t::$hostcall w3t::expand
                                   w3t::step/match89 wrt::%get-field nth len nthcdr take))
                  :do-not-induct t)))

(in-theory (disable redex-ref))

(defthm apply-rule-of-host-rule-when-not-host-ref
  (implies (and (sym-member fn *host-rules*)
                (not (host-ref-p (redex-ref redex) s)))
           (not (car (apply-rule fn (list :|%;%| s f) redex))))
  :hints (("Goal" :in-theory (enable sym-member) :do-not-induct t)))

; the functions of the full store are those of the fast store
(defthm host-ref-p-of-put-mem0-bytes
  (implies (store-fields-p s)
           (equal (host-ref-p ref (put-mem0-bytes s b))
                  (host-ref-p ref s)))
  :hints (("Goal" :in-theory (e/d (host-ref-p put-mem0-bytes) (wrt::%get-field wrt::%put-field)))))

(defthm store-fields-p-when-fast-inv-store
  (implies (fast-inv-store s)
           (store-fields-p s))
  :hints (("Goal" :in-theory (enable fast-inv-store fast-store-ok))))

; ---------------------------------------------------------------------------
; 2. (U) for a rule of the fallback that does not fire on the full store

(defthm u-holds-when-fallback-rule-fails
  (implies (and (not (sym-member fn *fast-memory-rules*))
                (not (frame-safe-p fn))
                (not (car (apply-rule fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))))
           (u-holds fn s f redex fm))
  :hints (("Goal" :in-theory (e/d (u-holds fast-apply-rule fast-apply-fallback put-z-bytes)
                                  ((:e sym-member)))
                  :do-not-induct t)))

; without the fast store (U) says nothing
(defthm u-holds-when-not-fast-inv-store
  (implies (not (fast-inv-store s))
           (u-holds fn s f redex fm))
  :hints (("Goal" :in-theory (enable u-holds))))

(defthm u-holds-of-host-rule-when-not-host-ref
  (implies (and (sym-member fn *host-rules*)
                (not (host-ref-p (redex-ref redex) s)))
           (u-holds fn s f redex fm))
  :hints (("Goal" :cases ((fast-inv-store s))
                  :in-theory (enable sym-member frame-safe-p)
                  :do-not-induct t)))

; ---------------------------------------------------------------------------
; 3. The place (:op :call_ref)

(make-event
 `(defthm fast-try-op-call_ref-is-try-rules
    (equal (fast-try-op-call_ref z redex fm)
           (fast-try-rules ',(rules-for '(:op :call_ref)) z redex fm))
    ; the hints of PLACE-EQ-LEMMA (refine-step.lisp)
    :hints (("Goal" :in-theory (e/d (fast-try-op-call_ref fast-try-rules)
                                    (,@(rules-for '(:op :call_ref))))
                    :expand ,(direct-rule-expands (rules-for '(:op :call_ref)))
                    :do-not-induct t))))

(make-event
 `(defthm all-u-holds-of-call_ref
    (implies (not (host-ref-p (redex-ref redex) s))
             (all-u-holds ',(rules-for '(:op :call_ref)) s f redex fm))
    :hints (("Goal" :in-theory (enable all-u-holds (:e sym-member)) :do-not-induct t))))

; FAST-TRY-OP-IS-TRY-RULES of refine-op.lisp, for every opcode
(defthm fast-try-op-is-try-rules-for-any-op
  (implies (op-has-rules kw)
           (equal (fast-try-op kw z redex fm)
                  (fast-try-rules (rules-for (list :op kw)) z redex fm)))
  :hints (("Goal" :cases ((equal kw :call_ref))
                  :in-theory (enable fast-try-op)
                  :do-not-induct t)))

(defthm all-u-holds-of-any-op
  (implies (and (op-has-rules kw)
                (or (not (equal kw :call_ref))
                    (not (host-ref-p (redex-ref redex) s))))
           (all-u-holds (rules-for (list :op kw)) s f redex fm))
  :hints (("Goal" :cases ((equal kw :call_ref)) :do-not-induct t)))

; ---------------------------------------------------------------------------
; 4. The redex of the op step: its reference is the top of the stack

(defthm len-of-rev-onto
  (equal (len (rev-onto x acc))
         (+ (len x) (len acc)))
  :hints (("Goal" :induct (rev-onto x acc) :in-theory (enable rev-onto))))

(defun rev-onto-count-induct (x acc n)
  (if (atom x)
      (list acc n)
    (rev-onto-count-induct (cdr x) (cons (car x) acc) (+ 1 n))))

(defthm nthcdr-of-rev-onto-past-its-list
  (implies (natp n)
           (equal (nthcdr (+ n (len x)) (rev-onto x acc))
                  (nthcdr n acc)))
  :hints (("Goal" :induct (rev-onto-count-induct x acc n) :in-theory (enable rev-onto))))

(defthm nthcdr-of-len-of-rev-onto
  (equal (nthcdr (len x) (rev-onto x acc))
         acc)
  :hints (("Goal" :use ((:instance nthcdr-of-rev-onto-past-its-list (n 0)))
                  :in-theory (disable nthcdr-of-rev-onto-past-its-list))))

(defthm redex-ref-of-op-redex
  (implies (and (posp k) (consp vals))
           (equal (redex-ref (rev-onto (take-n k vals) (list i)))
                  (car vals)))
  :hints (("Goal" :in-theory (enable redex-ref)
                  :expand ((take-n k vals)
                           (rev-onto (cons (car vals) (take-n (+ -1 k) (cdr vals))) (list i)))
                  :do-not-induct t)))

(defthm redex-arity-of-call_ref-is-positive
  (implies (and (equal (entry-kind i) :call_ref)
                (redex-arity i z vals))
           (< 0 (redex-arity i z vals)))
  :hints (("Goal" :in-theory (enable redex-arity)))
  :rule-classes (:rewrite :linear))

(defthm redex-ref-of-op-redex-when-enough-operands
  (implies (and (natp k) (< 0 k) (<= k (len vals)))
           (equal (redex-ref (rev-onto (take-n k vals) (list i)))
                  (car vals)))
  :hints (("Goal" :cases ((consp vals)) :do-not-induct t)))

; ---------------------------------------------------------------------------
; 5. The op step at call_ref

(defthm fast-op-step-refines-call_ref
  (implies (and (fmp fm) (fast-inv-store (fm-store fm))
                (equal (entry-kind (car (fm-is fm))) :call_ref)
                (not (host-ref-p (car (fm-vals fm)) (fm-store fm)))
                (not (equal (fm-status (fast-op-step fm)) :unsupported)))
           (equal (fm->ms (fast-op-step fm)) (op-step (fm->ms fm))))
  ; the proof of FAST-OP-STEP-REFINES (refine-op.lisp)
  :hints (("Goal" :in-theory (e/d (fast-op-step op-step fm->ms ms-z fm-z fm->ms-of-update-fm-status put-z-bytes)
                                  (fast-try-op op-has-rules rules-for fast-try-rules-refines))
                  :use ((:instance fast-try-rules-refines
                                   (rules (rules-for (list :op (entry-kind (car (fm-is fm))))))
                                   (s (fm-store fm)) (f (fm-frame fm))
                                   (redex (rev-onto (take-n (redex-arity (car (fm-is fm)) (fm-z fm) (fm-vals fm))
                                                            (fm-vals fm))
                                                    (list (car (fm-is fm)))))))
                  :do-not-induct t)))

; ---------------------------------------------------------------------------
; 6. The step

(defthm call_ref-is-an-op
  (implies (equal (entry-kind i) :call_ref)
           (and (consp i)
                (equal (car i) :call_ref)
                (not (value-instr-p i))
                (not (fast-val-p i))
                (not (admin-kind i))
                (not (exit-instr-p i))))
  :hints (("Goal" :in-theory (enable entry-kind value-instr-p fast-val-p w3t::val-p admin-kind
                                     exit-instr-p sym-member))))

(defthm fast-step-when-not-running
  (implies (not (equal (fm-status fm) :run))
           (equal (fast-step fm) fm))
  :hints (("Goal" :in-theory (enable fast-step))))

(defthm fast-step-at-call_ref
  (implies (and (equal (fm-status fm) :run)
                (equal (entry-kind (car (fm-is fm))) :call_ref))
           (equal (fast-step fm)
                  (if (host-ref-p (car (fm-vals fm)) (fm-store fm))
                      (update-fm-status :unsupported fm)
                    (fast-op-step fm))))
  :hints (("Goal" :in-theory (enable fast-step (:e sym-member))
                  :use ((:instance call_ref-is-an-op (i (car (fm-is fm)))))
                  :do-not-induct t)))

(defthm machine-step-at-call_ref
  (implies (and (equal (ms-status s) :run)
                (equal (entry-kind (car (ms-is s))) :call_ref))
           (equal (machine-step s) (op-step s)))
  :hints (("Goal" :in-theory (enable machine-step (:e sym-member))
                  :use ((:instance call_ref-is-an-op (i (car (ms-is s)))))
                  :do-not-induct t)))

(defthm machine-step-of-fm->ms-when-not-running
  (implies (not (equal (fm-status fm) :run))
           (equal (machine-step (fm->ms fm)) (fm->ms fm)))
  :hints (("Goal" :in-theory (enable machine-step))))

(defthm fast-step-refines-call_ref
  (implies (and (fmp fm) (fast-inv-store (fm-store fm))
                (equal (entry-kind (car (fm-is fm))) :call_ref)
                (not (equal (fm-status (fast-step fm)) :unsupported)))
           (equal (fm->ms (fast-step fm)) (machine-step (fm->ms fm))))
  :hints (("Goal" :cases ((equal (fm-status fm) :run)) :do-not-induct t)))

; The step theorem. FAST-STEP-REFINES of refine-op.lisp without its
; hypothesis about call_ref.
(defthm fast-step-is-machine-step
  (implies (and (fmp fm) (fast-inv-store (fm-store fm)) (ctrl-kinds-ok (fm-ctrl fm))
                (not (equal (fm-status (fast-step fm)) :unsupported)))
           (equal (fm->ms (fast-step fm)) (machine-step (fm->ms fm))))
  :hints (("Goal" :cases ((equal (entry-kind (car (fm-is fm))) :call_ref))
                  :in-theory (disable ctrl-kinds-ok)
                  :do-not-induct t)))

; ---------------------------------------------------------------------------
; 7. No host rule fires in a step of the fast machine

; at a call_ref of a host function the fast machine stops
(defthm fast-step-refuses-host-call
  (implies (and (equal (fm-status fm) :run)
                (equal (entry-kind (car (fm-is fm))) :call_ref)
                (host-ref-p (car (fm-vals fm)) (fm-store fm)))
           (equal (fm-status (fast-step fm)) :unsupported)))

; at any other call_ref the two host rules fail on the redex of the op step,
; in the store of the list machine (the fast store with the array put back)
(defthm host-rule-fails-on-op-redex
  (implies (and (sym-member fn *host-rules*)
                (fast-inv-store s)
                (not (host-ref-p (car vals) s))
                (natp k) (< 0 k) (<= k (len vals)))
           (not (car (apply-rule fn (list :|%;%| (put-mem0-bytes s b) f)
                                 (rev-onto (take-n k vals) (list i))))))
  :hints (("Goal" :in-theory (disable (:e sym-member)) :do-not-induct t)))

; ---------------------------------------------------------------------------
; 8. What the older books record as not proved is the host rules and their
; place, and nothing else (plan2.md V7, last item)

(make-event
 (if (and (equal *fallback-not-yet* *host-rules*)
          (equal *u-not-yet* *host-rules*)
          (equal *places-not-yet* '((:op :call_ref)))
          (subsetp-equal *host-rules* (rules-for '(:op :call_ref))))
     (value '(value-triple :not-proved-is-the-host-rules-and-their-place))
   (er soft 'call-ref
       "Recorded as not proved: fallback ~x0, (U) ~x1, places ~x2; expected the host rules ~x3 and the place (:op :call_ref)."
       *fallback-not-yet* *u-not-yet* *places-not-yet* *host-rules*)))

(in-theory (disable fast-step-refines-call_ref fast-op-step-refines-call_ref
                    fast-step-at-call_ref machine-step-at-call_ref))
