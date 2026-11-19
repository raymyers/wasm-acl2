; License: MIT. See the file LICENSE at the top of the repository.
;
; Ground work for the proofs about W3T::STEP (plan/wasm-engine/plan2.md V0):
;   - SPEC-DEFINITIONS: the theory of every definition of the specification,
;     which a proof book disables in its header and then opens by name;
;   - STEPN, exactly K steps (the definition of theorem/simulation.lisp,
;     stated again so that a rules book does not need that book);
;   - STEP-OPENER: STEP opened one level, as a rewrite rule that fires on an
;     explicit configuration only. The rule functions stay closed;
;   - what STEP returns: NIL, or a list of one configuration (:|%;%| z' is')
;     with IS' a true list (STEP-RESULT-P);
;   - %SIZE, the measure the context rules test before they recur: of a
;     sublist and of the body of an administrative term it is smaller.
(in-package "WE")
(include-book "terminal")
(include-book "../lib/lists")

(set-prover-step-limit 2000000)

(defun spec-definition-runes (runes)
  (declare (xargs :mode :program))
  (cond ((endp runes) nil)
        ((and (consp (car runes)) (eq (car (car runes)) :definition)
              (member-equal (symbol-package-name (cadr (car runes))) '("W3T" "WRT")))
         (cons (car runes) (spec-definition-runes (cdr runes))))
        (t (spec-definition-runes (cdr runes)))))

(deftheory spec-definitions (spec-definition-runes (current-theory :here)))

(in-theory (disable spec-definitions))

; ---------------------------------------------------------------------------
; STEPN

(defun stepn (k c)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      (list c)
    (let ((r (w3t::step c)))
      (and r (stepn (1- k) (car r))))))

(defthm stepn-of-0
  (equal (stepn 0 c) (list c)))

(defthm stepn-of-1
  (equal (stepn 1 c)
         (and (w3t::step c) (list (car (w3t::step c)))))
  :hints (("Goal" :expand ((stepn 1 c)))))

(in-theory (disable stepn))

; ---------------------------------------------------------------------------
; STEP, one level. The right-hand side is STEP's own body, read from the
; world, so the rule follows the specification when it is regenerated.

(make-event
 (let ((body (getpropc 'w3t::step 'acl2::unnormalized-body nil (w state))))
   `(defthm step-opener
      (implies (syntaxp (and (consp w3t::%a0) (eq (car w3t::%a0) 'cons)))
               (equal (w3t::step w3t::%a0) ,body))
      :hints (("Goal" :in-theory (theory 'minimal-theory)
                      :expand ((w3t::step w3t::%a0)))))))

(in-theory (disable step-opener))

; ---------------------------------------------------------------------------
; What a step returns

(defun step-result-p (r)
  (and (consp r) (null (cdr r))
       (consp (car r)) (equal (car (car r)) :|%;%|)
       (true-listp (cdr (car r))) (equal (len (cdr (car r))) 2)
       (true-listp (caddr (car r)))))

(defthm step-result-p-of-list-of-config
  (equal (step-result-p (list (list :|%;%| z is))) (true-listp is)))

(defthm true-listp-of-cons
  (equal (true-listp (cons a b)) (true-listp b)))

; One lemma per rule function that STEP calls. STEP/R-PURE and STEP/R-READ
; test that the instructions they return are a true list; every other rule
; builds its configuration explicitly.
(deflabel step-result-anchor)
(deftheory step-result-theory
  (union-theories (theory 'minimal-theory)
    (union-theories (executable-counterpart-theory 'step-result-anchor)
      '(step-result-p-of-list-of-config true-listp-of-cons car-cons cdr-cons))))

(defun result-lemma-name (fn)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-RESULT-SHAPE") 'we::here))

(defun result-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 200000
                   (defthm ,(result-lemma-name fn)
                     (implies (,fn c) (step-result-p (,fn c)))
                     :hints (("Goal" :in-theory (union-theories (theory 'step-result-theory) '(,fn))
                                     :do-not-induct t))))
                 (value-triple (cw "RESULT-SHAPE ~x0~%" ',fn)))
          (value-triple (cw "RESULT-SHAPE-FAILED ~x0~%" ',fn)))))

(defun result-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (result-lemma (car fns)) (result-lemmas (cdr fns)))))

(defun result-lemmas-missing (fns wrld)
  (declare (xargs :mode :program))
  (cond ((endp fns) nil)
        ((getpropc (result-lemma-name (car fns)) 'acl2::theorem nil wrld)
         (result-lemmas-missing (cdr fns) wrld))
        (t (cons (car fns) (result-lemmas-missing (cdr fns) wrld)))))

; proved by hand below: the context rules (members of STEP's clique) and
; the two host-call rules (their instructions are not an explicit list)
(defconst *result-shape-by-hand*
  '(w3t::step/r-ctxt-instrs w3t::step/r-ctxt-label w3t::step/r-ctxt-handler
    w3t::step/r-ctxt-frame w3t::step/r-call_ref-hostfunc-res
    w3t::step/r-call_ref-hostfunc-div))

(defun step-direct-rules (wrld)          ; the rule functions STEP calls
  (declare (xargs :mode :program))
  (rule-calls-of (getpropc 'w3t::step 'acl2::unnormalized-body nil wrld)))

; one top-level event: its step limit is the sum over the lemmas
(set-prover-step-limit 50000000)
(make-event `(progn ,@(result-lemmas (set-difference-eq (step-direct-rules (w state))
                                                         *result-shape-by-hand*))))
(set-prover-step-limit 2000000)

; The two host-call rules return ($LIFT_RESULT result), a true list for
; every host.
(defthm true-listp-of-$lift_result/iter1
  (true-listp (w3t::$lift_result/iter1 l))
  :hints (("Goal" :in-theory (enable w3t::$lift_result/iter1))))

(defthm true-listp-of-$lift_result
  (true-listp (w3t::$lift_result r))
  :hints (("Goal" :in-theory (enable w3t::$lift_result))))

(defthm step/r-call_ref-hostfunc-res-result-shape
  (implies (w3t::step/r-call_ref-hostfunc-res c)
           (step-result-p (w3t::step/r-call_ref-hostfunc-res c)))
  :hints (("Goal" :in-theory (union-theories (theory 'step-result-theory)
                                             '(w3t::step/r-call_ref-hostfunc-res true-listp-of-$lift_result))
                  :do-not-induct t)))

(defthm step/r-call_ref-hostfunc-div-result-shape
  (implies (w3t::step/r-call_ref-hostfunc-div c)
           (step-result-p (w3t::step/r-call_ref-hostfunc-div c)))
  :hints (("Goal" :in-theory (union-theories (theory 'step-result-theory)
                                             '(w3t::step/r-call_ref-hostfunc-div true-listp-of-append))
                  :do-not-induct t)))

; The context rules are members of STEP's clique, so they are opened by
; :expand. What they return is built explicitly: nothing is needed about the
; step inside.
(defthm step/r-ctxt-label-result-shape
  (implies (w3t::step/r-ctxt-label c) (step-result-p (w3t::step/r-ctxt-label c)))
  :hints (("Goal" :in-theory (theory 'step-result-theory)
                  :expand ((w3t::step/r-ctxt-label c)) :do-not-induct t)))

(defthm step/r-ctxt-handler-result-shape
  (implies (w3t::step/r-ctxt-handler c) (step-result-p (w3t::step/r-ctxt-handler c)))
  :hints (("Goal" :in-theory (theory 'step-result-theory)
                  :expand ((w3t::step/r-ctxt-handler c)) :do-not-induct t)))

(defthm step/r-ctxt-frame-result-shape
  (implies (w3t::step/r-ctxt-frame c) (step-result-p (w3t::step/r-ctxt-frame c)))
  :hints (("Goal" :in-theory (theory 'step-result-theory)
                  :expand ((w3t::step/r-ctxt-frame c)) :do-not-induct t)))

; Step/ctxt-instrs: its search counts K down and stops below 0
(defun search-down-induct (k)
  (declare (xargs :measure (if (natp k) (+ 1 k) 0)))
  (if (natp k) (search-down-induct (1- k)) k))

(in-theory (disable step-result-p))

(defthm step/search21-result-shape
  (implies (w3t::step/search21 k lo hi l p z c)
           (step-result-p (w3t::step/search21 k lo hi l p z c)))
  :hints (("Goal" :induct (search-down-induct k)
                  :in-theory (union-theories (theory 'step-result-theory)
                                             '(true-listp-of-append (:induction search-down-induct)))
                  :expand ((w3t::step/search21 k lo hi l p z c)))))

(defthm step/r-ctxt-instrs-result-shape
  (implies (w3t::step/r-ctxt-instrs c) (step-result-p (w3t::step/r-ctxt-instrs c)))
  :hints (("Goal" :in-theory (union-theories (theory 'step-result-theory) '(step/search21-result-shape))
                  :expand ((w3t::step/r-ctxt-instrs c)) :do-not-induct t)))

; every rule function STEP calls has its lemma
(make-event
 (let ((missing (result-lemmas-missing (step-direct-rules (w state)) (w state))))
   (if missing
       (er soft 'step-basics "No result-shape lemma was proved for ~x0." missing)
     (value '(value-triple :all-result-shape-lemmas-proved)))))

; STEP returns NIL or one well-shaped configuration. STEP is opened; the
; rule functions are not.
(defthm step-result-shape
  (implies (w3t::step c) (step-result-p (w3t::step c)))
  :hints (("Goal" :expand ((w3t::step c)) :do-not-induct t)))

; ---------------------------------------------------------------------------
; %SIZE. A context rule recurs on (z; is) only after the test
;   (< (%size (nth 2 (list :|%;%| z is))) (%size (nth 2 c)))
; where IS is a sublist of the instructions of C (Step/ctxt-instrs) or the
; body of the one administrative term of C (the other three).

(defthm %size-of-cons
  (equal (wrt::%size (cons a b)) (+ 1 (wrt::%size a) (wrt::%size b)))
  :hints (("Goal" :in-theory (enable wrt::%size))))

(defthm natp-of-%size
  (natp (wrt::%size x))
  :hints (("Goal" :in-theory (enable wrt::%size)))
  :rule-classes :type-prescription)

(defun cdr-n-induct (n l)
  (if (zp n) l (cdr-n-induct (1- n) (cdr l))))

(local
 (defthm acl2-count-of-nthcdr
   (<= (acl2-count (nthcdr n l)) (acl2-count l))
   :hints (("Goal" :induct (cdr-n-induct n l) :in-theory (enable nthcdr)))
   :rule-classes :linear))

(local
 (defthm acl2-count-of-nthcdr-strict
   (implies (and (consp l) (posp n))
            (< (acl2-count (nthcdr n l)) (acl2-count l)))
   :hints (("Goal" :expand ((nthcdr n l))
            :use ((:instance acl2-count-of-nthcdr (n (1- n)) (l (cdr l))))
            :in-theory (disable acl2-count-of-nthcdr)))
   :rule-classes :linear))

(defthm %size-of-nthcdr-linear
  (<= (wrt::%size (nthcdr n l)) (wrt::%size l))
  :hints (("Goal" :in-theory (enable wrt::%size)))
  :rule-classes :linear)

(defthm %size-of-nthcdr-strict-linear
  (implies (and (consp l) (posp n))
           (< (wrt::%size (nthcdr n l)) (wrt::%size l)))
  :hints (("Goal" :in-theory (enable wrt::%size)))
  :rule-classes :linear)

(defthm %size-of-take-linear
  (implies (<= (nfix n) (len l))
           (<= (wrt::%size (take n l)) (wrt::%size l)))
  :hints (("Goal" :in-theory (enable wrt::%size take)))
  :rule-classes :linear)

(defthm %size-of-take-strict-linear
  (implies (< (nfix n) (len l))
           (< (wrt::%size (take n l)) (wrt::%size l)))
  :hints (("Goal" :in-theory (enable wrt::%size take)))
  :rule-classes :linear)

; the test of Step/ctxt-label, Step/ctxt-handler and Step/ctxt-frame
(defthm %size-check-of-admin-body
  (< (wrt::%size (nth 2 (list :|%;%| z2 body)))
     (wrt::%size (nth 2 (list :|%;%| z (list (list kw n x body)))))))

; the test of Step/ctxt-instrs: M elements of L from K on, not all of L
(defthm %size-check-of-sublist
  (implies (and (natp k) (natp m) (<= (+ k m) (len l))
                (or (posp k) (< (+ k m) (len l))))
           (< (wrt::%size (nth 2 (list :|%;%| z2 (take m (nthcdr k l)))))
              (wrt::%size (nth 2 (list :|%;%| z l))))))
