; License: MIT. See the file LICENSE at the top of the repository.
;
; Dispatch (plan/wasm-engine/plan2.md V1, item 4 and the exit): on a redex,
; the relations of the specification are the machine's rule table.
;   - *PURE-RULE-FNS*, *READ-RULE-FNS*, *OWN-RULE-FNS*: the rule functions
;     of W3T::STEP_PURE, of W3T::STEP_READ/SPLIT and of W3T::STEP itself, in
;     their order. (STEP-OWN c) is the part of STEP's body that tries the
;     third group, so that it can be named.
;   - Generated, per relation and per head KW that has a rule there:
;       <relation>-OF-REDEX-<KW>   on a list of shape KW the relation is the
;                                  rules of KW, tried in order
;     and <relation>-OF-REDEX-WITHOUT-RULE for every other head.
;   - TRY-RULES-OF-PURE-RULES, -READ-RULES, -OWN-RULES: for a list L of shape
;     KW, TRY-RULES over the rules that RULES-FOR gives for KW's place is the
;     relation on L. With TRY-RULES-OF-RULES-FOR this is the statement that
;     the machine's table is STEP's order.
;   - On v ++ (i) ++ r with R not empty no pure and no read rule fires
;     (STEP_PURE-OF-VALS-INSTR-REST, STEP_READ/SPLIT-OF-VALS-INSTR-REST).
;   - The exit statements of V1 for nop, binop and local.get.
; The relation functions are opened; no rule function is.
(in-package "WE")
(include-book "shape")

(set-prover-step-limit 2000000)

(in-theory (disable mv-nth value-head-p))

; ---------------------------------------------------------------------------
; The three groups of rule functions

(make-event
 (let ((wrld (w state)))
   `(progn
      (defconst *pure-rule-fns*
        ',(rule-calls (getpropc 'w3t::step_pure 'acl2::unnormalized-body nil wrld)))
      (defconst *read-rule-fns*
        ',(rule-calls (getpropc 'w3t::step_read/split 'acl2::unnormalized-body nil wrld)))
      (defconst *own-rule-fns*
        ',(set-difference-eq (rule-calls (getpropc 'w3t::step 'acl2::unnormalized-body nil wrld))
                             *skipped-step-rules*)))))

; the elements of RULES that are in SET, in the order of RULES
(defun rules-in (rules set)
  (declare (xargs :guard t))
  (cond ((atom rules) nil)
        ((sym-member (car rules) set) (cons (car rules) (rules-in (cdr rules) set)))
        (t (rules-in (cdr rules) set))))

(defun pure-rules (rules) (declare (xargs :guard t)) (rules-in rules *pure-rule-fns*))
(defun read-rules (rules) (declare (xargs :guard t)) (rules-in rules *read-rule-fns*))
(defun own-rules (rules) (declare (xargs :guard t)) (rules-in rules *own-rule-fns*))

; the place of the rules whose redex ends with an element of head KW
(defun head-place (kw)
  (declare (xargs :guard t))
  (case kw
    (:label_%{%}% '(:entry :l))
    (:handler_%{%}% '(:entry :h))
    (:frame_%{%}% '(:entry :f))
    (otherwise (list :op kw))))

; --- TRY-RULES over the table is TRY-RULES over the three groups in turn ----

(defthm try-rules-of-append
  (equal (try-rules (append a b) z l)
         (if (mv-nth 0 (try-rules a z l))
             (try-rules a z l)
           (try-rules b z l))))

; every entry of the table is its pure rules, then its read rules, then its
; own rules
(defun places-ordered-p (al)
  (if (atom al)
      t
    (and (equal (cdr-t (car al))
                (append (pure-rules (cdr-t (car al)))
                        (append (read-rules (cdr-t (car al)))
                                (own-rules (cdr-t (car al))))))
         (places-ordered-p (cdr al)))))

(defthm rules-of-assoc-when-places-ordered-p
  (implies (places-ordered-p al)
           (equal (append (pure-rules (cdr-t (assoc-equal place al)))
                          (append (read-rules (cdr-t (assoc-equal place al)))
                                  (own-rules (cdr-t (assoc-equal place al)))))
                  (cdr-t (assoc-equal place al))))
  :hints (("Goal" :induct (assoc-equal place al)
                  :in-theory (disable pure-rules read-rules own-rules))))

(defthm rules-for-is-pure-read-own
  (equal (append (pure-rules (rules-for place))
                 (append (read-rules (rules-for place))
                         (own-rules (rules-for place))))
         (rules-for place))
  :hints (("Goal" :in-theory (disable pure-rules read-rules own-rules))))

(defthm try-rules-of-rules-for
  (equal (try-rules (rules-for place) z l)
         (if (mv-nth 0 (try-rules (pure-rules (rules-for place)) z l))
             (try-rules (pure-rules (rules-for place)) z l)
           (if (mv-nth 0 (try-rules (read-rules (rules-for place)) z l))
               (try-rules (read-rules (rules-for place)) z l)
             (try-rules (own-rules (rules-for place)) z l))))
  :hints (("Goal" :in-theory (disable rules-for-is-pure-read-own try-rules rules-for
                                      pure-rules read-rules own-rules)
                  :use rules-for-is-pure-read-own)))

(in-theory (disable try-rules-of-rules-for))

; a head that the table does not have has no rules
(defun place-kws (al)
  (if (atom al) nil (cons (car-t (cdr-t (car-t (car al)))) (place-kws (cdr al)))))

(defthm assoc-of-op-when-not-in-place-kws
  (implies (not (member-equal kw (place-kws al)))
           (equal (assoc-equal (list :op kw) al) nil)))

(defconst *known-heads*
  (list* :label_%{%}% :handler_%{%}% :frame_%{%}% (place-kws *rule-places*)))

(defthm rules-for-of-head-place-when-not-known
  (implies (not (member-equal kw *known-heads*))
           (equal (rules-for (head-place kw)) nil))
  :hints (("Goal" :in-theory (disable assoc-equal (:e place-kws)))))

(in-theory (disable rules-in pure-rules read-rules own-rules head-place rules-for
                    places-ordered-p place-kws))

; ---------------------------------------------------------------------------
; STEP-OWN: what STEP tries after its two relations and its four context
; rules. The body is read from STEP's own.

(defun step-rest (term n)               ; TERM is ((lambda (%r ..) (if %r %r REST)) ..)
  (declare (xargs :mode :program))
  (if (zp n) term (step-rest (cadddr (caddr (car term))) (1- n))))

(make-event
 `(defun step-own (w3t::%a0)
    ,(step-rest (getpropc 'w3t::step 'acl2::unnormalized-body nil (w state))
                (len *skipped-step-rules*))))

(defthm step-opener-with-step-own
  (implies (syntaxp (and (consp c) (eq (car c) 'cons)))
           (equal (w3t::step c)
                  (or (w3t::step/r-pure c) (w3t::step/r-read c)
                      (w3t::step/r-ctxt-instrs c) (w3t::step/r-ctxt-label c)
                      (w3t::step/r-ctxt-handler c) (w3t::step/r-ctxt-frame c)
                      (step-own c))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(step-own))
                  :expand ((w3t::step c)))))

(in-theory (disable step-own step-opener-with-step-own))

(theory-invariant (incompatible (:rewrite step-opener) (:rewrite step-opener-with-step-own)))

; ---------------------------------------------------------------------------
; Per relation and per head, generated

; THROW_REF-INSTRS asks for an exception reference or THROW_REF at
; FIRST-NONVAL; the first is the head of a value
(defthm not-ref.exn_addr-when-not-value-head
  (implies (not (value-head-p x)) (not (equal x :ref.exn_addr)))
  :hints (("Goal" :in-theory (enable value-head-p))))

(defthm not-ref.exn_addr-when-not-value-head-2
  (implies (not (value-head-p x)) (not (equal :ref.exn_addr x)))
  :hints (("Goal" :in-theory (enable value-head-p))))

(defun relation-fns (rel)               ; :pure :read :own
  (declare (xargs :mode :program))
  (case rel (:pure *pure-rule-fns*) (:read *read-rule-fns*) (t *own-rule-fns*)))

(defun relation-name (rel)
  (declare (xargs :mode :program))
  (case rel (:pure "STEP_PURE") (:read "STEP_READ/SPLIT") (t "STEP-OWN")))

(defun relation-fn (rel)
  (declare (xargs :mode :program))
  (case rel (:pure 'w3t::step_pure) (:read 'w3t::step_read/split) (t 'step-own)))

(defun relation-call (rel)              ; the relation on the list L in state Z
  (declare (xargs :mode :program))
  (if (eq rel :pure) '(w3t::step_pure l) `(,(relation-fn rel) (list :|%;%| z l))))

; the heads on which a rule of the relation fires that is not a rule of the
; head's place: TRAP-INSTRS (pure) and THROW_REF-INSTRS (read)
(defun relation-excluded (rel)
  (declare (xargs :mode :program))
  (case rel (:pure '(:trap)) (:read '(:throw_ref)) (t nil)))

(defun rules-with-kw (kw fns)
  (declare (xargs :mode :program))
  (cond ((endp fns) nil)
        ((equal (shape-kw (car fns)) kw) (cons (car fns) (rules-with-kw kw (cdr fns))))
        (t (rules-with-kw kw (cdr fns)))))

(defun kws-of (fns acc)                 ; the heads of FNS, each once, in order
  (declare (xargs :mode :program))
  (cond ((endp fns) (reverse acc))
        ((or (null (shape-kw (car fns))) (member-eq (shape-kw (car fns)) acc))
         (kws-of (cdr fns) acc))
        (t (kws-of (cdr fns) (cons (shape-kw (car fns)) acc)))))

(defun rule-calls-on (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (rule-call (car fns)) (rule-calls-on (cdr fns)))))

(defun redex-lemma-name (rel kw)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (concatenate 'string (relation-name rel) "-OF-REDEX-" (symbol-name kw)) 'we::here))

(defun redex-lemma (rel kw)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 200000
                   (defthm ,(redex-lemma-name rel kw)
                     (implies (redex-shape-p ,kw l)
                              (equal ,(relation-call rel)
                                     (or ,@(rule-calls-on (rules-with-kw kw (relation-fns rel))))))
                     :hints (("Goal" :in-theory (enable ,(relation-fn rel)) :do-not-induct t))))
                 (value-triple (cw "REDEX ~s0 ~x1~%" ,(relation-name rel) ,kw)))
          (value-triple (cw "REDEX-FAILED ~s0 ~x1~%" ,(relation-name rel) ,kw)))))

(defun redex-lemmas (rel kws)
  (declare (xargs :mode :program))
  (cond ((endp kws) nil)
        ((member-eq (car kws) (relation-excluded rel)) (redex-lemmas rel (cdr kws)))
        (t (cons (redex-lemma rel (car kws)) (redex-lemmas rel (cdr kws))))))

(defun redex-lemmas-missing (rel kws wrld)
  (declare (xargs :mode :program))
  (cond ((endp kws) nil)
        ((getpropc (redex-lemma-name rel (car kws)) 'acl2::theorem nil wrld)
         (redex-lemmas-missing rel (cdr kws) wrld))
        (t (cons (car kws) (redex-lemmas-missing rel (cdr kws) wrld)))))

; every head with a rule in the relation has its lemma, but the excluded ones
(defun redex-census (rel)
  (declare (xargs :mode :program))
  `(make-event
    (let* ((kws (kws-of (relation-fns ,rel) nil))
           (missing (redex-lemmas-missing ,rel kws (w state))))
      (if (equal missing (intersection-eq kws (relation-excluded ,rel)))
          (value `(value-triple (cw "REDEX-CENSUS ~s0: ~x1 heads, no lemma for ~x2~%"
                                    ,(relation-name ,rel) ,(len kws) ',missing)))
        (er soft 'dispatch "~s0: the heads with no lemma are ~x1." (relation-name ,rel) missing)))))

; the other heads: no rule of the relation fires
(defun without-rule-lemma (rel)
  (declare (xargs :mode :program))
  `(defthm ,(intern-in-package-of-symbol
             (concatenate 'string (relation-name rel) "-OF-REDEX-WITHOUT-RULE") 'we::here)
     (implies (and (redex-shape-p kw l)
                   (not (member-equal kw ',(union-eq (relation-excluded rel)
                                                     (kws-of (relation-fns rel) nil)))))
              (equal ,(relation-call rel) nil))
     :hints (("Goal" :in-theory (enable ,(relation-fn rel)) :do-not-induct t))))

(defun relation-result (rel)            ; what APPLY-RULE makes of the relation's result
  (declare (xargs :mode :program))
  (let ((call (relation-call rel)))
    (if (eq rel :own)
        `(if ,call
             (mv t (car-t (drop-n 1 (car ,call))) (car-t (drop-n 2 (car ,call))))
           (mv nil z nil))
      `(if ,call (mv t z (car ,call)) (mv nil z nil)))))

(defun try-rules-lemma (rel)
  (declare (xargs :mode :program))
  (let ((filter (case rel (:pure 'pure-rules) (:read 'read-rules) (t 'own-rules)))
        (excluded (relation-excluded rel)))
    `(defthm ,(intern-in-package-of-symbol
               (concatenate 'string "TRY-RULES-OF-" (symbol-name filter)) 'we::here)
       (implies (and (redex-shape-p kw l)
                     ,@(and excluded `((not (equal kw ,(car excluded)))))
                     (equal place (head-place kw)))
                (equal (try-rules (,filter (rules-for place)) z l)
                       ,(relation-result rel)))
       :hints (("Goal" :cases ((member-equal kw *known-heads*))
                       :in-theory (enable apply-rule (:e head-place) (:e rules-for) (:e ,filter))
                       :do-not-induct t)))))

; on v ++ (i) ++ r, whatever R is: no rule of the relation fires when the
; head of I has none
(defun vals-instr-without-rule-lemma (rel)
  (declare (xargs :mode :program))
  `(defthm ,(intern-in-package-of-symbol
             (concatenate 'string (relation-name rel) "-OF-VALS-INSTR-WITHOUT-RULE") 'we::here)
     (implies (and (vals-p v)
                   (not (value-head-p (car i)))
                   (not (member-equal (car i) ',(union-eq (relation-excluded rel)
                                                          (kws-of (relation-fns rel) nil)))))
              (equal ,(subst '(append v (cons i r)) 'l (relation-call rel)) nil))
     :hints (("Goal" :in-theory (enable ,(relation-fn rel)) :do-not-induct t))))

; on v ++ (i) ++ r with R not empty: no rule of the relation fires
(defun vals-instr-rest-lemma (rel)
  (declare (xargs :mode :program))
  `(defthm ,(intern-in-package-of-symbol
             (concatenate 'string (relation-name rel) "-OF-VALS-INSTR-REST") 'we::here)
     (implies (and (vals-p v)
                   (not (value-head-p (car i)))
                   ,@(and (relation-excluded rel)
                          `((not (equal (car i) ,(car (relation-excluded rel))))))
                   (consp r))
              (equal ,(subst '(append v (cons i r)) 'l (relation-call rel)) nil))
     :hints (("Goal" :in-theory (enable ,(relation-fn rel)) :do-not-induct t))))

(defun relation-events (rel)
  (declare (xargs :mode :program))
  `(progn ,@(redex-lemmas rel (kws-of (relation-fns rel) nil))
          ,(redex-census rel)
          ,(without-rule-lemma rel)
          ,(try-rules-lemma rel)
          ,(vals-instr-without-rule-lemma rel)
          ,(vals-instr-rest-lemma rel)))

; one top-level event each: its step limit is the sum over its lemmas
(set-prover-step-limit 200000000)
(make-event (relation-events :pure))
(make-event (relation-events :read))
(make-event (relation-events :own))
(set-prover-step-limit 2000000)

; ---------------------------------------------------------------------------
; Step/pure and Step/read on v ++ (i) ++ r with R not empty

(defthm step/r-pure-of-vals-instr-rest
  (implies (and (vals-p v) (not (value-head-p (car i))) (not (equal (car i) :trap)) (consp r))
           (equal (w3t::step/r-pure (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-pure))))

(defthm step/r-read-of-vals-instr-rest
  (implies (and (vals-p v) (not (value-head-p (car i))) (not (equal (car i) :throw_ref)) (consp r))
           (equal (w3t::step/r-read (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-read))))

; ---------------------------------------------------------------------------
; The exit statements of V1: for values V and any R, with R or the extra
; values not empty, Step/pure and Step/read do not fire on v ++ (i) ++ r,
; for nop, binop and local.get. Each is two cases, R not empty (above) and
; too many or too few values (the length lemma of the instruction's rules).

(defthm step/r-pure-of-vals-nop-rest
  (implies (and (vals-p v) (equal (car i) :nop) (or (consp v) (consp r)))
           (equal (w3t::step/r-pure (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :cases ((consp r)) :in-theory (enable w3t::step/r-pure))))

(defthm step/r-read-of-vals-nop-rest
  (implies (and (vals-p v) (equal (car i) :nop))
           (equal (w3t::step/r-read (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-read))))

(defthm step/r-pure-of-vals-binop-rest
  (implies (and (vals-p v) (equal (car i) :binop) (or (not (equal (len v) 2)) (consp r)))
           (equal (w3t::step/r-pure (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :cases ((consp r)) :in-theory (enable w3t::step/r-pure))))

(defthm step/r-read-of-vals-binop-rest
  (implies (and (vals-p v) (equal (car i) :binop))
           (equal (w3t::step/r-read (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-read))))

(defthm step/r-pure-of-vals-local.get-rest
  (implies (and (vals-p v) (equal (car i) :local.get))
           (equal (w3t::step/r-pure (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-pure))))

(defthm step/r-read-of-vals-local.get-rest
  (implies (and (vals-p v) (equal (car i) :local.get) (or (consp v) (consp r)))
           (equal (w3t::step/r-read (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :cases ((consp r)) :in-theory (enable w3t::step/r-read))))
