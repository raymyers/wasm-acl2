; License: MIT. See the file LICENSE at the top of the repository.
;
; Exits and propagation (plan/wasm-engine/plan2.md V4): W3T::STEP where the
; machine applies a rule that is not the rule of an opcode on its operands.
;   - Generated: the instructions of the 12 pure and read rules that return
;     what a search found are a true list (<R>-INSTRS-TRUE-LISTP, the rules
;     that rules/flat.lisp left: *INSTRS-NOT-YET*), from one lemma per search.
;     Every pure and every read rule has the lemma now.
;   - An administrative term (LABEL_, HANDLER_, FRAME_) on which one of its 24
;     rules fires. They are pure or read rules, which STEP tries before the
;     context rules, so nothing is asked of the body: STEP of the term is the
;     first rule of the machine's table that fires
;     (STEP-OF-ADMIN-TERM-WHEN-RULE-FIRES), also with values before the term
;     and a rest after it (STEP-OF-EXIT-TERM).
;   - A block  val* TRAP instr*  or  val* THROW_REF instr*  on which
;     TRAP-INSTRS or THROW_REF-INSTRS fires (STEP-OF-BLOCK-RULE).
;     THROW_REF-INSTRS fires only with an exception reference before the
;     THROW_REF (EXN-BEFORE-THROW-P), so not where THROW_REF-NULL does.
;   - THROW_REF under a null reference: the rule THROW_REF-NULL on the
;     reference and the instruction, in a block
;     (STEP-OF-NULL-THROW_REF-BLOCK). The head THROW_REF is the one that
;     rules/flat.lisp excludes; the search of Step/ctxt-instrs is the same.
; STEP is opened one level by STEP-OPENER-WITH-STEP-OWN; a rule function is
; opened in its own lemma only.
(in-package "WE")
(include-book "context")
(local (include-book "arithmetic/top" :dir :system))

(set-prover-step-limit 2000000)

(in-theory (disable mv-nth value-head-p redex-arity admin-term try-rules apply-rule))

; ---------------------------------------------------------------------------
; What the 12 rules return. Generated: one line per lemma in the
; certification output, a step limit per lemma, a census at the end.

(defconst *exit-and-block-rules*
  (append (rules-for '(:entry :l)) (rules-for '(:entry :h)) (rules-for '(:entry :f))
          *block-rules*))

(defun search-instrs-lemma (fn wrld)    ; the search returns NIL or a list of one true list
  (declare (xargs :mode :program))
  (let ((formals (acl2::formals fn wrld)))
    `(make-event
      '(:or (progn (with-prover-step-limit 500000
                     (defthm ,(lemma-name fn "-INSTRS-TRUE-LISTP")
                       (true-listp (car (,fn ,@formals)))
                       :hints (("Goal" :induct (,fn ,@formals)
                                       :in-theory (union-theories (theory 'instrs-theory)
                                                                  '(,fn (:induction ,fn)))))))
                   (value-triple (cw "SEARCH-INSTRS ~x0~%" ',fn)))
            (value-triple (cw "SEARCH-INSTRS-NONE ~x0~%" ',fn))))))

(defun search-instrs-lemmas (fns wrld)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (cons (search-instrs-lemma (car fns) wrld) (search-instrs-lemmas (cdr fns) wrld))))

; Three searches by hand. BR-LABEL-ZERO appends the continuation of the label,
; which its rule has tested; RETURN_CALL_REF-FRAME-ADDR has two searches, one
; inside the other.
(defthm step_pure/search51-instrs-true-listp
  (implies (true-listp instrs)
           (true-listp (car (w3t::step_pure/search51 k lo hi l n instrs))))
  :hints (("Goal" :induct (w3t::step_pure/search51 k lo hi l n instrs)
                  :in-theory (union-theories (theory 'instrs-theory)
                                             '(w3t::step_pure/search51
                                               (:induction w3t::step_pure/search51))))))

(defthm step_read/split/search118-instrs-true-listp
  (true-listp (car (w3t::step_read/split/search118 k lo hi t98 t97 t96 t95 t94 z)))
  :hints (("Goal" :induct (w3t::step_read/split/search118 k lo hi t98 t97 t96 t95 t94 z)
                  :in-theory (union-theories (theory 'instrs-theory)
                                             '(w3t::step_read/split/search118
                                               (:induction w3t::step_read/split/search118))))))

(defthm step_read/split/search119-instrs-true-listp
  (true-listp (car (w3t::step_read/split/search119 k lo hi l z)))
  :hints (("Goal" :induct (w3t::step_read/split/search119 k lo hi l z)
                  :in-theory (union-theories (theory 'instrs-theory)
                                             '(w3t::step_read/split/search119
                                               step_read/split/search118-instrs-true-listp
                                               (:induction w3t::step_read/split/search119))))))

(defconst *search-instrs-by-hand*
  '(w3t::step_pure/search51 w3t::step_read/split/search119))

; one top-level event: its step limit is the sum over the lemmas
(set-prover-step-limit 100000000)
(make-event
 `(progn ,@(search-instrs-lemmas
            (set-difference-eq (searches-of-rules *exit-and-block-rules* (w state))
                               *search-instrs-by-hand*)
            (w state))))
(set-prover-step-limit 2000000)

(make-event
 (let* ((fns (searches-of-rules *exit-and-block-rules* (w state)))
        (missing (lemmas-missing fns "" "-INSTRS-TRUE-LISTP" (w state))))
   (if missing
       (er soft 'exits "No instrs lemma for the search: ~x0." missing)
     (value `(value-triple (cw "SEARCH-INSTRS-CENSUS ~x0 searches: ~x0 lemmas~%" ,(len fns)))))))

(defun search-instrs-names (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (cons (lemma-name (car fns) "-INSTRS-TRUE-LISTP") (search-instrs-names (cdr fns)))))

(defun exit-instrs-lemma (fn wrld)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 200000
                   (defthm ,(lemma-name fn "-INSTRS-TRUE-LISTP")
                     (true-listp (car ,(rule-call fn)))
                     :hints (("Goal" :in-theory
                                     (union-theories
                                      (theory 'instrs-theory)
                                      '(,fn ,@(search-instrs-names
                                               (searches-of-rules (list fn) wrld))))
                                     :do-not-induct t))))
                 (value-triple (cw "INSTRS ~x0~%" ',fn)))
          (value-triple (cw "INSTRS-NONE ~x0~%" ',fn)))))

(defun exit-instrs-lemmas (fns wrld)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (cons (exit-instrs-lemma (car fns) wrld) (exit-instrs-lemmas (cdr fns) wrld))))

(set-prover-step-limit 100000000)
(make-event `(progn ,@(exit-instrs-lemmas *instrs-not-yet* (w state))))
(set-prover-step-limit 2000000)

; every pure and every read rule has its lemma: the recorded set is empty
(make-event
 (let* ((fns (append *pure-rule-fns* *read-rule-fns*))
        (missing (lemmas-missing fns "" "-INSTRS-TRUE-LISTP" (w state))))
   (if missing
       (er soft 'exits "No instrs lemma: ~x0." missing)
     (value `(value-triple (cw "INSTRS-CENSUS ~x0 rules: ~x0 lemmas~%" ,(len fns)))))))

; the two relations, on one administrative term
(defthm step_pure-instrs-true-listp-of-admin-term
  (implies (and (redex-shape-p kw l) (member-equal kw *admin-heads*))
           (true-listp (car (w3t::step_pure l))))
  :hints (("Goal" :do-not-induct t)))

(defthm step_read/split-instrs-true-listp-of-admin-term
  (implies (and (redex-shape-p kw l) (member-equal kw *admin-heads*))
           (true-listp (car (w3t::step_read/split (list :|%;%| z l)))))
  :hints (("Goal" :do-not-induct t)))

; ---------------------------------------------------------------------------
; V4 item 1: an administrative term on which a rule of the machine's table
; fires. The table has the pure rules of the head and then the read rules,
; and STEP tries Step/pure and Step/read first.

(defthm redex-shape-p-of-one-term
  (equal (redex-shape-p kw (list (list kw2 n x b))) (equal kw2 kw)))

(defthm try-rules-on-admin-term
  (implies (member-equal kw *admin-heads*)
           (equal (try-rules (rules-for (head-place kw)) z (list (list kw n x b)))
                  (if (w3t::step_pure (list (list kw n x b)))
                      (mv t z (car (w3t::step_pure (list (list kw n x b)))))
                    (if (w3t::step_read/split (list :|%;%| z (list (list kw n x b))))
                        (mv t z (car (w3t::step_read/split
                                      (list :|%;%| z (list (list kw n x b))))))
                      (mv nil z nil)))))
  :hints (("Goal" :in-theory (e/d (try-rules-of-rules-for car-t-of-drop-n nth-of-constant)
                                  (try-rules-of-pure-rules try-rules-of-read-rules
                                   try-rules-of-own-rules member-equal))
                  :use ((:instance try-rules-of-pure-rules (place (head-place kw))
                                   (l (list (list kw n x b))))
                        (:instance try-rules-of-read-rules (place (head-place kw))
                                   (l (list (list kw n x b))))
                        (:instance try-rules-of-own-rules (place (head-place kw))
                                   (l (list (list kw n x b)))))
                  :do-not-induct t)))

; the state is unchanged and the instructions are a true list, whether a rule
; fires or not
(defthm try-rules-on-admin-term-result
  (implies (member-equal kw *admin-heads*)
           (and (equal (mv-nth 1 (try-rules (rules-for (head-place kw)) z (list (list kw n x b))))
                       z)
                (true-listp (mv-nth 2 (try-rules (rules-for (head-place kw)) z
                                                 (list (list kw n x b)))))))
  :hints (("Goal" :in-theory (disable member-equal)
                  :use ((:instance step_pure-instrs-true-listp-of-admin-term
                                   (l (list (list kw n x b))))
                        (:instance step_read/split-instrs-true-listp-of-admin-term
                                   (l (list (list kw n x b)))))
                  :do-not-induct t)))

(defthm step-of-admin-term-when-rule-fires
  (implies (and (member-equal kw *admin-heads*)
                (equal tr (try-rules (rules-for (head-place kw)) z (list (list kw n x b))))
                (mv-nth 0 tr))
           (equal (w3t::step (list :|%;%| z (list (list kw n x b))))
                  (list (list :|%;%| z (mv-nth 2 tr)))))
  :hints (("Goal" :in-theory (e/d (step-opener-with-step-own w3t::step/r-pure w3t::step/r-read)
                                  (member-equal))
                  :use ((:instance step_pure-instrs-true-listp-of-admin-term
                                   (l (list (list kw n x b))))
                        (:instance step_read/split-instrs-true-listp-of-admin-term
                                   (l (list (list kw n x b)))))
                  :do-not-induct t)))

(in-theory (disable try-rules-on-admin-term))

; with values before the term and a rest after it (rules/flat.lisp when there
; is one of them)
(defthm step-of-admin-term-in-block-when-rule-fires
  (implies (and (member-equal kw *admin-heads*) (vals-p v) (true-listp r)
                (equal tr (try-rules (rules-for (head-place kw)) z (list (list kw n x b))))
                (mv-nth 0 tr))
           (equal (w3t::step (list :|%;%| z (append v (cons (list kw n x b) r))))
                  (list (list :|%;%| z (append v (append (mv-nth 2 tr) r))))))
  :hints (("Goal" :cases ((or (consp v) (consp r)))
                  :in-theory (disable member-equal)
                  :do-not-induct t)))

; The same for the term as EXIT-STEP builds it, (ADMIN-TERM k n x b), and the
; rules it tries, those of (:entry k).
(defthm step-of-exit-term
  (implies (and (member-equal k '(:l :h :f)) (vals-p v) (true-listp r)
                (equal tr (try-rules (rules-for (list :entry k)) z (list (admin-term k n x b))))
                (mv-nth 0 tr))
           (and (equal (w3t::step (list :|%;%| z (append v (cons (admin-term k n x b) r))))
                       (list (list :|%;%| z (append v (append (mv-nth 2 tr) r)))))
                (equal (mv-nth 1 tr) z)
                (true-listp (mv-nth 2 tr))))
  :hints (("Goal" :in-theory (e/d (admin-term (:e head-place) (:e rules-for))
                                  (step-of-admin-term-in-block-when-rule-fires
                                   try-rules-on-admin-term-result))
                  :use ((:instance step-of-admin-term-in-block-when-rule-fires (kw :label_%{%}%)
                                   (tr (try-rules (rules-for (head-place :label_%{%}%)) z
                                                  (list (list :label_%{%}% n x b)))))
                        (:instance step-of-admin-term-in-block-when-rule-fires (kw :handler_%{%}%)
                                   (tr (try-rules (rules-for (head-place :handler_%{%}%)) z
                                                  (list (list :handler_%{%}% n x b)))))
                        (:instance step-of-admin-term-in-block-when-rule-fires (kw :frame_%{%}%)
                                   (tr (try-rules (rules-for (head-place :frame_%{%}%)) z
                                                  (list (list :frame_%{%}% n x b)))))
                        (:instance try-rules-on-admin-term-result (kw :label_%{%}%))
                        (:instance try-rules-on-admin-term-result (kw :handler_%{%}%))
                        (:instance try-rules-on-admin-term-result (kw :frame_%{%}%)))
                  :do-not-induct t))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; V4 item 2: the two rules on a whole block. The block is values, an
; instruction of head TRAP or THROW_REF, and a rest.

; Step/pure at a TRAP is TRAP-INSTRS; Step/read at a THROW_REF is
; THROW_REF-NULL or THROW_REF-INSTRS (the heads that rules/dispatch.lisp
; excludes)
(defthm step_pure-of-vals-trap-rest
  (implies (and (vals-p v) (equal (car i) :trap))
           (equal (w3t::step_pure (append v (cons i r)))
                  (w3t::step_pure/r-trap-instrs (append v (cons i r)))))
  :hints (("Goal" :in-theory (enable w3t::step_pure) :do-not-induct t)))

(defthm step_read/split-of-vals-throw_ref-rest
  (implies (and (vals-p v) (equal (car i) :throw_ref))
           (equal (w3t::step_read/split (list :|%;%| z (append v (cons i r))))
                  (or (w3t::step_read/split/r-throw_ref-null
                       (list :|%;%| z (append v (cons i r))))
                      (w3t::step_read/split/r-throw_ref-instrs
                       (list :|%;%| z (append v (cons i r)))))))
  :hints (("Goal" :in-theory (enable w3t::step_read/split) :do-not-induct t)))

(defthm step_pure-of-vals-throw_ref-rest
  (implies (and (vals-p v) (equal (car i) :throw_ref))
           (equal (w3t::step_pure (append v (cons i r))) nil))
  :hints (("Goal" :do-not-induct t)))

; each of the two rules fails at the head of the other
(defthm step_read/split/r-throw_ref-instrs-of-vals-trap-rest
  (implies (and (vals-p v) (equal (car i) :trap))
           (equal (w3t::step_read/split/r-throw_ref-instrs (list :|%;%| z (append v (cons i r))))
                  nil))
  :hints (("Goal" :do-not-induct t)))

(defthm step_pure/r-trap-instrs-of-vals-throw_ref-rest
  (implies (and (vals-p v) (equal (car i) :throw_ref))
           (equal (w3t::step_pure/r-trap-instrs (append v (cons i r))) nil))
  :hints (("Goal" :do-not-induct t)))

; (EXN-BEFORE-THROW-P l): the first element of L that is not a value has the
; head of an exception reference (one that is not a value), or the element
; before it has. THROW_REF-INSTRS fires on such a list only.
(defun exn-before-throw-p (l)
  (or (equal (car (nth (first-nonval l) l)) :ref.exn_addr)
      (and (posp (first-nonval l))
           (equal (car (nth (+ -1 (first-nonval l)) l)) :ref.exn_addr))))

; values, an element that may be a value, THROW_REF. The search keeps
; (cadr (nthcdr k l)) as it is (rules/shape.lisp).
(defthm first-nonval-when-vals-then-exn-throw
  (implies (and (vals-p (take k l)) (natp k)
                (consp (cdr (nthcdr k l)))
                (equal (car (cadr (nthcdr k l))) :throw_ref))
           (equal (first-nonval l) (if (w3t::val-p (nth k l)) (+ 1 k) k)))
  :hints (("Goal" :induct (cdr-n-induct k l)
                  :in-theory (enable first-nonval take nth nthcdr))))

(defthm exn-before-throw-p-when-vals-then-exn-throw
  (implies (and (vals-p (take k l)) (natp k)
                (equal (car (nth k l)) :ref.exn_addr)
                (consp (cdr (nthcdr k l)))
                (equal (car (cadr (nthcdr k l))) :throw_ref))
           (exn-before-throw-p l))
  :hints (("Goal" :in-theory (disable nth) :do-not-induct t)))

; in the machine's block the element before the THROW_REF is the top of the
; operand stack
(defthm exn-before-throw-p-of-rev-vals-throw_ref-rest
  (implies (and (vals-p vals) (equal (car i) :throw_ref))
           (equal (exn-before-throw-p (append (revappend vals nil) (cons i r)))
                  (equal (car (car vals)) :ref.exn_addr)))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable exn-before-throw-p))

(defthm step_read/split/search134-fails-when-not-exn-before-throw
  (implies (not (exn-before-throw-p l))
           (equal (w3t::step_read/split/search134 k lo hi l) nil))
  :hints (("Goal" :induct (w3t::step_read/split/search134 k lo hi l)
                  :in-theory (enable w3t::step_read/split/search134))))

(defthm step_read/split/r-throw_ref-instrs-fails-when-not-exn-before-throw
  (implies (not (exn-before-throw-p l))
           (equal (w3t::step_read/split/r-throw_ref-instrs (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (enable w3t::step_read/split/r-throw_ref-instrs))))

; THROW_REF-NULL needs a null reference before the THROW_REF
(defthm step_read/split/r-throw_ref-null-fails-when-not-null
  (implies (not (equal (car (nth (+ -2 (len l)) l)) :ref.null_addr))
           (equal (w3t::step_read/split/r-throw_ref-null (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (enable w3t::step_read/split/r-throw_ref-null))))

(defthm step_read/split/r-throw_ref-null-of-rev-vals-throw_ref-rest
  (implies (and (vals-p vals) (equal (car i) :throw_ref)
                (not (equal (car (car vals)) :ref.null_addr)))
           (equal (w3t::step_read/split/r-throw_ref-null
                   (list :|%;%| z (append (revappend vals nil) (cons i r))))
                  nil))
  :hints (("Goal" :cases ((consp r))
                  :in-theory (disable step_read/split/r-throw_ref-null-fails-when-not-null)
                  :use ((:instance step_read/split/r-throw_ref-null-fails-when-not-null
                                   (l (append (revappend vals nil) (cons i r)))))
                  :do-not-induct t)))

; The block as ANYPREFIX-STEP has it, VALS the operand stack. TRAP-INSTRS is
; a pure rule and THROW_REF-INSTRS a read rule: STEP tries them before
; Step/ctxt-instrs. Where THROW_REF-INSTRS fires, THROW_REF-NULL, which the
; relation tries before it, does not.
(defthm step-of-block-rule
  (implies (and (vals-p vals) (true-listp r)
                (member-equal (car i) '(:trap :throw_ref))
                (mv-nth 0 (try-rules (rules-for :anyprefix) z
                                     (append (revappend vals nil) (cons i r)))))
           (and (equal (w3t::step (list :|%;%| z (append (revappend vals nil) (cons i r))))
                       (list (list :|%;%| z
                                   (mv-nth 2 (try-rules (rules-for :anyprefix) z
                                                        (append (revappend vals nil)
                                                                (cons i r)))))))
                (equal (mv-nth 1 (try-rules (rules-for :anyprefix) z
                                            (append (revappend vals nil) (cons i r))))
                       z)))
  :hints (("Goal" :cases ((equal (car (car vals)) :ref.exn_addr))
                  :in-theory (enable try-rules apply-rule (:e rules-for)
                                     step-opener-with-step-own w3t::step/r-pure w3t::step/r-read)
                  :do-not-induct t))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; V4 item 3: THROW_REF under a null reference. The redex is the reference
; and the instruction, (operands 1 vals) ++ (i), and the one rule of the
; opcode is THROW_REF-NULL.

; a THROW_REF with no operand does not step
(defthm step-of-throw_ref-instr-alone
  (implies (equal (car i) :throw_ref)
           (equal (w3t::step (list :|%;%| z (list i))) nil))
  :hints (("Goal" :in-theory (e/d (step-opener-with-step-own w3t::step/r-pure w3t::step/r-read
                                   exn-before-throw-p)
                                  (step_pure-of-vals-throw_ref-rest
                                   step_read/split-of-vals-throw_ref-rest))
                  :use ((:instance step_pure-of-vals-throw_ref-rest (v nil) (r nil))
                        (:instance step_read/split-of-vals-throw_ref-rest (v nil) (r nil))
                        (:instance step-own-of-vals-instr-without-rule (v nil) (r nil)))
                  :expand ((first-nonval (list i)))
                  :do-not-induct t)))

(defthm operands-of-0
  (equal (operands 0 vals) nil)
  :hints (("Goal" :in-theory (e/d (operands) (revappend-of-take-becomes-operands)))))

(defthm operands-1-when-one-value
  (implies (and (true-listp vals) (equal (len vals) 1))
           (equal (operands 1 vals) (revappend vals nil)))
  :hints (("Goal" :use operands-of-len :in-theory (disable operands-of-len))))

(defthm no-step-below-1-of-throw_ref
  (implies (equal (car i) :throw_ref)
           (no-step-below 1 i z vals))
  :hints (("Goal" :expand ((no-step-below 1 i z vals)))))

; What OP-STEP makes of THROW_REF-NULL, (mv t z2 res), is STEP's result on
; the redex
(defthm try-rules-on-null-throw_ref-is-step
  (implies (and (vals-p vals) (<= 1 (len vals)) (equal (car i) :throw_ref)
                (equal tr (try-rules (rules-for '(:op :throw_ref)) z
                                     (append (operands 1 vals) (list i))))
                (mv-nth 0 tr))
           (and (equal (w3t::step (list :|%;%| z (append (operands 1 vals) (list i))))
                       (list (list :|%;%| z (mv-nth 2 tr))))
                (equal (mv-nth 1 tr) z)
                (true-listp (mv-nth 2 tr))))
  :hints (("Goal" :in-theory (enable try-rules apply-rule (:e rules-for)
                                     step-opener-with-step-own w3t::step/r-pure w3t::step/r-read)
                  :do-not-induct t))
  :rule-classes nil)

; with more values or a rest, STEP is Step/ctxt-instrs: no pure and no read
; rule fires on the whole block
(defthm step-of-null-throw_ref-block-is-flat-search
  (implies (and (vals-p vals) (true-listp r) (equal (car i) :throw_ref)
                (equal (car (car vals)) :ref.null_addr)
                (or (consp r) (< 1 (len vals)))
                (flat-search (len vals) (revappend vals nil) i r z))
           (equal (w3t::step (list :|%;%| z (append (revappend vals nil) (cons i r))))
                  (flat-search (len vals) (revappend vals nil) i r z)))
  :hints (("Goal" :in-theory (e/d (step-opener-with-step-own w3t::step/r-pure w3t::step/r-read)
                                  (flat-search flat-search-when-step-fails
                                   flat-search-skips-too-few-operands flat-search-at-redex
                                   flat-search-finds-redex))
                  :cases ((consp r))
                  :do-not-induct t)))

; as STEP-OF-FLAT-BLOCK of rules/flat.lisp, for this head: INNER is the step
; of the redex
(defthm step-of-null-throw_ref-block
  (implies (and (vals-p vals) (true-listp r) (equal (car i) :throw_ref)
                (equal (car (car vals)) :ref.null_addr)
                (<= 1 (len vals))
                (equal inner (w3t::step (list :|%;%| z (append (operands 1 vals) (list i)))))
                inner)
           (equal (w3t::step (list :|%;%| z (append (revappend vals nil) (cons i r))))
                  (list (list :|%;%| (cadr (car inner))
                              (append (revappend (nthcdr 1 vals) nil)
                                      (append (caddr (car inner)) r))))))
  :hints (("Goal" :in-theory (disable flat-search flat-search-when-step-fails
                                      flat-search-skips-too-few-operands flat-search-at-redex
                                      flat-search-finds-redex)
                  :cases ((or (consp r) (< 1 (len vals))))
                  :use ((:instance flat-search-finds-redex (a 1)))
                  :do-not-induct t)))

(in-theory (disable step-of-null-throw_ref-block step-of-null-throw_ref-block-is-flat-search))
