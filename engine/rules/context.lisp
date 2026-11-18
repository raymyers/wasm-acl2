; License: MIT. See the file LICENSE at the top of the repository.
;
; One control entry (plan/wasm-engine/plan2.md V3, items 1 and 2): W3T::STEP
; on a list that is one administrative term, (LABEL_ n x b), (HANDLER_ n x b)
; or (FRAME_ n f b), whose body B steps.
;   - A block whose first element that is not a value has the head BR,
;     RETURN or RETURN_CALL_REF does not step (STEP-OF-VALS-EXIT-INSTR-REST):
;     these heads have no rule of their own.
;   - (EXIT-BODY-P b): the shapes of a body on which one of the 24 rules of an
;     administrative term can fire. Generated, per rule function R:
;       <R>-FAILS-WHEN-NOT-EXIT-BODY
;     from one lemma per search function of these rules,
;       <search>-FAILS-WHEN-NOT-EXIT-BLOCK.
;   - A block of values, an instruction whose head is not a value's, and a
;     rest, if it steps, is not such a body
;     (NOT-EXIT-BODY-P-WHEN-BLOCK-STEPS). So no pure and no read rule fires on
;     a term whose body steps, and STEP is the context rule of the term.
;   - STEP-OF-ADMIN-TERM: the step of the term from the step of its body.
;     STEP-OF-ADMIN-TERM-IN-BLOCK: the same with values before the term and a
;     rest after it, which is one step of the induction on the control stack
;     (machine/op-context.lisp).
; The term is written (ADMIN-TERM k n x b), as MACHINE-ABS builds it. STEP is
; opened one level by STEP-OPENER-WITH-STEP-OWN; a rule function is opened in
; its own generated lemma only.
(in-package "WE")
(include-book "flat")
(local (include-book "arithmetic/top" :dir :system))

(set-prover-step-limit 2000000)

(in-theory (disable mv-nth value-head-p redex-arity admin-term))

; ---------------------------------------------------------------------------
; BR, RETURN and RETURN_CALL_REF: no rule has one of them as the head of its
; redex. They are consumed by the rules of the enclosing administrative term.

(defun exit-head-p (kw)
  (declare (xargs :guard t))
  (member-equal kw '(:br :return :return_call_ref)))

(defthm exit-head-p-forward
  (implies (exit-head-p kw)
           (and (not (value-head-p kw))
                (not (equal kw :trap))
                (not (equal kw :throw_ref))
                (not (equal kw :label_%{%}%))
                (not (equal kw :handler_%{%}%))
                (not (equal kw :frame_%{%}%))))
  :hints (("Goal" :in-theory (enable value-head-p)))
  :rule-classes :forward-chaining)

(defthm step/r-pure-of-vals-exit-instr
  (implies (and (vals-p v) (exit-head-p (car i)))
           (equal (w3t::step/r-pure (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-pure))))

(defthm step/r-read-of-vals-exit-instr
  (implies (and (vals-p v) (exit-head-p (car i)))
           (equal (w3t::step/r-read (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-read))))

(defthm step-own-of-vals-exit-instr
  (implies (and (vals-p v) (exit-head-p (car i)))
           (equal (step-own (list :|%;%| z (append v (cons i r)))) nil)))

(in-theory (disable exit-head-p))

; with any number of operands, as in rules/flat.lisp: by induction on the
; number, since Step/ctxt-instrs tries the smaller numbers
(defthm no-step-below-when-exit-head
  (implies (and (vals-p vals) (exit-head-p (car i)) (natp n) (<= n (+ 1 (len vals))))
           (no-step-below n i z vals))
  :hints (("Goal" :induct (count-up-induct n)
                  :in-theory (e/d (step-opener-with-step-own) (flat-search))
                  :expand ((no-step-below n i z vals)))))

(defthm step-of-operands-exit-instr
  (implies (and (vals-p vals) (exit-head-p (car i)) (natp j) (<= j (len vals)))
           (equal (w3t::step (list :|%;%| z (append (operands j vals) (list i)))) nil))
  :hints (("Goal" :use ((:instance no-step-below-when-exit-head (n (+ 1 (len vals))))
                        (:instance step-of-operands-when-no-step-below (n (+ 1 (len vals)))))
                  :in-theory (disable no-step-below-when-exit-head
                                      step-of-operands-when-no-step-below))))

(defthm step-of-rev-vals-exit-instr
  (implies (and (vals-p vals) (exit-head-p (car i)))
           (equal (w3t::step (list :|%;%| z (append (revappend vals nil) (list i)))) nil))
  :hints (("Goal" :use ((:instance step-of-operands-exit-instr (j (len vals))))
                  :in-theory (disable step-of-operands-exit-instr))))

(defthm flat-search-of-exit-instr
  (implies (and (vals-p vals) (exit-head-p (car i)) (natp k) (<= k (len vals)))
           (equal (flat-search k (revappend vals nil) i r z) nil))
  :hints (("Goal" :induct (search-down-induct k)
                  :in-theory (enable flat-search-when-step-fails)
                  :expand ((flat-search 0 (revappend vals nil) i r z)))))

(defthm step-of-rev-vals-exit-instr-rest
  (implies (and (vals-p vals) (exit-head-p (car i)) (true-listp r))
           (equal (w3t::step (list :|%;%| z (append (revappend vals nil) (cons i r)))) nil))
  :hints (("Goal" :in-theory (enable step-opener-with-step-own) :do-not-induct t)))

; V4 uses this for the bodies (vals ++ (br l) ++ r) and (vals ++ (return) ++ r)
(defthm step-of-vals-exit-instr-rest
  (implies (and (vals-p v) (exit-head-p (car i)) (true-listp r))
           (equal (w3t::step (list :|%;%| z (append v (cons i r)))) nil))
  :hints (("Goal" :use ((:instance step-of-rev-vals-exit-instr-rest (vals (revappend v nil))))
                  :in-theory (disable step-of-rev-vals-exit-instr-rest))))

; ---------------------------------------------------------------------------
; (EXIT-BLOCK-P b): the first element of B that is not a value has the head
; BR, RETURN or RETURN_CALL_REF; or it is a reference that is not a value and
; RETURN_CALL_REF follows it (the two RETURN_CALL_REF rules of a frame match
; the reference by its head only).

(defun exit-block-p (b)
  (or (exit-head-p (car (nth (first-nonval b) b)))
      (and (member-equal (car (nth (first-nonval b) b)) '(:ref.null_addr :ref.func_addr))
           (equal (car (nth (+ 1 (first-nonval b)) b)) :return_call_ref))))

; a value prefix, from the pieces the generated searches match
(defun take-take-induct (a b l)
  (if (or (zp a) (zp b)) (list a b l) (take-take-induct (1- a) (1- b) (cdr l))))

(defthm vals-p-of-take-when-longer-take
  (implies (and (vals-p (take a l)) (<= (nfix b) (nfix a)))
           (vals-p (take b l)))
  :hints (("Goal" :induct (take-take-induct a b l) :in-theory (enable take))))

; Forward chaining, as the VALS-P-WHEN-<match> lemmas of rules/shape.lisp
(defthm vals-p-of-take-from-two-parts
  (implies (and (vals-p (nthcdr a (take b l))) (vals-p (take a l)))
           (vals-p (take b l)))
  :hints (("Goal" :induct (take-take-induct a b l) :in-theory (enable take nthcdr)))
  :rule-classes ((:forward-chaining :trigger-terms ((vals-p (nthcdr a (take b l)))))))

(defthm vals-p-from-take-and-nthcdr
  (implies (and (vals-p (nthcdr a l)) (vals-p (take a l)))
           (vals-p l))
  :hints (("Goal" :induct (cdr-n-induct a l) :in-theory (enable take nthcdr)))
  :rule-classes ((:forward-chaining :trigger-terms ((vals-p (nthcdr a l))))))

(defthm vals-p-of-take-of-1+
  (implies (and (vals-p (take k l)) (natp k) (w3t::val-p (nth k l)))
           (vals-p (take (+ 1 k) l)))
  :hints (("Goal" :induct (cdr-n-induct k l) :in-theory (enable take nth))))

; values, then an element that may be a value, then one that is not
(defthm first-nonval-when-vals-then-reference
  (implies (and (vals-p (take k l)) (natp k) (< (+ 1 k) (len l))
                (not (w3t::val-p (nth (+ 1 k) l))))
           (equal (first-nonval l) (if (w3t::val-p (nth k l)) (+ 1 k) k)))
  :hints (("Goal" :use ((:instance first-nonval-when-vals-then-nonval (k (+ 1 k)))
                        (:instance first-nonval-when-vals-then-nonval)
                        vals-p-of-take-of-1+)
                  :in-theory (disable first-nonval-when-vals-then-nonval vals-p-of-take-of-1+)
                  :do-not-induct t)))

(defthm exit-block-p-when-vals-then-exit-instr
  (implies (and (vals-p (take k l)) (natp k) (exit-head-p (car (nth k l))))
           (exit-block-p l))
  :hints (("Goal" :cases ((< k (len l))) :do-not-induct t)))

(defthm exit-block-p-when-vals-then-reference
  (implies (and (vals-p (take k l)) (natp k)
                (member-equal (car (nth k l)) '(:ref.null_addr :ref.func_addr))
                (equal (car (nth (+ 1 k) l)) :return_call_ref))
           (exit-block-p l))
  :hints (("Goal" :cases ((< (+ 1 k) (len l))) :do-not-induct t
                  :in-theory (e/d (exit-head-p) (first-nonval-when-vals-then-nonval nth)))))

(defthm not-reference-head-when-not-value-head
  (implies (not (value-head-p kw))
           (not (member-equal kw '(:ref.null_addr :ref.func_addr))))
  :hints (("Goal" :in-theory (enable value-head-p))))

(defthm exit-block-p-of-vals-instr-rest
  (implies (and (vals-p v) (not (value-head-p (car i))))
           (iff (exit-block-p (append v (cons i r))) (exit-head-p (car i))))
  :hints (("Goal" :in-theory (disable member-equal) :do-not-induct t)))

(in-theory (disable exit-block-p))

; ---------------------------------------------------------------------------
; The rules of an administrative term, and their searches. Generated: one
; line per lemma in the certification output, a step limit per lemma, a
; census at the end.

(defun entry-rule-fns ()                ; in STEP's order, per kind of term
  (declare (xargs :mode :program))
  (append (rules-for '(:entry :l)) (rules-for '(:entry :h)) (rules-for '(:entry :f))))

(mutual-recursion
 (defun search-calls (term)
   (declare (xargs :mode :program))
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((consp (car term))
          (append (search-calls-list (cdr term)) (search-calls (caddr (car term)))))
         (t (append (and (search-fn-p (car term)) (list (car term)))
                    (search-calls-list (cdr term))))))
 (defun search-calls-list (terms)
   (declare (xargs :mode :program))
   (if (atom terms) nil (append (search-calls (car terms)) (search-calls-list (cdr terms))))))

(defun searches-of-rules (fns wrld)     ; the search functions the rules call
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (union-eq (search-calls (getpropc (car fns) 'acl2::unnormalized-body nil wrld))
              (searches-of-rules (cdr fns) wrld))))

; the list a search function searches is its fourth formal
(defun exit-search-lemma (fn wrld)
  (declare (xargs :mode :program))
  (let ((formals (acl2::formals fn wrld)))
    `(make-event
      '(:or (progn (with-prover-step-limit 500000
                     (defthm ,(lemma-name fn "-FAILS-WHEN-NOT-EXIT-BLOCK")
                       (implies (not (exit-block-p ,(nth 3 formals)))
                                (equal (,fn ,@formals) nil))
                       :hints (("Goal" :induct (,fn ,@formals)
                                       :in-theory (enable ,fn exit-head-p)))))
                   (value-triple (cw "EXIT-SEARCH ~x0~%" ',fn)))
            (value-triple (cw "EXIT-SEARCH-FAILED ~x0~%" ',fn))))))

(defun exit-search-lemmas (fns wrld)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (cons (exit-search-lemma (car fns) wrld) (exit-search-lemmas (cdr fns) wrld))))

; RETURN_CALL_REF-FRAME-ADDR has two searches, one inside the other. The
; inner one, by hand: what it found, and that the outer one calls it on
; prefixes of its own list.
(defthm step_read/split/search118-shape
  (implies (w3t::step_read/split/search118 k lo hi t98 t97 t96 t95 t94 z)
           (and (vals-p t98)
                (equal (car (nth (+ -1 (len t97)) t97)) :ref.func_addr)
                (equal (car (nth (+ -1 (len t96)) t96)) :return_call_ref)))
  :hints (("Goal" :induct (w3t::step_read/split/search118 k lo hi t98 t97 t96 t95 t94 z)
                  :in-theory (enable w3t::step_read/split/search118)))
  :rule-classes nil)

(defthm step_read/split/search118-fails-when-not-exit-block
  (implies (and (not (exit-block-p l)) (natp k) (<= 2 k))
           (equal (w3t::step_read/split/search118 j lo hi (take (+ -2 k) l) (take (+ -1 k) l)
                                                  (take k l) t95 t94 z)
                  nil))
  :hints (("Goal" :use ((:instance step_read/split/search118-shape
                                   (k j) (t98 (take (+ -2 k) l)) (t97 (take (+ -1 k) l))
                                   (t96 (take k l)))
                        (:instance exit-block-p-when-vals-then-reference (k (+ -2 k))))
                  :in-theory (disable exit-block-p-when-vals-then-reference)
                  :do-not-induct t)))

; one top-level event: its step limit is the sum over the lemmas
(set-prover-step-limit 100000000)
(make-event `(progn ,@(exit-search-lemmas (searches-of-rules (entry-rule-fns) (w state))
                                          (w state))))
(set-prover-step-limit 2000000)

(make-event
 (let* ((fns (searches-of-rules (entry-rule-fns) (w state)))
        (missing (lemmas-missing fns "" "-FAILS-WHEN-NOT-EXIT-BLOCK" (w state))))
   (if missing
       (er soft 'context "No exit-block lemma: ~x0." missing)
     (value `(value-triple (cw "EXIT-SEARCH-CENSUS ~x0 searches: ~x0 lemmas~%" ,(len fns)))))))

; ---------------------------------------------------------------------------
; (EXIT-BODY-P b): a body on which a rule of the enclosing administrative
; term can fire: values (label-vals, ...), TRAP alone (trap-label, ...), an
; EXIT-BLOCK-P (br-label-zero, return-frame, ...), or an exception reference
; and THROW_REF (throw_ref-label, ...).

(defun exn-throw-p (b)                  ; ((:ref.exn_addr a) (:throw_ref))
  (and (consp b) (consp (car b)) (equal (car (car b)) :ref.exn_addr)
       (consp (cdr (car b))) (null (cddr (car b)))
       (equal (cdr b) '((:throw_ref)))))

(defun exit-body-p (b)
  (or (vals-p b) (equal b '((:trap))) (exit-block-p b) (exn-throw-p b)))

(defun exit-body-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 500000
                   (defthm ,(lemma-name fn "-FAILS-WHEN-NOT-EXIT-BODY")
                     (implies (not (exit-body-p (cadddr (car l))))
                              (equal ,(rule-call fn) nil))
                     :hints (("Goal" :in-theory (enable ,fn) :do-not-induct t))))
                 (value-triple (cw "EXIT-BODY ~x0~%" ',fn)))
          (value-triple (cw "EXIT-BODY-FAILED ~x0~%" ',fn)))))

(defun exit-body-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (exit-body-lemma (car fns)) (exit-body-lemmas (cdr fns)))))

(set-prover-step-limit 100000000)
(make-event `(progn ,@(exit-body-lemmas (entry-rule-fns))))
(set-prover-step-limit 2000000)

(make-event
 (let* ((fns (entry-rule-fns))
        (missing (lemmas-missing fns "" "-FAILS-WHEN-NOT-EXIT-BODY" (w state))))
   (if missing
       (er soft 'context "No exit-body lemma: ~x0." missing)
     (value `(value-triple (cw "EXIT-BODY-CENSUS ~x0 rules: ~x0 lemmas~%" ,(len fns)))))))

; an exception reference that is a value, and THROW_REF: C3 of
; rules/terminal.lisp
(defthm step-of-exn-throw
  (implies (and (exn-throw-p b) (w3t::val-p (car b)))
           (equal (w3t::step (list :|%;%| z b)) nil))
  :hints (("Goal" :use ((:instance step-of-uncaught-exception (a (cadr (car b)))))
                  :in-theory (disable step-of-uncaught-exception))))

(defthm val-p-of-car-when-exn-throw-p
  (implies (and (vals-p v) (not (value-head-p (car i))) (exn-throw-p (append v (cons i r))))
           (w3t::val-p (car (append v (cons i r)))))
  :hints (("Goal" :do-not-induct t :expand ((vals-p v)))))

; a block of values and an administrative term is none of these shapes
(defthm admin-head-forward
  (implies (member-equal (car i) *admin-heads*)
           (and (not (equal i '(:trap))) (not (equal i '(:throw_ref)))
                (not (value-head-p (car i))) (not (exit-head-p (car i)))))
  :hints (("Goal" :in-theory (enable value-head-p exit-head-p)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((member-equal (car i)
                                                '(:label_%{%}% :handler_%{%}% :frame_%{%}%))))))

(defthm vals-then-instr-is-not-one-instr
  (implies (and (vals-p u) (not (w3t::val-p j)) (not (equal i j)))
           (not (equal (append u (cons i r)) (list j))))
  :hints (("Goal" :cases ((consp u)) :expand ((vals-p u)) :do-not-induct t)))

(defthm exn-throw-p-of-vals-admin-term-rest
  (implies (and (vals-p v) (member-equal (car i) *admin-heads*))
           (not (exn-throw-p (append v (cons i r)))))
  :hints (("Goal" :cases ((consp v)) :expand ((vals-p v)) :do-not-induct t)))

(in-theory (disable exn-throw-p))

(defthm vals-p-of-append-of-vals-and-instr
  (implies (not (w3t::val-p i)) (not (vals-p (append v (cons i r)))))
  :hints (("Goal" :induct (len v))))

; V3 item 2: a block that steps is not the body of an exit. The block is
; values, an instruction whose head is not a value's, and a rest: what the
; machine has inside every control entry.
(defthm not-exit-body-p-when-block-steps
  (implies (and (vals-p v) (not (value-head-p (car i))) (true-listp r)
                (w3t::step (list :|%;%| z (append v (cons i r)))))
           (not (exit-body-p (append v (cons i r)))))
  :hints (("Goal" :use ((:instance step-of-exn-throw (b (append v (cons i r)))))
                  :in-theory (disable step-of-exn-throw car-of-append)
                  :do-not-induct t))
  :rule-classes nil)

(defthm not-exit-body-p-of-vals-admin-term-rest
  (implies (and (vals-p v) (member-equal (car i) *admin-heads*))
           (not (exit-body-p (append v (cons i r)))))
  :hints (("Goal" :in-theory (disable member-equal (:e member-equal)) :do-not-induct t)))

(in-theory (disable exit-body-p))

; ---------------------------------------------------------------------------
; STEP on one administrative term whose body is not the body of an exit: no
; pure and no read rule fires, Step/ctxt-instrs has nothing around the term,
; and STEP has no rule of its own for it. So STEP is its context rule.

(defthm step_pure-of-admin-term-when-body-not-exit
  (implies (and (member-equal kw *admin-heads*) (not (exit-body-p b)))
           (equal (w3t::step_pure (list (list kw n x b))) nil))
  :hints (("Goal" :do-not-induct t)))

(defthm step_read/split-of-admin-term-when-body-not-exit
  (implies (and (member-equal kw *admin-heads*) (not (exit-body-p b)))
           (equal (w3t::step_read/split (list :|%;%| z (list (list kw n x b)))) nil))
  :hints (("Goal" :do-not-induct t)))

(defthm step/r-ctxt-instrs-of-one-instr
  (implies (not (w3t::val-p i))
           (equal (w3t::step/r-ctxt-instrs (list :|%;%| z (list i))) nil))
  :hints (("Goal" :use ((:instance step/r-ctxt-instrs-becomes-flat-search (x nil) (r nil)))
                  :in-theory (disable step/r-ctxt-instrs-becomes-flat-search)
                  :expand ((flat-search 0 nil i nil z)))))

(defthm step-own-of-admin-term
  (implies (member-equal kw *admin-heads*)
           (equal (step-own (list :|%;%| z (list (list kw n x b)))) nil))
  :hints (("Goal" :use ((:instance step-own-of-redex-without-rule (l (list (list kw n x b)))))
                  :in-theory (disable step-own-of-redex-without-rule))))

(defthm step-of-admin-term-is-context-rule
  (implies (and (member-equal kw *admin-heads*) (not (exit-body-p b)))
           (equal (w3t::step (list :|%;%| z (list (list kw n x b))))
                  (or (w3t::step/r-ctxt-label (list :|%;%| z (list (list kw n x b))))
                      (w3t::step/r-ctxt-handler (list :|%;%| z (list (list kw n x b))))
                      (w3t::step/r-ctxt-frame (list :|%;%| z (list (list kw n x b)))))))
  :hints (("Goal" :in-theory (e/d (step-opener-with-step-own w3t::step/r-pure w3t::step/r-read)
                                  (member-equal))
                  :do-not-induct t)))

; The three context rules on a body that steps. INNER is the step of the
; body; the size test of each rule is linear arithmetic over %SIZE-OF-CONS.
(defthm step/r-ctxt-label-of-stepping-body
  (implies (and (true-listp x) (true-listp b)
                (equal inner (w3t::step (list :|%;%| z b)))
                inner)
           (equal (w3t::step/r-ctxt-label (list :|%;%| z (list (list :label_%{%}% n x b))))
                  (list (list :|%;%| (cadr (car inner))
                              (list (list :label_%{%}% n x (caddr (car inner))))))))
  :hints (("Goal" :expand ((w3t::step/r-ctxt-label
                            (list :|%;%| z (list (list :label_%{%}% n x b)))))
                  :do-not-induct t)))

(defthm step/r-ctxt-handler-of-stepping-body
  (implies (and (true-listp x) (true-listp b)
                (equal inner (w3t::step (list :|%;%| z b)))
                inner)
           (equal (w3t::step/r-ctxt-handler (list :|%;%| z (list (list :handler_%{%}% n x b))))
                  (list (list :|%;%| (cadr (car inner))
                              (list (list :handler_%{%}% n x (caddr (car inner))))))))
  :hints (("Goal" :expand ((w3t::step/r-ctxt-handler
                            (list :|%;%| z (list (list :handler_%{%}% n x b)))))
                  :do-not-induct t)))

; the body of a frame steps in the frame of the term, F2; the frame around
; the term, F, is kept
(defthm step/r-ctxt-frame-of-stepping-body
  (implies (and (true-listp b)
                (equal inner (w3t::step (list :|%;%| (list :|%;%| s f2) b)))
                inner
                (state-shape-p (cadr (car inner))))
           (equal (w3t::step/r-ctxt-frame
                   (list :|%;%| (list :|%;%| s f) (list (list :frame_%{%}% n f2 b))))
                  (list (list :|%;%| (list :|%;%| (cadr (cadr (car inner))) f)
                              (list (list :frame_%{%}% n (caddr (cadr (car inner)))
                                          (caddr (car inner))))))))
  :hints (("Goal" :expand ((w3t::step/r-ctxt-frame
                            (list :|%;%| (list :|%;%| s f) (list (list :frame_%{%}% n f2 b)))))
                  :in-theory (enable state-shape-p)
                  :do-not-induct t)))

; V3 item 1. K is :l, :h or :f, as in a control entry of the machine; X is
; the label's continuation, the handler's clauses, or the frame of the term.
; INNER is the step of the body, in the frame X for a frame and in F
; otherwise.
(defthm step-of-admin-term
  (implies (and (member-equal k '(:l :h :f))
                (or (equal k :f) (true-listp x))
                (true-listp b) (not (exit-body-p b))
                (equal inner (w3t::step (list :|%;%| (list :|%;%| s (if (equal k :f) x f)) b)))
                inner
                (state-shape-p (cadr (car inner))))
           (equal (w3t::step (list :|%;%| (list :|%;%| s f) (list (admin-term k n x b))))
                  (list (list :|%;%|
                              (list :|%;%| (cadr (cadr (car inner)))
                                    (if (equal k :f) f (caddr (cadr (car inner)))))
                              (list (admin-term k n
                                                (if (equal k :f) (caddr (cadr (car inner))) x)
                                                (caddr (car inner))))))))
  :hints (("Goal" :in-theory (enable admin-term) :do-not-induct t)))

(defthm admin-head-of-admin-term
  (member-equal (car (admin-term k n x b)) '(:label_%{%}% :handler_%{%}% :frame_%{%}%))
  :hints (("Goal" :in-theory (enable admin-term))))

; with values before the term and a rest after it (rules/flat.lisp when
; there is one of them, the lemma above when there is none)
(defthm step-of-admin-term-in-block
  (implies (and (member-equal k '(:l :h :f))
                (or (equal k :f) (true-listp x))
                (true-listp b) (not (exit-body-p b))
                (vals-p v) (true-listp r)
                (equal inner (w3t::step (list :|%;%| (list :|%;%| s (if (equal k :f) x f)) b)))
                inner
                (state-shape-p (cadr (car inner))))
           (equal (w3t::step (list :|%;%| (list :|%;%| s f)
                                   (append v (cons (admin-term k n x b) r))))
                  (list (list :|%;%|
                              (list :|%;%| (cadr (cadr (car inner)))
                                    (if (equal k :f) f (caddr (cadr (car inner)))))
                              (append v (cons (admin-term k n
                                                          (if (equal k :f)
                                                              (caddr (cadr (car inner)))
                                                            x)
                                                          (caddr (car inner)))
                                              r))))))
  :hints (("Goal" :cases ((or (consp v) (consp r)))
                  :in-theory (disable member-equal)
                  :do-not-induct t)))
