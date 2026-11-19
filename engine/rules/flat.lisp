; License: MIT. See the file LICENSE at the top of the repository.
;
; The flat block (plan/wasm-engine/plan2.md V2): W3T::STEP on a list of
; values, one instruction and a rest, with no fact about a control stack.
;   - FLAT-SEARCH: what the search of Step/ctxt-instrs does on x ++ (i) ++ r,
;     X values and I not a value. STEP/SEARCH21 and STEP/R-CTXT-INSTRS are
;     rewritten to it, so no later proof opens them.
;   - Per relation: a rule that fires on a redex has the number of operands
;     that the machine's REDEX-ARITY gives (STEP_PURE-ARITY,
;     STEP_READ/SPLIT-ARITY, STEP-OWN-ARITY), from the <R>-ARITY lemmas.
;   - Generated: the instructions a pure or a read rule returns are a true
;     list (<R>-INSTRS-TRUE-LISTP); the state one of STEP's own rules returns
;     has the shape (:|%;%| s f) (<R>-STATE-SHAPE).
;   - Operand prefix: with fewer operands than its arity, an instruction does
;     not step (NO-STEP-BELOW-ARITY).
;   - STEP-OF-REDEX: on the operands and the instruction alone, STEP is its
;     pure rules, its read rules or its own rules.
;   - STEP-OF-FLAT-BLOCK: if STEP of (z; w ++ (i)) is (z'; is') then STEP of
;     (z; v ++ w ++ (i) ++ r) is (z'; v ++ is' ++ r).
; The operands are named as the machine has them: VALS is its operand stack,
; top first, and the J operands of I are (revappend (take j vals) nil).
; STEP is opened one level by STEP-OPENER-WITH-STEP-OWN; no rule function is
; opened but in its own generated lemma.
(in-package "WE")
(include-book "dispatch")
(include-book "arity")
(local (include-book "arithmetic/top" :dir :system))

(set-prover-step-limit 2000000)

(in-theory (disable mv-nth value-head-p redex-arity))

; ---------------------------------------------------------------------------
; FLAT-SEARCH: the search of Step/ctxt-instrs

(defthm step/match13-of-vals
  (implies (vals-p x) (equal (w3t::step/match13 x) (list (list x))))
  :hints (("Goal" :induct (len x) :in-theory (enable w3t::step/match13))))

(defthm step/iter20-of-true-list
  (implies (true-listp x) (equal (w3t::step/iter20 x) x))
  :hints (("Goal" :induct (len x) :in-theory (enable w3t::step/iter20))))

; K counts down from the number of values, as STEP/SEARCH21 does: the step
; inside is tried on the values from K on and the instruction, so with the
; fewest operands first.
(defun flat-search (k x i r z)
  (declare (xargs :measure (nfix (+ 1 k))))
  (if (not (natp k))
      nil
    (let ((inner (w3t::step (list :|%;%| z (append (nthcdr k x) (list i))))))
      (if (and (or (posp k) (consp r)) inner)
          (list (list :|%;%| (cadr (car inner))
                      (append (take k x) (append (caddr (car inner)) r))))
        (flat-search (1- k) x i r z)))))

(defthm flat-search-when-not-natp
  (implies (not (natp k)) (equal (flat-search k x i r z) nil)))

(defthm step/search21-when-not-natp
  (implies (not (natp k)) (equal (w3t::step/search21 k lo hi l p z c) nil))
  :hints (("Goal" :expand ((w3t::step/search21 k lo hi l p z c)))))

; the size test of the search (rules/step-basics.lisp), in the form the
; rewriter gives its two lists
(defthm %size-of-operands-and-instr
  (implies (and (natp k) (<= k (len x)) (or (posp k) (consp r)) (true-listp x))
           (< (wrt::%size (append (nthcdr k x) (list i)))
              (wrt::%size (append x (cons i r)))))
  :hints (("Goal" :use ((:instance %size-check-of-sublist (l (append x (cons i r)))
                                   (m (+ 1 (- (len x) k))) (z2 z)))
                  :in-theory (disable %size-check-of-sublist)))
  :rule-classes (:rewrite :linear))

(defthm %size-of-all-operands-and-instr
  (implies (and (consp r) (true-listp x))
           (< (wrt::%size (append x (list i)))
              (wrt::%size (append x (cons i r)))))
  :hints (("Goal" :use ((:instance %size-of-operands-and-instr (k 0)))
                  :in-theory (disable %size-of-operands-and-instr)))
  :rule-classes (:rewrite :linear))

(defthm take-under-iff
  (iff (take n l) (not (zp n)))
  :hints (("Goal" :in-theory (enable take))))

; what a step returns, as the search reads it
(defthm step-result-components
  (implies (w3t::step c)
           (and (consp (car (w3t::step c)))
                (equal (car (car (w3t::step c))) :|%;%|)
                (true-listp (cdr (car (w3t::step c))))
                (equal (len (cdr (car (w3t::step c)))) 2)
                (true-listp (caddr (car (w3t::step c))))
                (equal (cdr (w3t::step c)) nil)))
  :hints (("Goal" :use step-result-shape
                  :in-theory (e/d (step-result-p) (step-result-shape)))))

(defthm step/search21-becomes-flat-search
  (implies (and (vals-p x) (not (w3t::val-p i)) (true-listp r) (natp k) (<= k (len x))
                (equal p (len x)))
           (equal (w3t::step/search21 k 0 p (append x (cons i r)) p z
                                      (list :|%;%| z (append x (cons i r))))
                  (flat-search k x i r z)))
  :hints (("Goal" :induct (flat-search k x i r z)
                  :in-theory (disable (:definition flat-search))
                  :expand ((:free (p l c) (w3t::step/search21 k 0 p l p z c))
                           (flat-search k x i r z)
                           (:free (p l c) (w3t::step/search21 0 0 p l p z c))
                           (:free (r) (flat-search 0 x i r z))))))

(defthm step/r-ctxt-instrs-becomes-flat-search
  (implies (and (vals-p x) (not (w3t::val-p i)) (true-listp r))
           (equal (w3t::step/r-ctxt-instrs (list :|%;%| z (append x (cons i r))))
                  (flat-search (len x) x i r z)))
  :hints (("Goal" :in-theory (disable flat-search)
                  :expand ((w3t::step/r-ctxt-instrs (list :|%;%| z (append x (cons i r))))))))

; ---------------------------------------------------------------------------
; The other three context rules need one administrative term

(defthm step/r-ctxt-label-fails-when-not-shape
  (implies (not (redex-shape-p :label_%{%}% l))
           (equal (w3t::step/r-ctxt-label (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (theory 'shape-theory)
                  :expand ((w3t::step/r-ctxt-label (list :|%;%| z l))))))

(defthm step/r-ctxt-handler-fails-when-not-shape
  (implies (not (redex-shape-p :handler_%{%}% l))
           (equal (w3t::step/r-ctxt-handler (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (theory 'shape-theory)
                  :expand ((w3t::step/r-ctxt-handler (list :|%;%| z l))))))

(defthm step/r-ctxt-frame-fails-when-not-shape
  (implies (not (redex-shape-p :frame_%{%}% l))
           (equal (w3t::step/r-ctxt-frame (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (theory 'shape-theory)
                  :expand ((w3t::step/r-ctxt-frame (list :|%;%| z l))))))

; ---------------------------------------------------------------------------
; Per relation: a rule that fires has the operand count of REDEX-ARITY

; the heads for which REDEX-ARITY is not NIL
(defconst *arity-heads*
  '(:unreachable :nop :local.get :global.get :call :call_indirect :memory.size :ref.null :ref.func
    :data.drop :elem.drop :drop :ifelse :br_if :br_table :local.tee :local.set :global.set
    :unop :testop :cvtop :load :memory.grow :ref.cast
    :ref.is_null :ref.as_non_null :br_on_null :br_on_non_null :table.get :throw_ref
    :binop :relop :store :ref.eq :table.set :table.grow
    :select :memory.fill :memory.copy :memory.init :table.fill :table.copy :table.init
    :block :loop :try_table :throw :call_ref))

(defthm redex-arity-when-head-not-supported
  (implies (not (member-equal (car i) *arity-heads*))
           (equal (redex-arity i z vals) nil))
  :hints (("Goal" :in-theory (enable redex-arity entry-kind))))

(defthm redex-arity-of-last-when-not-supported
  (implies (and (redex-shape-p kw l) (not (member-equal kw *arity-heads*)))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) nil))
  :hints (("Goal" :in-theory (disable member-equal))))

(defthm step_pure-arity
  (implies (and (redex-shape-p kw l)
                (w3t::step_pure l)
                (natp (redex-arity (nth (+ -1 (len l)) l) z vals)))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) (+ -1 (len l))))
  :rule-classes nil
  :hints (("Goal" :cases ((member-equal kw *known-heads*)) :do-not-induct t)))

; THROW_REF is excluded as in TRY-RULES-OF-READ-RULES: THROW_REF-INSTRS fires
; on a redex of that head
(defthm step_read/split-arity
  (implies (and (redex-shape-p kw l)
                (w3t::step_read/split (list :|%;%| z l))
                (not (equal kw :throw_ref))
                (natp (redex-arity (nth (+ -1 (len l)) l) z vals)))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) (+ -1 (len l))))
  :rule-classes nil
  :hints (("Goal" :cases ((member-equal kw *known-heads*)) :do-not-induct t)))

; call_ref: every rule needs a reference before the instruction, and the
; three rules for a function need a function reference
(defthm step/r-call_ref-null-fails-when-short
  (implies (not (consp (cdr l)))
           (equal (w3t::step/r-call_ref-null (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (union-theories (theory 'shape-theory)
                                             '(w3t::step/r-call_ref-null)))))

(defthm step/r-call_ref-func-fails-when-not-func
  (implies (or (not (consp (cdr l)))
               (not (equal (car (nth (+ -2 (len l)) l)) :ref.func_addr)))
           (equal (w3t::step/r-call_ref-func (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-call_ref-func))))

(defthm step/r-call_ref-hostfunc-res-fails-when-not-func
  (implies (or (not (consp (cdr l)))
               (not (equal (car (nth (+ -2 (len l)) l)) :ref.func_addr)))
           (equal (w3t::step/r-call_ref-hostfunc-res (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-call_ref-hostfunc-res))))

(defthm step/r-call_ref-hostfunc-div-fails-when-not-func
  (implies (or (not (consp (cdr l)))
               (not (equal (car (nth (+ -2 (len l)) l)) :ref.func_addr)))
           (equal (w3t::step/r-call_ref-hostfunc-div (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-call_ref-hostfunc-div))))

; The hypotheses for call_ref are those of the <R>-ARITY lemmas
; (notes/V1-dispatch.md §4): the top of the machine's operand stack is the
; reference, and a function reference names a natural number.
(defthm step-own-arity
  (implies (and (redex-shape-p kw l)
                (step-own (list :|%;%| (list :|%;%| s f) l))
                (natp (redex-arity (nth (+ -1 (len l)) l) (list :|%;%| s f) vals))
                (or (not (equal kw :call_ref))
                    (not (consp (cdr l)))
                    (and (equal (car vals) (nth (+ -2 (len l)) l))
                         (or (not (equal (car (car vals)) :ref.func_addr))
                             (natp (cadr (car vals)))))))
           (equal (redex-arity (nth (+ -1 (len l)) l) (list :|%;%| s f) vals)
                  (+ -1 (len l))))
  :rule-classes nil
  :hints (("Goal" :cases ((member-equal kw *known-heads*)) :do-not-induct t)))

; ---------------------------------------------------------------------------
; Generated: what a rule returns

(deflabel flat-anchor)

; the instructions of a pure or a read rule are a true list
(deftheory instrs-theory
  (union-theories (theory 'minimal-theory)
    (union-theories (executable-counterpart-theory 'flat-anchor)
      '(true-listp-of-cons true-listp-of-append car-cons cdr-cons))))

(defun instrs-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 200000
                   (defthm ,(lemma-name fn "-INSTRS-TRUE-LISTP")
                     (true-listp (car ,(rule-call fn)))
                     :hints (("Goal" :in-theory (union-theories (theory 'instrs-theory) '(,fn))
                                     :do-not-induct t))))
                 (value-triple (cw "INSTRS ~x0~%" ',fn)))
          (value-triple (cw "INSTRS-NONE ~x0~%" ',fn)))))

(defun instrs-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (instrs-lemma (car fns)) (instrs-lemmas (cdr fns)))))

; The rules that return what a search found: their redex is an administrative
; term or a whole block (V3, V4), never the redex of an opcode.
(defconst *instrs-not-yet*
  '(w3t::step_pure/r-br-label-zero w3t::step_pure/r-br-label-succ
    w3t::step_pure/r-br-handler w3t::step_pure/r-return-frame
    w3t::step_pure/r-return-label w3t::step_pure/r-return-handler
    w3t::step_pure/r-trap-instrs
    w3t::step_read/split/r-return_call_ref-label
    w3t::step_read/split/r-return_call_ref-handler
    w3t::step_read/split/r-return_call_ref-frame-null
    w3t::step_read/split/r-return_call_ref-frame-addr
    w3t::step_read/split/r-throw_ref-instrs))

(defun op-rules (fns)                   ; the rules whose redex ends with an opcode
  (declare (xargs :mode :program))
  (cond ((endp fns) nil)
        ((eq (car (rule-place (car fns))) :op) (cons (car fns) (op-rules (cdr fns))))
        (t (op-rules (cdr fns)))))

; one top-level event: its step limit is the sum over the lemmas
(set-prover-step-limit 100000000)
(make-event `(progn ,@(instrs-lemmas (append *pure-rule-fns* *read-rule-fns*))))
(set-prover-step-limit 2000000)

(make-event
 (let ((missing (lemmas-missing (append *pure-rule-fns* *read-rule-fns*)
                                "" "-INSTRS-TRUE-LISTP" (w state))))
   (if (and (equal missing *instrs-not-yet*)
            (not (intersection-eq missing (op-rules *step-rules*))))
       (value `(value-triple (cw "INSTRS-CENSUS ~x0 rules: ~x1 lemmas; none for ~x2 rules, no rule of an opcode among them~%"
                                 ,(+ (len *pure-rule-fns*) (len *read-rule-fns*))
                                 ,(- (+ (len *pure-rule-fns*) (len *read-rule-fns*)) (len missing))
                                 ,(len missing))))
     (er soft 'flat "No instrs lemma: ~x0. Recorded: ~x1." missing *instrs-not-yet*))))

; the state of one of STEP's own rules has the shape (:|%;%| s f) when the
; state it started from has
(defun state-shape-p (z)
  (declare (xargs :guard t))
  (and (consp z) (equal (car z) :|%;%|) (consp (cdr z)) (consp (cddr z)) (null (cdddr z))))

(defthm state-shape-p-of-list
  (state-shape-p (list :|%;%| s f)))

(defthm rebuild-when-state-shape-p
  (implies (state-shape-p z)
           (equal (list :|%;%| (cadr z) (caddr z)) z)))

; the functions of the specification that change a state: $with_local,
; $with_mem, $add_exninst, ...
(defun state-update-fn-p (fn)
  (declare (xargs :mode :program))
  (let ((s (symbol-name fn)))
    (and (equal (symbol-package-name fn) "W3T")
         (or (and (<= 6 (length s)) (equal (subseq s 0 6) "$WITH_"))
             (and (<= 5 (length s)) (equal (subseq s 0 5) "$ADD_"))))))

(defun state-update-fns (runes)
  (declare (xargs :mode :program))
  (cond ((endp runes) nil)
        ((and (consp (car runes)) (eq (car (car runes)) :definition)
              (state-update-fn-p (cadr (car runes))))
         (cons (cadr (car runes)) (state-update-fns (cdr runes))))
        (t (state-update-fns (cdr runes)))))

(make-event
 `(defconst *state-update-fns*
    ',(state-update-fns (acl2::function-theory-fn :here (w state)))))

(deftheory state-theory
  (union-theories (theory 'minimal-theory)
    (union-theories (executable-counterpart-theory 'flat-anchor)
      (append '(state-shape-p state-shape-p-of-list car-cons cdr-cons) *state-update-fns*))))

(in-theory (disable state-shape-p))

(defun state-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 200000
                   (defthm ,(lemma-name fn "-STATE-SHAPE")
                     (implies (and (,fn (list :|%;%| z l)) (state-shape-p z))
                              (state-shape-p (cadr (car (,fn (list :|%;%| z l))))))
                     :hints (("Goal" :in-theory (union-theories (theory 'state-theory) '(,fn))
                                     :do-not-induct t))))
                 (value-triple (cw "STATE ~x0~%" ',fn)))
          (value-triple (cw "STATE-FAILED ~x0~%" ',fn)))))

(defun state-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (state-lemma (car fns)) (state-lemmas (cdr fns)))))

(set-prover-step-limit 100000000)
(make-event `(progn ,@(state-lemmas *own-rule-fns*)))
(set-prover-step-limit 2000000)

(make-event
 (let ((missing (lemmas-missing *own-rule-fns* "" "-STATE-SHAPE" (w state))))
   (if missing
       (er soft 'flat "No state-shape lemma: ~x0." missing)
     (value `(value-triple (cw "STATE-CENSUS ~x0 rules: ~x0 lemmas~%" ,(len *own-rule-fns*)))))))

; the three relations, on a redex
(defthm step-own-result-shape
  (implies (step-own c) (step-result-p (step-own c)))
  :hints (("Goal" :in-theory (enable step-own) :do-not-induct t)))

(defthm step-own-state-shape
  (implies (and (step-own (list :|%;%| z l)) (state-shape-p z))
           (state-shape-p (cadr (car (step-own (list :|%;%| z l))))))
  :hints (("Goal" :in-theory (enable step-own) :do-not-induct t)))

(defthm step_pure-instrs-true-listp
  (implies (and (redex-shape-p kw l)
                (not (member-equal kw '(:trap :label_%{%}% :handler_%{%}% :frame_%{%}%))))
           (true-listp (car (w3t::step_pure l))))
  :hints (("Goal" :cases ((member-equal kw *known-heads*)) :do-not-induct t)))

(defthm step_read/split-instrs-true-listp
  (implies (and (redex-shape-p kw l)
                (not (member-equal kw '(:throw_ref :label_%{%}% :handler_%{%}% :frame_%{%}%))))
           (true-listp (car (w3t::step_read/split (list :|%;%| z l)))))
  :hints (("Goal" :cases ((member-equal kw *known-heads*)) :do-not-induct t)))

; ---------------------------------------------------------------------------
; The operands, as the machine has them: (operands j vals) is the top J
; values of the stack VALS in the order of the configuration.

(defun operands (j vals)
  (revappend (take j vals) nil))

(defthm vals-p-of-revappend
  (implies (and (vals-p x) (vals-p acc)) (vals-p (revappend x acc))))

(defthm vals-p-of-operands
  (implies (and (vals-p vals) (<= (nfix j) (len vals)))
           (vals-p (operands j vals))))

(defthm len-of-operands
  (equal (len (operands j vals)) (nfix j)))

(defthm nthcdr-of-operands
  (implies (and (natp k) (natp j) (<= k j))
           (equal (nthcdr k (operands j vals)) (operands (- j k) vals))))

(defthm last-of-operands
  (implies (and (posp j) (<= j (len vals)))
           (equal (nth (+ -1 j) (operands j vals)) (car vals))))

(defthm operands-of-len
  (implies (true-listp vals)
           (equal (operands (len vals) vals) (revappend vals nil))))

(defthm revappend-of-take-becomes-operands
  (equal (revappend (take j vals) nil) (operands j vals)))

(in-theory (disable operands))

(theory-invariant (incompatible (:definition operands)
                                (:rewrite revappend-of-take-becomes-operands)))

; An instruction that the machine gives to OP-STEP: not a value, not an
; administrative term, and not TRAP or THROW_REF (V4).
(defun op-instr-p (i)
  (declare (xargs :guard t))
  (and (consp i)
       (not (value-head-p (car i)))
       (not (member-equal (car i) '(:trap :throw_ref :label_%{%}% :handler_%{%}% :frame_%{%}%)))))

(defthm op-instr-p-forward
  (implies (op-instr-p i)
           (and (consp i)
                (not (value-head-p (car i)))
                (not (w3t::val-p i))
                (not (equal (car i) :trap))
                (not (equal (car i) :throw_ref))
                (not (equal (car i) :label_%{%}%))
                (not (equal (car i) :handler_%{%}%))
                (not (equal (car i) :frame_%{%}%))))
  :rule-classes :forward-chaining)

(defthm head-place-of-op-instr
  (implies (op-instr-p i) (equal (head-place (car i)) (list :op (car i))))
  :hints (("Goal" :in-theory (enable head-place))))

(in-theory (disable op-instr-p))

; ---------------------------------------------------------------------------
; With another number of operands than its arity, no rule fires

(defthm step/r-pure-of-operands-when-not-arity
  (implies (and (vals-p vals) (op-instr-p i) (natp j) (<= j (len vals))
                (natp (redex-arity i z vals))
                (not (equal j (redex-arity i z vals))))
           (equal (w3t::step/r-pure (list :|%;%| z (append (operands j vals) (list i)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-pure)
                  :use ((:instance step_pure-arity (l (append (operands j vals) (list i)))
                                   (kw (car i)))))))

(defthm step/r-read-of-operands-when-not-arity
  (implies (and (vals-p vals) (op-instr-p i) (natp j) (<= j (len vals))
                (natp (redex-arity i z vals))
                (not (equal j (redex-arity i z vals))))
           (equal (w3t::step/r-read (list :|%;%| z (append (operands j vals) (list i)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-read)
                  :use ((:instance step_read/split-arity (l (append (operands j vals) (list i)))
                                   (kw (car i)))))))

; a function reference that is a value names a natural number
; (notes/V1-dispatch.md §5)
(defthm natp-of-function-address-when-val-p
  (implies (and (w3t::val-p x) (equal (car x) :ref.func_addr))
           (natp (cadr x)))
  :hints (("Goal" :in-theory (enable w3t::val-p w3t::ref-p w3t::funcaddr-p w3t::addr-p)))
  :rule-classes nil)

(defthm natp-of-function-address-on-stack
  (implies (and (vals-p vals) (equal (car (car vals)) :ref.func_addr))
           (natp (cadr (car vals))))
  :hints (("Goal" :use ((:instance natp-of-function-address-when-val-p (x (car vals)))))))

(defthm step-own-of-operands-when-not-arity
  (implies (and (vals-p vals) (op-instr-p i) (natp j) (<= j (len vals))
                (natp (redex-arity i (list :|%;%| s f) vals))
                (not (equal j (redex-arity i (list :|%;%| s f) vals))))
           (equal (step-own (list :|%;%| (list :|%;%| s f) (append (operands j vals) (list i))))
                  nil))
  :hints (("Goal" :use ((:instance step-own-arity (l (append (operands j vals) (list i)))
                                   (kw (car i)))))))

; ---------------------------------------------------------------------------
; Operand prefix: STEP fails with fewer operands than the arity.
; (no-step-below n i z vals): STEP fails on every (operands m vals) ++ (i),
; m < n.

(defun no-step-below (n i z vals)
  (if (zp n)
      t
    (and (not (w3t::step (list :|%;%| z (append (operands (1- n) vals) (list i)))))
         (no-step-below (1- n) i z vals))))

(defthm no-step-below-of-0
  (no-step-below 0 i z vals))

(defthm step-of-operands-when-no-step-below
  (implies (and (no-step-below n i z vals) (natp n) (natp j) (< j n))
           (equal (w3t::step (list :|%;%| z (append (operands j vals) (list i)))) nil))
  :hints (("Goal" :induct (no-step-below n i z vals))))

; the search of Step/ctxt-instrs on the operands and the instruction alone
; tries fewer operands only
(defthm flat-search-of-operands-when-no-step-below
  (implies (and (no-step-below m i z vals) (natp k) (natp m) (<= k m))
           (equal (flat-search k (operands m vals) i nil z) nil))
  :hints (("Goal" :induct (flat-search k (operands m vals) i nil z)
                  :in-theory (disable no-step-below))))

(in-theory (disable no-step-below (:induction no-step-below)))

(defun count-up-induct (n)
  (if (zp n) n (count-up-induct (1- n))))

(defthm no-step-below-arity
  (implies (and (vals-p vals) (op-instr-p i) (natp n) (<= n (len vals))
                (natp (redex-arity i (list :|%;%| s f) vals))
                (<= n (redex-arity i (list :|%;%| s f) vals)))
           (no-step-below n i (list :|%;%| s f) vals))
  :hints (("Goal" :induct (count-up-induct n)
                  :in-theory (e/d (step-opener-with-step-own) (flat-search))
                  :expand ((no-step-below n i (list :|%;%| s f) vals)))))

; ---------------------------------------------------------------------------
; STEP on the redex: no context rule fires

(defthm step-of-redex
  (implies (and (vals-p vals) (op-instr-p i) (natp j) (<= j (len vals))
                (equal j (redex-arity i (list :|%;%| s f) vals)))
           (equal (w3t::step (list :|%;%| (list :|%;%| s f) (append (operands j vals) (list i))))
                  (or (w3t::step/r-pure
                       (list :|%;%| (list :|%;%| s f) (append (operands j vals) (list i))))
                      (w3t::step/r-read
                       (list :|%;%| (list :|%;%| s f) (append (operands j vals) (list i))))
                      (step-own
                       (list :|%;%| (list :|%;%| s f) (append (operands j vals) (list i)))))))
  :hints (("Goal" :in-theory (e/d (step-opener-with-step-own) (flat-search))
                  :use ((:instance no-step-below-arity (n j)))
                  :do-not-induct t)))

; ---------------------------------------------------------------------------
; The search on the whole block stops at the arity

(defthm flat-search-when-step-fails
  (implies (and (natp k) (not (w3t::step (list :|%;%| z (append (nthcdr k x) (list i))))))
           (equal (flat-search k x i r z) (flat-search (+ -1 k) x i r z))))

(defun count-to-induct (j a)
  (declare (xargs :measure (nfix (- a j))))
  (if (and (natp j) (natp a) (< j a)) (count-to-induct (+ 1 j) a) (list j a)))

(defthm flat-search-skips-too-few-operands
  (implies (and (vals-p vals) (no-step-below a i z vals) (natp a) (<= a (len vals))
                (natp j) (<= j a))
           (equal (flat-search (- (len vals) j) (revappend vals nil) i r z)
                  (flat-search (- (len vals) a) (revappend vals nil) i r z)))
  :hints (("Goal" :induct (count-to-induct j a)
                  :in-theory (disable flat-search))))

(defthm flat-search-at-redex
  (implies (and (vals-p vals) (natp a) (<= a (len vals))
                (or (consp r) (< a (len vals)))
                (w3t::step (list :|%;%| z (append (operands a vals) (list i)))))
           (equal (flat-search (- (len vals) a) (revappend vals nil) i r z)
                  (list (list :|%;%|
                              (cadr (car (w3t::step (list :|%;%| z (append (operands a vals) (list i))))))
                              (append (revappend (nthcdr a vals) nil)
                                      (append (caddr (car (w3t::step
                                                           (list :|%;%| z (append (operands a vals)
                                                                                  (list i))))))
                                              r))))))
  :hints (("Goal" :in-theory (disable flat-search flat-search-when-step-fails)
                  :cases ((equal a (len vals)))
                  :do-not-induct t
                  :expand ((flat-search (+ (- a) (len vals)) (revappend vals nil) i r z)
                           (flat-search 0 (revappend vals nil) i r z)))))

(defthm flat-search-finds-redex
  (implies (and (vals-p vals) (no-step-below a i z vals) (natp a) (<= a (len vals))
                (or (consp r) (< a (len vals)))
                (w3t::step (list :|%;%| z (append (operands a vals) (list i)))))
           (equal (flat-search (len vals) (revappend vals nil) i r z)
                  (list (list :|%;%|
                              (cadr (car (w3t::step (list :|%;%| z (append (operands a vals) (list i))))))
                              (append (revappend (nthcdr a vals) nil)
                                      (append (caddr (car (w3t::step
                                                           (list :|%;%| z (append (operands a vals)
                                                                                  (list i))))))
                                              r))))))
  :hints (("Goal" :in-theory (disable flat-search flat-search-when-step-fails
                                      flat-search-skips-too-few-operands flat-search-at-redex)
                  :do-not-induct t
                  :use ((:instance flat-search-skips-too-few-operands (j 0))
                        flat-search-at-redex))))

; ---------------------------------------------------------------------------
; The flat block

; with values before the operands or a rest after the instruction, STEP is
; Step/ctxt-instrs. STEP is opened on the whole block only: the step inside
; is not in this statement.
(defthm step-of-flat-block-is-flat-search
  (implies (and (vals-p vals) (op-instr-p i) (true-listp r)
                (natp (redex-arity i (list :|%;%| s f) vals))
                (or (consp r)
                    (not (equal (redex-arity i (list :|%;%| s f) vals) (len vals))))
                (flat-search (len vals) (revappend vals nil) i r (list :|%;%| s f)))
           (equal (w3t::step (list :|%;%| (list :|%;%| s f) (append (revappend vals nil) (cons i r))))
                  (flat-search (len vals) (revappend vals nil) i r (list :|%;%| s f))))
  :hints (("Goal" :in-theory (e/d (step-opener-with-step-own)
                                  (flat-search flat-search-when-step-fails
                                   flat-search-skips-too-few-operands flat-search-at-redex
                                   flat-search-finds-redex))
                  :cases ((consp r))
                  :use ((:instance step/r-pure-of-operands-when-not-arity
                                   (j (len vals)) (z (list :|%;%| s f)))
                        (:instance step/r-read-of-operands-when-not-arity
                                   (j (len vals)) (z (list :|%;%| s f))))
                  :do-not-induct t)))

(defthm step-result-rebuild
  (implies (w3t::step c)
           (equal (list (list :|%;%| (cadr (car (w3t::step c))) (caddr (car (w3t::step c)))))
                  (w3t::step c)))
  :hints (("Goal" :use step-result-shape
                  :in-theory (e/d (step-result-p) (step-result-shape step-result-components)))))

; V2 item 2. VALS is the operand stack, top first; I takes A of them; R is
; the rest of the block. If STEP of the redex is (z'; is') then STEP of the
; block is (z'; v ++ is' ++ r), V the values under the operands.
(defthm step-of-flat-block
  (implies (and (vals-p vals) (op-instr-p i) (true-listp r)
                (natp (redex-arity i (list :|%;%| s f) vals))
                (<= (redex-arity i (list :|%;%| s f) vals) (len vals))
                (equal a (redex-arity i (list :|%;%| s f) vals))
                (equal inner (w3t::step (list :|%;%| (list :|%;%| s f)
                                              (append (operands a vals) (list i)))))
                inner)
           (equal (w3t::step (list :|%;%| (list :|%;%| s f) (append (revappend vals nil) (cons i r))))
                  (list (list :|%;%| (cadr (car inner))
                              (append (revappend (nthcdr a vals) nil)
                                      (append (caddr (car inner)) r))))))
  :hints (("Goal" :in-theory (disable flat-search flat-search-when-step-fails step-of-redex
                                      flat-search-skips-too-few-operands flat-search-at-redex
                                      no-step-below-arity)
                  :cases ((and (equal (redex-arity i (list :|%;%| s f) vals) (len vals)) (atom r)))
                  :use ((:instance no-step-below-arity (n (redex-arity i (list :|%;%| s f) vals))))
                  :do-not-induct t)))

; ---------------------------------------------------------------------------
; V2 item 3: the middle is one administrative term (no operand). The search
; finds it first, so nothing is asked about fewer operands.

(defconst *admin-heads* '(:label_%{%}% :handler_%{%}% :frame_%{%}%))

(defthm step_pure-of-admin-term-when-not-alone
  (implies (and (redex-shape-p kw l) (member-equal kw *admin-heads*)
                (not (equal (len l) 1)))
           (equal (w3t::step_pure l) nil))
  :hints (("Goal" :do-not-induct t)))

(defthm step_read/split-of-admin-term-when-not-alone
  (implies (and (redex-shape-p kw l) (member-equal kw *admin-heads*)
                (not (equal (len l) 1)))
           (equal (w3t::step_read/split (list :|%;%| z l)) nil))
  :hints (("Goal" :do-not-induct t)))

(defthm value-head-p-when-admin-head
  (implies (member-equal kw *admin-heads*) (not (value-head-p kw)))
  :hints (("Goal" :in-theory (enable value-head-p))))

(defthm step/r-pure-of-vals-admin-term
  (implies (and (vals-p v) (consp v) (member-equal (car i) *admin-heads*))
           (equal (w3t::step/r-pure (list :|%;%| z (append v (list i)))) nil))
  :hints (("Goal" :in-theory (e/d (w3t::step/r-pure) (member-equal))
                  :use ((:instance step_pure-of-admin-term-when-not-alone
                                   (kw (car i)) (l (append v (list i))))))))

(defthm step/r-read-of-vals-admin-term
  (implies (and (vals-p v) (consp v) (member-equal (car i) *admin-heads*))
           (equal (w3t::step/r-read (list :|%;%| z (append v (list i)))) nil))
  :hints (("Goal" :in-theory (e/d (w3t::step/r-read) (member-equal))
                  :use ((:instance step_read/split-of-admin-term-when-not-alone
                                   (kw (car i)) (l (append v (list i))))))))

(defthm step-of-admin-term-in-flat-block-is-flat-search
  (implies (and (vals-p v) (true-listp r) (member-equal (car i) *admin-heads*)
                (or (consp v) (consp r))
                (flat-search (len v) v i r z))
           (equal (w3t::step (list :|%;%| z (append v (cons i r))))
                  (flat-search (len v) v i r z)))
  :hints (("Goal" :in-theory (e/d (step-opener-with-step-own)
                                  (flat-search flat-search-when-step-fails))
                  :cases ((consp r))
                  :do-not-induct t)))

(defthm step-of-admin-term-in-flat-block
  (implies (and (vals-p v) (true-listp r) (member-equal (car i) *admin-heads*)
                (or (consp v) (consp r))
                (equal inner (w3t::step (list :|%;%| z (list i))))
                inner)
           (equal (w3t::step (list :|%;%| z (append v (cons i r))))
                  (list (list :|%;%| (cadr (car inner))
                              (append v (append (caddr (car inner)) r))))))
  :hints (("Goal" :in-theory (disable flat-search flat-search-when-step-fails member-equal)
                  :expand ((flat-search (len v) v i r z)
                           (flat-search 0 v i r z))
                  :do-not-induct t)))

; ---------------------------------------------------------------------------
; The machine's rules on the redex are STEP on the redex

(defthm try-rules-on-redex
  (implies (and (vals-p vals) (op-instr-p i) (natp j) (<= j (len vals))
                (equal l (append (operands j vals) (list i))))
           (equal (try-rules (rules-for (list :op (car i))) z l)
                  (if (w3t::step_pure l)
                      (mv t z (car (w3t::step_pure l)))
                    (if (w3t::step_read/split (list :|%;%| z l))
                        (mv t z (car (w3t::step_read/split (list :|%;%| z l))))
                      (if (step-own (list :|%;%| z l))
                          (mv t (cadr (car (step-own (list :|%;%| z l))))
                              (caddr (car (step-own (list :|%;%| z l)))))
                        (mv nil z nil))))))
  :hints (("Goal" :in-theory (e/d (try-rules-of-rules-for car-t-of-drop-n nth-of-constant)
                                  (try-rules-of-pure-rules try-rules-of-read-rules
                                   try-rules-of-own-rules try-rules))
                  :use ((:instance try-rules-of-pure-rules (kw (car i)) (place (list :op (car i))))
                        (:instance try-rules-of-read-rules (kw (car i)) (place (list :op (car i))))
                        (:instance try-rules-of-own-rules (kw (car i)) (place (list :op (car i)))))
                  :do-not-induct t)))

(defthm step_pure-of-redex-instrs-true-listp
  (implies (and (vals-p vals) (op-instr-p i) (natp j) (<= j (len vals)))
           (true-listp (car (w3t::step_pure (append (operands j vals) (list i))))))
  :hints (("Goal" :in-theory (disable step_pure-instrs-true-listp)
                  :use ((:instance step_pure-instrs-true-listp (kw (car i))
                                   (l (append (operands j vals) (list i))))))))

(defthm step_read/split-of-redex-instrs-true-listp
  (implies (and (vals-p vals) (op-instr-p i) (natp j) (<= j (len vals)))
           (true-listp (car (w3t::step_read/split
                             (list :|%;%| z (append (operands j vals) (list i)))))))
  :hints (("Goal" :in-theory (disable step_read/split-instrs-true-listp)
                  :use ((:instance step_read/split-instrs-true-listp (kw (car i))
                                   (l (append (operands j vals) (list i))))))))

(defthm step-of-redex-by-relation
  (implies (and (vals-p vals) (op-instr-p i) (natp j) (<= j (len vals))
                (equal j (redex-arity i (list :|%;%| s f) vals)))
           (equal (w3t::step (list :|%;%| (list :|%;%| s f) (append (operands j vals) (list i))))
                  (if (w3t::step_pure (append (operands j vals) (list i)))
                      (list (list :|%;%| (list :|%;%| s f)
                                  (car (w3t::step_pure (append (operands j vals) (list i))))))
                    (if (w3t::step_read/split
                         (list :|%;%| (list :|%;%| s f) (append (operands j vals) (list i))))
                        (list (list :|%;%| (list :|%;%| s f)
                                    (car (w3t::step_read/split
                                          (list :|%;%| (list :|%;%| s f)
                                                (append (operands j vals) (list i)))))))
                      (step-own (list :|%;%| (list :|%;%| s f)
                                      (append (operands j vals) (list i))))))))
  :hints (("Goal" :in-theory (enable w3t::step/r-pure w3t::step/r-read) :do-not-induct t)))

(defthm step-own-result-rebuild
  (implies (step-own c)
           (and (equal (list (list :|%;%| (cadr (car (step-own c))) (caddr (car (step-own c)))))
                       (step-own c))
                (true-listp (caddr (car (step-own c))))))
  :hints (("Goal" :use step-own-result-shape
                  :in-theory (e/d (step-result-p) (step-own-result-shape)))))

(defthm step-own-state-rebuild
  (implies (step-own (list :|%;%| (list :|%;%| s f) l))
           (equal (list :|%;%|
                        (cadr (cadr (car (step-own (list :|%;%| (list :|%;%| s f) l)))))
                        (caddr (cadr (car (step-own (list :|%;%| (list :|%;%| s f) l))))))
                  (cadr (car (step-own (list :|%;%| (list :|%;%| s f) l))))))
  :hints (("Goal" :use ((:instance step-own-state-shape (z (list :|%;%| s f))))
                  :in-theory (disable step-own-state-shape))))

; What OP-STEP makes of a rule that fired, (mv t z2 res), is STEP's result:
; the machine keeps (cadr z2) and (caddr z2) as its store and frame.
(defthm try-rules-on-redex-is-step
  (implies (and (vals-p vals) (op-instr-p i) (natp j) (<= j (len vals))
                (equal j (redex-arity i (list :|%;%| s f) vals))
                (equal tr (try-rules (rules-for (list :op (car i))) (list :|%;%| s f)
                                     (append (operands j vals) (list i))))
                (mv-nth 0 tr))
           (and (equal (w3t::step (list :|%;%| (list :|%;%| s f) (append (operands j vals) (list i))))
                       (list (list :|%;%|
                                   (list :|%;%| (cadr (mv-nth 1 tr)) (caddr (mv-nth 1 tr)))
                                   (mv-nth 2 tr))))
                (true-listp (mv-nth 2 tr))))
  :hints (("Goal" :in-theory (disable step-of-redex try-rules) :do-not-induct t)))

(in-theory (disable flat-search flat-search-when-step-fails step-of-redex step-of-redex-by-relation
                    try-rules-on-redex no-step-below-arity))
