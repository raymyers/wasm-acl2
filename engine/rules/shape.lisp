; License: MIT. See the file LICENSE at the top of the repository.
;
; The shape of a redex (plan/wasm-engine/plan2.md V1, items 1 to 3 and 5).
; For every rule function R of W3T::STEP_PURE, W3T::STEP_READ/SPLIT and
; W3T::STEP: if R fires on the instruction list L, then L has R's shape.
;   - FIRST-NONVAL: the index of the first element that is not a value. It is
;     W3T::STEP/PREFIX7, which is rewritten to it.
;   - (REDEX-SHAPE-P KW L): L is not empty, every element but the last has
;     the head of a value, and the last has head KW.
;   - Generated, per rule function R with opcode (or administrative head) K:
;       <R>-FAILS-WHEN-NOT-SHAPE   (not (redex-shape-p K l)) => (R l) = nil
;       <R>-FAILS-WHEN-NOT-LENGTH  (not (equal (len l) n))   => (R l) = nil
;       <R>-SHAPE                  forward chaining: (R l) => both
;     The length lemma is for the rules of a fixed shape (N - 1 operands).
;   - By hand: the nine rules whose number of operands comes from a type
;     (their shape, and their length in terms of the type the rule reads),
;     and the two rules on a whole block, TRAP-INSTRS and THROW_REF-INSTRS.
;   - A census: every rule function of *STEP-RULES* has its lemmas.
; No rule function is opened on anything but a variable, each in its own
; lemma, in a theory with no other definition of the specification.
(in-package "WE")
(include-book "step-basics")
(local (include-book "arithmetic/top" :dir :system))

(set-prover-step-limit 2000000)

; VALUE-HEAD-P (rules/terminal.lisp) is used closed from here on; on a
; constant it is computed.
(in-theory (disable value-head-p))

; ---------------------------------------------------------------------------
; FIRST-NONVAL

(defun first-nonval (l)
  (if (atom l)
      0
    (if (w3t::val-p (car l))
        (+ 1 (first-nonval (cdr l)))
      0)))

(defthm step/prefix7-becomes-first-nonval
  (equal (w3t::step/prefix7 l) (first-nonval l))
  :hints (("Goal" :in-theory (enable w3t::step/prefix7))))

(defthm natp-of-first-nonval
  (natp (first-nonval l))
  :rule-classes :type-prescription)

(defthm first-nonval-bound
  (<= (first-nonval l) (len l))
  :rule-classes :linear)

(defthm first-nonval-of-vals
  (implies (vals-p l) (equal (first-nonval l) (len l))))

(defthm not-val-p-when-head-not-value
  (implies (not (value-head-p (car x))) (not (w3t::val-p x))))

(defthm value-head-p-of-car-when-val-p
  (implies (w3t::val-p x) (value-head-p (car x))))

(defthm first-nonval-of-append-of-vals-and-instr
  (implies (and (vals-p v) (not (w3t::val-p i)))
           (equal (first-nonval (append v (cons i r))) (len v))))

(defthm nth-of-first-nonval-of-append-of-vals-and-instr
  (implies (and (vals-p v) (not (w3t::val-p i)))
           (equal (nth (len v) (append v (cons i r))) i)))

(defthm first-nonval-when-vals-then-nonval
  (implies (and (vals-p (take k l)) (natp k) (< k (len l)) (not (w3t::val-p (nth k l))))
           (equal (first-nonval l) k))
  :hints (("Goal" :induct (cdr-n-induct k l) :in-theory (enable take nth))))

(in-theory (disable first-nonval))

; ---------------------------------------------------------------------------
; REDEX-SHAPE-P

(defun redex-shape-p (kw l)
  (and (consp l)
       (if (consp (cdr l))
           (and (value-head-p (car (car l))) (redex-shape-p kw (cdr l)))
         (equal (car (car l)) kw))))

(defthm redex-shape-p-when-consp-cdr
  (implies (consp (cdr l))
           (equal (redex-shape-p kw l)
                  (and (value-head-p (car (car l))) (redex-shape-p kw (cdr l))))))

(defthm redex-shape-p-when-not-consp-cdr
  (implies (not (consp (cdr l)))
           (equal (redex-shape-p kw l)
                  (and (consp l) (equal (car (car l)) kw)))))

(defthm consp-when-redex-shape-p
  (implies (redex-shape-p kw l) (consp l))
  :rule-classes :forward-chaining)

; a list has one shape
(defthm redex-shape-p-unique
  (implies (and (redex-shape-p kw1 l) (not (equal kw1 kw2)))
           (not (redex-shape-p kw2 l)))
  :hints (("Goal" :induct (len l)
                  :in-theory (disable redex-shape-p-when-consp-cdr redex-shape-p-when-not-consp-cdr))))

; the head of the last element
(defthm head-of-last-when-redex-shape-p
  (implies (redex-shape-p kw l)
           (equal (car (nth (+ -1 (len l)) l)) kw))
  :hints (("Goal" :in-theory (enable nth))))

(defthm val-p-when-ref-p
  (implies (w3t::ref-p x) (w3t::val-p x))
  :hints (("Goal" :in-theory (enable w3t::val-p w3t::ref-p))))

(defthm consp-of-last-when-redex-shape-p
  (implies (and (redex-shape-p kw l) kw)
           (consp (nth (+ -1 (len l)) l)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm value-head-p-of-car-when-ref-p
  (implies (w3t::ref-p x) (value-head-p (car x))))

; values before position N: the shape of L is the shape of its tail
(defthm redex-shape-p-of-vals-then-tail
  (implies (and (vals-p (take n l)) (natp n) (< n (len l)))
           (equal (redex-shape-p kw l) (redex-shape-p kw (nthcdr n l))))
  :hints (("Goal" :induct (cdr-n-induct n l) :in-theory (enable take nthcdr))))

(defthm redex-shape-p-of-nthcdr-1
  (implies (and (natp n) (equal (len l) (+ 1 n)))
           (equal (redex-shape-p kw (nthcdr n l)) (equal (car (nth n l)) kw)))
  :hints (("Goal" :induct (cdr-n-induct n l) :in-theory (enable nthcdr nth))))

(defthm redex-shape-p-of-nthcdr-2
  (implies (and (natp n) (equal (len l) (+ 2 n)))
           (equal (redex-shape-p kw (nthcdr n l))
                  (and (value-head-p (car (nth n l))) (equal (car (cadr (nthcdr n l))) kw))))
  :hints (("Goal" :induct (cdr-n-induct n l) :in-theory (enable nthcdr nth))))

(defthm redex-shape-p-of-append-of-vals-and-instr
  (implies (and (vals-p v) (not (value-head-p (car i))))
           (equal (redex-shape-p kw (append v (cons i r)))
                  (and (atom r) (equal (car i) kw))))
  :hints (("Goal" :induct (len v)
                  :in-theory (disable redex-shape-p-when-consp-cdr redex-shape-p-when-not-consp-cdr))))

; the element at FIRST-NONVAL has the head of a value, or is the last one, or
; there is none
(defthm head-of-first-nonval-when-redex-shape-p
  (implies (and (redex-shape-p kw l) (not (equal kw2 kw)) (not (value-head-p kw2)) kw2)
           (not (equal (car (nth (first-nonval l) l)) kw2)))
  :hints (("Goal" :induct (len l)
                  :in-theory (e/d (first-nonval nth)
                                  (redex-shape-p-when-consp-cdr redex-shape-p-when-not-consp-cdr)))))

(defthm head-of-first-nonval-when-redex-shape-p-2
  (implies (and (redex-shape-p kw l) (not (equal kw2 kw)) (not (value-head-p kw2)) kw2)
           (not (equal kw2 (car (nth (first-nonval l) l)))))
  :hints (("Goal" :induct (len l)
                  :in-theory (e/d (first-nonval nth)
                                  (redex-shape-p-when-consp-cdr redex-shape-p-when-not-consp-cdr)))))

; no element of a redex has a head that is neither a value's nor KW
(defun head-member (kw l)
  (and (consp l)
       (or (equal (car (car l)) kw) (head-member kw (cdr l)))))

(defthm head-member-when-redex-shape-p
  (implies (and (redex-shape-p kw l) (not (equal kw2 kw)) (not (value-head-p kw2)))
           (not (head-member kw2 l)))
  :hints (("Goal" :induct (len l)
                  :in-theory (disable redex-shape-p-when-consp-cdr redex-shape-p-when-not-consp-cdr))))

(defthm head-member-when-head-of-nth
  (implies (and (equal (car (nth n l)) kw) (natp n) (< n (len l)))
           (head-member kw l))
  :hints (("Goal" :induct (cdr-n-induct n l) :in-theory (enable nth))))

; the generated bodies keep (cadr (nthcdr n l)) as it is
(defthm head-member-when-head-of-cadr-of-nthcdr
  (implies (and (consp (cdr (nthcdr n l))) (equal (car (cadr (nthcdr n l))) kw))
           (head-member kw l))
  :hints (("Goal" :induct (cdr-n-induct n l) :in-theory (enable nthcdr))))

(in-theory (disable redex-shape-p head-member))

; ---------------------------------------------------------------------------
; One lemma per rule function, generated. The theory of each proof is
; MINIMAL-THEORY, the executable counterparts, the rules named here and the
; rule function itself (V0-ground §2: in the default theory the
; preprocessing of one such lemma ran 346 s).

(deflabel shape-anchor)

(deftheory shape-theory
  (union-theories (theory 'minimal-theory)
    (union-theories (executable-counterpart-theory 'shape-anchor)
      '(redex-shape-p-when-consp-cdr redex-shape-p-when-not-consp-cdr
        equal-of-len-and-constant value-head-p-of-car-when-val-p
        value-head-p-of-car-when-ref-p car-cons cdr-cons atom))))

; the head of the last element of R's redex, NIL for the rules on a block
(defun shape-kw (fn)
  (declare (xargs :mode :program))
  (let ((p (rule-place fn)))
    (cond ((equal p '(:entry :l)) :label_%{%}%)
          ((equal p '(:entry :h)) :handler_%{%}%)
          ((equal p '(:entry :f)) :frame_%{%}%)
          ((consp p) (cadr p))
          (t nil))))

; the rules whose number of operands comes from a type: by hand, below
(defconst *variable-shape-rules*
  '(w3t::step_read/split/r-block w3t::step_read/split/r-loop
    w3t::step_read/split/r-try_table w3t::step/r-throw w3t::step/r-struct.new
    w3t::step/r-array.new_fixed w3t::step/r-call_ref-func
    w3t::step/r-call_ref-hostfunc-res w3t::step/r-call_ref-hostfunc-div))

; the two rules on a whole block: by hand, below
(defconst *block-rules*
  '(w3t::step_pure/r-trap-instrs w3t::step_read/split/r-throw_ref-instrs))

(defun lemma-name (fn suffix)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) suffix) 'we::here))

(defun rule-call (fn)                   ; R on the instruction list L in state Z
  (declare (xargs :mode :program))
  (if (eq (rule-kind fn) :pure) `(,fn l) `(,fn (list :|%;%| z l))))

; The length a fixed-shape rule asks of its list: the first test
; (equal (len <variable>) 'n) of its body.
(mutual-recursion
 (defun len-tests (term)
   (declare (xargs :mode :program))
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((consp (car term))
          (append (len-tests-list (cdr term)) (len-tests (caddr (car term)))))
         ((and (eq (car term) 'equal) (consp (cadr term)) (eq (car (cadr term)) 'len)
               (symbolp (cadr (cadr term))) (quotep (caddr term)))
          (list (cadr (caddr term))))
         (t (len-tests-list (cdr term)))))
 (defun len-tests-list (terms)
   (declare (xargs :mode :program))
   (if (atom terms) nil (append (len-tests (car terms)) (len-tests-list (cdr terms))))))

(defun rule-length (fn wrld)
  (declare (xargs :mode :program))
  (car (len-tests (getpropc fn 'acl2::unnormalized-body nil wrld))))

(defun shape-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 100000
                   (defthm ,(lemma-name fn "-FAILS-WHEN-NOT-SHAPE")
                     (implies (not (redex-shape-p ,(shape-kw fn) l)) (equal ,(rule-call fn) nil))
                     :hints (("Goal" :in-theory (union-theories (theory 'shape-theory) '(,fn))
                                     :do-not-induct t))))
                 (value-triple (cw "SHAPE ~x0~%" ',fn)))
          (value-triple (cw "SHAPE-FAILED ~x0~%" ',fn)))))

(defun not-length-lemma (fn wrld)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 100000
                   (defthm ,(lemma-name fn "-FAILS-WHEN-NOT-LENGTH")
                     (implies (not (equal (len l) ,(rule-length fn wrld))) (equal ,(rule-call fn) nil))
                     :hints (("Goal" :in-theory (union-theories (theory 'shape-theory) '(,fn))
                                     :do-not-induct t))))
                 (value-triple (cw "LENGTH ~x0 ~x1~%" ',fn ,(rule-length fn wrld))))
          (value-triple (cw "LENGTH-FAILED ~x0~%" ',fn)))))

; forward chaining, from the two rewrite rules
(defun fc-lemma (fn wrld)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 100000
                   (defthm ,(lemma-name fn "-SHAPE")
                     (implies ,(rule-call fn)
                              (and (redex-shape-p ,(shape-kw fn) l)
                                   (equal (len l) ,(rule-length fn wrld))))
                     :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                                '(,(lemma-name fn "-FAILS-WHEN-NOT-SHAPE")
                                                                  ,(lemma-name fn "-FAILS-WHEN-NOT-LENGTH")))
                                     :do-not-induct t))
                     :rule-classes ((:forward-chaining :trigger-terms (,(rule-call fn))))))
                 (value-triple (cw "FC ~x0~%" ',fn)))
          (value-triple (cw "FC-FAILED ~x0~%" ',fn)))))

(defun fixed-shape-lemmas (fns wrld)
  (declare (xargs :mode :program))
  (cond ((endp fns) nil)
        ((or (member-eq (car fns) *variable-shape-rules*) (member-eq (car fns) *block-rules*))
         (fixed-shape-lemmas (cdr fns) wrld))
        (t (list* (shape-lemma (car fns)) (not-length-lemma (car fns) wrld) (fc-lemma (car fns) wrld)
                  (fixed-shape-lemmas (cdr fns) wrld)))))

; one top-level event: its step limit is the sum over the lemmas
(set-prover-step-limit 100000000)
(make-event `(progn ,@(fixed-shape-lemmas *step-rules* (w state))))
(set-prover-step-limit 2000000)

; ---------------------------------------------------------------------------
; The rules whose redex has a number of values that comes from a type:
;   block, loop, try_table, throw, struct.new, array.new_fixed: val^n instr
;   call_ref (three rules): val^n ref instr
; Each matches (take (- (len l) j) l) with a generated MATCHnn function that
; accepts lists of values only.

(defun match-fn-p (fn wrld)
  (declare (xargs :mode :program))
  (let ((s (symbol-name fn)))
    (and (equal (symbol-package-name fn) "W3T")
         (<= 4 (length s)) (equal (subseq s 0 4) "STEP")
         (search "/MATCH" s)
         (equal (len (acl2::formals fn wrld)) 1))))

(defun match-fns (runes wrld)
  (declare (xargs :mode :program))
  (cond ((endp runes) nil)
        ((and (consp (car runes)) (eq (car (car runes)) :definition)
              (match-fn-p (cadr (car runes)) wrld))
         (cons (cadr (car runes)) (match-fns (cdr runes) wrld)))
        (t (match-fns (cdr runes) wrld))))

(defun match-lemma-name (fn)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string "VALS-P-WHEN-" (symbol-name fn)) 'we::here))

; Forward chaining, not rewrite: as rewrite rules about VALS-P they make
; every later (vals-p ...) goal backchain into a recursive match function
; (V0-ground §2).
(defun match-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 100000
                   (defthm ,(match-lemma-name fn)
                     (implies (,fn s) (vals-p s))
                     :hints (("Goal" :induct (,fn s) :in-theory (enable ,fn vals-p)))
                     :rule-classes :forward-chaining))
                 (value-triple (cw "MATCH ~x0~%" ',fn)))
          (value-triple (cw "MATCH-FAILED ~x0~%" ',fn)))))

(defun match-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (match-lemma (car fns)) (match-lemmas (cdr fns)))))

(defun all-match-fns (wrld)             ; the theory is not used: every definition, enabled or not
  (declare (xargs :mode :program))
  (match-fns (acl2::function-theory-fn :here wrld) wrld))

; the match functions that accept something else than a value list (types,
; instructions, catch clauses): no rule of *VARIABLE-SHAPE-RULES* uses them
; on its operands
(defconst *match-fns-not-values*
  '(w3t::step/match248 w3t::step/match232 w3t::step/match58
    w3t::step_read/split/match573 w3t::step_read/split/match554
    w3t::step_read/match824 w3t::step_read/match805))

(set-prover-step-limit 100000000)
(make-event `(progn ,@(match-lemmas (all-match-fns (w state)))))
(set-prover-step-limit 2000000)

(defun lemmas-missing (fns prefix suffix wrld)
  (declare (xargs :mode :program))
  (cond ((endp fns) nil)
        ((getpropc (intern-in-package-of-symbol
                    (concatenate 'string prefix (symbol-name (car fns)) suffix) 'we::here)
                   'acl2::theorem nil wrld)
         (lemmas-missing (cdr fns) prefix suffix wrld))
        (t (cons (car fns) (lemmas-missing (cdr fns) prefix suffix wrld)))))

(make-event
 (let ((missing (lemmas-missing (all-match-fns (w state)) "VALS-P-WHEN-" "" (w state))))
   (if (and (subsetp-eq missing *match-fns-not-values*)
            (subsetp-eq *match-fns-not-values* missing))
       (value '(value-triple :match-lemmas-as-recorded))
     (er soft 'shape "The match functions with no lemma are ~x0; recorded: ~x1."
         missing *match-fns-not-values*))))

; R's redex is values, then one or two elements; the shape lemma of R. The
; value prefix is found by REDEX-SHAPE-P-OF-VALS-THEN-TAIL, whose free
; variable N is bound by the forward-chained (vals-p (take n l)).
(defun tail-shape-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 2000000
                   (defthm ,(lemma-name fn "-FAILS-WHEN-NOT-SHAPE")
                     (implies (not (redex-shape-p ,(shape-kw fn) l)) (equal ,(rule-call fn) nil))
                     :hints (("Goal" :in-theory (enable ,fn) :do-not-induct t))))
                 (value-triple (cw "SHAPE ~x0~%" ',fn)))
          (value-triple (cw "SHAPE-FAILED ~x0~%" ',fn)))))

(defun tail-shape-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (cons (tail-shape-lemma (car fns)) (tail-shape-lemmas (cdr fns)))))

(set-prover-step-limit 100000000)
(make-event `(progn ,@(tail-shape-lemmas *variable-shape-rules*)))
(set-prover-step-limit 2000000)

; ---------------------------------------------------------------------------
; The two rules on a whole block: val* TRAP instr* (TRAP-INSTRS) and
; val* ref THROW_REF instr* (THROW_REF-INSTRS). Their searches accept a
; value prefix only. Two facts each: the element at FIRST-NONVAL is the TRAP
; (the exception reference, or the THROW_REF when the reference is a
; value), and some element has the head TRAP (THROW_REF).

(defthm step_pure/search171-fails-when-first-instr-not-trap
  (implies (not (equal (car (nth (first-nonval l) l)) :trap))
           (equal (w3t::step_pure/search171 k lo hi l) nil))
  :hints (("Goal" :induct (w3t::step_pure/search171 k lo hi l)
                  :in-theory (enable w3t::step_pure/search171))))

(defthm step_pure/search171-fails-when-no-trap
  (implies (not (head-member :trap l))
           (equal (w3t::step_pure/search171 k lo hi l) nil))
  :hints (("Goal" :induct (w3t::step_pure/search171 k lo hi l)
                  :in-theory (enable w3t::step_pure/search171))))

(defthm step_pure/r-trap-instrs-fails-when-first-instr-not-trap
  (implies (not (equal (car (nth (first-nonval l) l)) :trap))
           (equal (w3t::step_pure/r-trap-instrs l) nil))
  :hints (("Goal" :in-theory (enable w3t::step_pure/r-trap-instrs))))

(defthm step_pure/r-trap-instrs-fails-when-no-trap
  (implies (not (head-member :trap l))
           (equal (w3t::step_pure/r-trap-instrs l) nil))
  :hints (("Goal" :in-theory (enable w3t::step_pure/r-trap-instrs))))

(defthm head-of-first-nonval-when-vals-then-throw_ref
  (implies (and (vals-p (take k l)) (natp k) (consp (cdr (nthcdr k l)))
                (equal (car (cadr (nthcdr k l))) :throw_ref))
           (equal (car (nth (first-nonval l) l))
                  (if (w3t::val-p (nth k l)) :throw_ref (car (nth k l)))))
  :hints (("Goal" :induct (cdr-n-induct k l)
                  :in-theory (enable first-nonval take nth nthcdr))))

(defthm step_read/split/search134-fails-when-first-instr-not-throw_ref
  (implies (not (member-equal (car (nth (first-nonval l) l)) '(:ref.exn_addr :throw_ref)))
           (equal (w3t::step_read/split/search134 k lo hi l) nil))
  :hints (("Goal" :induct (w3t::step_read/split/search134 k lo hi l)
                  :in-theory (enable w3t::step_read/split/search134))))

(defthm step_read/split/search134-fails-when-no-throw_ref
  (implies (not (head-member :throw_ref l))
           (equal (w3t::step_read/split/search134 k lo hi l) nil))
  :hints (("Goal" :induct (w3t::step_read/split/search134 k lo hi l)
                  :in-theory (enable w3t::step_read/split/search134))))

(defthm step_read/split/r-throw_ref-instrs-fails-when-first-instr-not-throw_ref
  (implies (not (member-equal (car (nth (first-nonval l) l)) '(:ref.exn_addr :throw_ref)))
           (equal (w3t::step_read/split/r-throw_ref-instrs (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (enable w3t::step_read/split/r-throw_ref-instrs))))

(defthm step_read/split/r-throw_ref-instrs-fails-when-no-throw_ref
  (implies (not (head-member :throw_ref l))
           (equal (w3t::step_read/split/r-throw_ref-instrs (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (enable w3t::step_read/split/r-throw_ref-instrs))))

; ---------------------------------------------------------------------------
; Census. Every rule function of *STEP-RULES* but the two on a whole block
; has its shape lemma; every one of a fixed shape has its length lemma and
; its forward-chaining lemma.

(make-event
 (let* ((wrld (w state))
        (no-shape (lemmas-missing *step-rules* "" "-FAILS-WHEN-NOT-SHAPE" wrld))
        (no-length (lemmas-missing *step-rules* "" "-FAILS-WHEN-NOT-LENGTH" wrld))
        (no-fc (lemmas-missing *step-rules* "" "-SHAPE" wrld))
        (variable (append *variable-shape-rules* *block-rules*)))
   (if (and (equal no-shape *block-rules*)
            (subsetp-eq no-length variable) (subsetp-eq variable no-length)
            (equal no-fc no-length))
       (value `(value-triple (cw "SHAPE-CENSUS ~x0 rules: ~x1 shape lemmas, ~x2 length lemmas~%"
                                 ,(len *step-rules*)
                                 ,(- (len *step-rules*) (len no-shape))
                                 ,(- (len *step-rules*) (len no-length)))))
     (er soft 'shape "No shape lemma: ~x0. No length lemma: ~x1. No forward-chaining lemma: ~x2."
         no-shape no-length no-fc))))
