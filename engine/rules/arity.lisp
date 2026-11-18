; License: MIT. See the file LICENSE at the top of the repository.
;
; The number of operands (plan/wasm-engine/plan2.md V1, item 3): if a rule
; function R fires on the instruction list L, then the machine's
; REDEX-ARITY of the last element of L is the number of elements before it.
;     <R>-ARITY   (R l) => (redex-arity (nth (+ -1 (len l)) l) z vals)
;                          = (+ -1 (len l))
;   - Generated for the rules of a fixed shape, from <R>-SHAPE: the opcode's
;     arity in REDEX-ARITY is the rule's length less one.
;   - By hand for the rules whose count comes from a type: block, loop,
;     try_table (the block type), throw (the tag's type) and call_ref (the
;     type of the function the reference names). REDEX-ARITY computes the
;     count with the function of the specification that the rule calls.
;     For call_ref REDEX-ARITY reads the reference from the operand stack
;     VALS; the lemma asks that its top is the element before the last.
;   - A census: every rule of an opcode that REDEX-ARITY supports has its
;     lemma.
(in-package "WE")
(include-book "shape")

(set-prover-step-limit 2000000)

(in-theory (disable mv-nth value-head-p))

; ---------------------------------------------------------------------------
; The opcodes with a fixed arity

(defconst *typed-arity-heads* '(:block :loop :try_table :throw :call_ref))

(defun fixed-arity (kw)
  (declare (xargs :guard t))
  (if (sym-member kw *typed-arity-heads*)
      nil
    (redex-arity (list kw) nil nil)))

(defthm redex-arity-when-fixed-arity
  (implies (and (consp i) (fixed-arity (car i)))
           (equal (redex-arity i z vals) (fixed-arity (car i)))))

(defthm fixed-arity-is-of-a-head
  (implies (fixed-arity kw) kw)
  :rule-classes :forward-chaining)

(defthm redex-arity-of-last-when-redex-shape-p
  (implies (and (redex-shape-p kw l) (fixed-arity kw) (natp n) (equal (len l) (+ 1 n)))
           (equal (redex-arity (nth n l) z vals) (fixed-arity kw)))
  :hints (("Goal" :in-theory (disable fixed-arity redex-arity head-of-last-when-redex-shape-p
                                      consp-of-last-when-redex-shape-p)
                  :use (head-of-last-when-redex-shape-p consp-of-last-when-redex-shape-p))))

(in-theory (disable fixed-arity redex-arity-when-fixed-arity))

; ---------------------------------------------------------------------------
; Generated: the rules of a fixed shape

(deflabel arity-anchor)

(defun arity-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (progn (with-prover-step-limit 100000
                   (defthm ,(lemma-name fn "-ARITY")
                     (implies ,(rule-call fn)
                              (equal (redex-arity (nth (+ -1 (len l)) l) z vals)
                                     (+ -1 (len l))))
                     :hints (("Goal" :in-theory
                                     (union-theories
                                      (theory 'minimal-theory)
                                      (union-theories
                                       (executable-counterpart-theory 'arity-anchor)
                                       '(,(lemma-name fn "-SHAPE")
                                         redex-arity-of-last-when-redex-shape-p)))
                                     :do-not-induct t))))
                 (value-triple (cw "ARITY ~x0~%" ',fn)))
          (value-triple (cw "ARITY-NONE ~x0~%" ',fn)))))

(defun arity-lemmas (fns)
  (declare (xargs :mode :program))
  (cond ((endp fns) nil)
        ((and (shape-kw (car fns)) (fixed-arity (shape-kw (car fns)))
              (not (member-eq (car fns) *variable-shape-rules*)))
         (cons (arity-lemma (car fns)) (arity-lemmas (cdr fns))))
        (t (arity-lemmas (cdr fns)))))

(set-prover-step-limit 100000000)
(make-event `(progn ,@(arity-lemmas *step-rules*)))
(set-prover-step-limit 2000000)

; ---------------------------------------------------------------------------
; By hand: the count comes from a type. REDEX-ARITY is opened on the last
; element; the machine's accessors become those of the rule.

(defthm car-t-of-drop-n
  (equal (car-t (drop-n n x)) (nth n x))
  :hints (("Goal" :in-theory (enable nth))))

(defthm nth-of-constant
  (implies (syntaxp (quotep n))
           (equal (nth n x) (if (zp n) (car x) (nth (1- n) (cdr x)))))
  :hints (("Goal" :in-theory (enable nth))))

; the call_ref rules name the last element (cadr (nthcdr (- (len l) 2) l))
(defthm cadr-of-nthcdr
  (implies (natp n)
           (equal (cadr (nthcdr n l)) (nth (+ 1 n) l)))
  :hints (("Goal" :induct (cdr-n-induct n l) :in-theory (enable nthcdr nth))))

(defthm entry-kind-becomes-car
  (equal (entry-kind e) (car e)))

(defthm entry-n-becomes-cadr
  (equal (entry-n e) (cadr e)))

(deftheory typed-arity-theory
  '(redex-arity functype-params func-params car-t-of-drop-n nth-of-constant
    entry-kind-becomes-car entry-n-becomes-cadr cadr-of-nthcdr
    car-t-becomes-car cdr-t-becomes-cdr len-t-becomes-len nth-t-becomes-nth))

(in-theory (disable car-t-of-drop-n nth-of-constant entry-kind-becomes-car entry-n-becomes-cadr
                    cadr-of-nthcdr))

(defthm step_read/split/r-block-arity
  (implies (w3t::step_read/split/r-block (list :|%;%| z l))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) (+ -1 (len l))))
  :hints (("Goal" :in-theory (enable typed-arity-theory w3t::step_read/split/r-block)
                  :do-not-induct t)))

(defthm step_read/split/r-loop-arity
  (implies (w3t::step_read/split/r-loop (list :|%;%| z l))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) (+ -1 (len l))))
  :hints (("Goal" :in-theory (enable typed-arity-theory w3t::step_read/split/r-loop)
                  :do-not-induct t)))

(defthm step_read/split/r-try_table-arity
  (implies (w3t::step_read/split/r-try_table (list :|%;%| z l))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) (+ -1 (len l))))
  :hints (("Goal" :in-theory (enable typed-arity-theory w3t::step_read/split/r-try_table)
                  :do-not-induct t)))

(defthm step/r-throw-arity
  (implies (w3t::step/r-throw (list :|%;%| z l))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) (+ -1 (len l))))
  :hints (("Goal" :in-theory (enable typed-arity-theory w3t::step/r-throw)
                  :do-not-induct t)))

; call_ref. The reference is the top of the machine's operand stack. The
; rules match (:ref.func_addr a) by its shape only, and REDEX-ARITY asks
; that A is a natural number: the lemmas for a function reference ask it too
; (a reference that is a value has it).
(defthm step/r-call_ref-null-arity
  (implies (and (w3t::step/r-call_ref-null (list :|%;%| z l))
                (equal (car vals) (nth (+ -2 (len l)) l)))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) (+ -1 (len l))))
  :hints (("Goal" :in-theory (enable typed-arity-theory w3t::step/r-call_ref-null)
                  :do-not-induct t)))

; this rule reads the store with ($s z); the state has the machine's shape
(defthm step/r-call_ref-func-arity
  (implies (and (w3t::step/r-call_ref-func (list :|%;%| (list :|%;%| s f) l))
                (equal (car vals) (nth (+ -2 (len l)) l))
                (natp (cadr (nth (+ -2 (len l)) l))))
           (equal (redex-arity (nth (+ -1 (len l)) l) (list :|%;%| s f) vals) (+ -1 (len l))))
  :hints (("Goal" :in-theory (enable typed-arity-theory w3t::step/r-call_ref-func
                                     w3t::$s w3t::$store)
                  :do-not-induct t)))

(defthm step/r-call_ref-hostfunc-res-arity
  (implies (and (w3t::step/r-call_ref-hostfunc-res (list :|%;%| z l))
                (equal (car vals) (nth (+ -2 (len l)) l))
                (natp (cadr (nth (+ -2 (len l)) l))))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) (+ -1 (len l))))
  :hints (("Goal" :in-theory (enable typed-arity-theory w3t::step/r-call_ref-hostfunc-res)
                  :do-not-induct t)))

(defthm step/r-call_ref-hostfunc-div-arity
  (implies (and (w3t::step/r-call_ref-hostfunc-div (list :|%;%| z l))
                (equal (car vals) (nth (+ -2 (len l)) l))
                (natp (cadr (nth (+ -2 (len l)) l))))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) (+ -1 (len l))))
  :hints (("Goal" :in-theory (enable typed-arity-theory w3t::step/r-call_ref-hostfunc-div)
                  :do-not-induct t)))

; ---------------------------------------------------------------------------
; Census: a rule has no arity lemma exactly when REDEX-ARITY does not support
; its opcode (the machine stops :unsupported there), or its redex is an
; administrative term or a whole block.

(defun arity-expected-missing (fns)
  (declare (xargs :mode :program))
  (cond ((endp fns) nil)
        ((and (eq (car (rule-place (car fns))) :op)
              (or (fixed-arity (shape-kw (car fns)))
                  (member-eq (shape-kw (car fns)) *typed-arity-heads*)))
         (arity-expected-missing (cdr fns)))
        (t (cons (car fns) (arity-expected-missing (cdr fns))))))

(defun count-ops (fns)                  ; the rules whose place is an opcode
  (declare (xargs :mode :program))
  (cond ((endp fns) 0)
        ((eq (car (rule-place (car fns))) :op) (1+ (count-ops (cdr fns))))
        (t (count-ops (cdr fns)))))

(make-event
 (let* ((missing (lemmas-missing *step-rules* "" "-ARITY" (w state)))
        (expected (arity-expected-missing *step-rules*)))
   (if (equal missing expected)
       (value `(value-triple
                (cw "ARITY-CENSUS ~x0 rules: ~x1 arity lemmas; none for ~x2 rules of unsupported opcodes and ~x3 rules on an administrative term or a block~%"
                    ,(len *step-rules*) ,(- (len *step-rules*) (len missing))
                    ,(count-ops missing) ,(- (len missing) (count-ops missing)))))
     (er soft 'arity "No arity lemma: ~x0. Expected: ~x1."
         (set-difference-eq missing expected) (set-difference-eq expected missing)))))
