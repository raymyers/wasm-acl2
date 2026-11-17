; V0 spike (plan/wasm-engine/plan2.md, V0 last item): the V1 exit statement
; for `nop` alone, by hand. A session script, not a certified book.
;   cd plan/wasm-engine/notes/data/v0-ground && acl2 < spike-nop.lsp     (inside nix develop)
; Result and prover steps: notes/V0-ground.md.
(ld "../../../../../engine/rules/cert.acl2")
(include-book "../../../../../engine/rules/terminal")
(include-book "../../../../../engine/machine/machine")
(include-book "std/lists/top" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)
(in-package "WE")
(set-inhibit-output-lst '(proof-tree prove event common-lisp::warning warning! observation))
(set-prover-step-limit 2000000)

; --- the shape of a redex: values, then one instruction with head KW --------
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
(defthm equal-of-len-and-constant
  (implies (syntaxp (quotep k))
           (equal (equal (len l) k)
                  (if (posp k)
                      (and (consp l) (equal (len (cdr l)) (1- k)))
                    (and (equal k 0) (atom l))))))
(defthm value-head-p-of-car-when-val-p
  (implies (w3t::val-p x) (value-head-p (car x)))
  :hints (("Goal" :in-theory (enable w3t::val-p))))
(defthm val-p-when-ref-p
  (implies (w3t::ref-p x) (w3t::val-p x))
  :hints (("Goal" :in-theory (enable w3t::val-p))))
(defthm value-head-p-of-car-when-ref-p
  (implies (w3t::ref-p x) (value-head-p (car x))))
(in-theory (disable value-head-p))

; values before the last J elements: the shape is decided by those J
(defun cdr-n-induct (n l) (if (zp n) l (cdr-n-induct (1- n) (cdr l))))
(defthm redex-shape-p-of-vals-then-tail
  (implies (and (vals-p (take n l)) (natp n) (< n (len l)))
           (equal (redex-shape-p kw l) (redex-shape-p kw (nthcdr n l))))
  :hints (("Goal" :induct (cdr-n-induct n l) :in-theory (enable redex-shape-p take nthcdr))))
(in-theory (disable redex-shape-p))

; --- one lemma per rule function, generated ---------------------------------
(deflabel shape-anchor)
(deftheory shape-theory
  (union-theories (theory 'minimal-theory)
    (union-theories (executable-counterpart-theory 'shape-anchor)
      '(redex-shape-p-when-consp-cdr redex-shape-p-when-not-consp-cdr
        equal-of-len-and-constant value-head-p-of-car-when-val-p
        value-head-p-of-car-when-ref-p car-cons cdr-cons atom))))

(defun shape-kw (fn)
  (declare (xargs :mode :program))
  (let ((p (rule-place fn)))
    (cond ((equal p '(:entry :l)) :label_%{%}%)
          ((equal p '(:entry :h)) :handler_%{%}%)
          ((equal p '(:entry :f)) :frame_%{%}%)
          ((consp p) (cadr p))
          (t nil))))
(defun shape-name (fn)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-FAILS-WHEN-NOT-SHAPE") 'we::here))
(defun shape-lemma (fn)
  (declare (xargs :mode :program))
  (let* ((call (if (eq (rule-kind fn) :pure) `(,fn l) `(,fn (list :|%;%| z l)))))
    `(make-event
      '(:or (progn (with-prover-step-limit 100000
                     (defthm ,(shape-name fn)
                       (implies (not (redex-shape-p ,(shape-kw fn) l)) (equal ,call nil))
                       :hints (("Goal" :in-theory (union-theories (theory 'shape-theory) '(,fn)) :do-not-induct t))))
                   (value-triple (cw "SHAPE ~x0~%" ',fn)))
            (value-triple (cw "SHAPE-FAILED ~x0~%" ',fn))))))
(defun shape-lemmas (fns)
  (declare (xargs :mode :program))
  (cond ((endp fns) nil)
        ((shape-kw (car fns)) (cons (shape-lemma (car fns)) (shape-lemmas (cdr fns))))
        (t (shape-lemmas (cdr fns)))))
(set-inhibit-output-lst '(proof-tree prove event common-lisp::warning warning! observation summary common-lisp::error))
(make-event `(progn ,@(shape-lemmas *step-rules*)))
(set-inhibit-output-lst '(proof-tree prove event common-lisp::warning warning! observation))

; --- the rules whose redex has a variable number of values -------------------
; block, loop, try_table, throw, struct.new, array.new_fixed: val^n instr;
; call_ref (three rules): val^n ref instr. Each matches (take (- (len l) j) l)
; with a generated MATCHnn function that accepts lists of values.
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
; forward-chaining, not rewrite: as rewrite rules about VALS-P they make the
; later proofs of this family exceed their step limit
(defun match-lemma (fn)
  (declare (xargs :mode :program))
  (let ((name (intern-in-package-of-symbol (concatenate 'string "VALS-P-WHEN-" (symbol-name fn)) 'we::here)))
    `(make-event
      '(:or (progn (with-prover-step-limit 100000
                     (defthm ,name (implies (,fn s) (vals-p s))
                       :hints (("Goal" :induct (,fn s) :in-theory (enable ,fn vals-p)))
                       :rule-classes :forward-chaining))
                   (value-triple (cw "MATCH ~x0~%" ',fn)))
            (value-triple (cw "MATCH-FAILED ~x0~%" ',fn))))))
(defun match-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (match-lemma (car fns)) (match-lemmas (cdr fns)))))
; one top-level event: its step limit is the sum over the lemmas
(set-prover-step-limit 50000000)
(set-inhibit-output-lst '(proof-tree prove event common-lisp::warning warning! observation summary common-lisp::error))
(make-event `(progn ,@(match-lemmas (match-fns (acl2::function-theory-fn :here (w state)) (w state)))))
(set-inhibit-output-lst '(proof-tree prove event common-lisp::warning warning! observation))

; from here on no definition of the specification is enabled unless named
(defun spec-def-runes (runes)
  (declare (xargs :mode :program))
  (cond ((endp runes) nil)
        ((and (consp (car runes)) (eq (car (car runes)) :definition)
              (member-equal (symbol-package-name (cadr (car runes))) '("W3T" "WRT")))
         (cons (car runes) (spec-def-runes (cdr runes))))
        (t (spec-def-runes (cdr runes)))))
(deftheory spec-defs-theory (spec-def-runes (current-theory :here)))
(in-theory (disable spec-defs-theory))

(defthm redex-shape-p-of-nthcdr-1
  (implies (and (natp n) (equal (len l) (+ 1 n)))
           (equal (redex-shape-p kw (nthcdr n l)) (equal (car (nth n l)) kw)))
  :hints (("Goal" :induct (cdr-n-induct n l) :in-theory (enable redex-shape-p nthcdr nth))))
(defthm redex-shape-p-of-nthcdr-2
  (implies (and (natp n) (equal (len l) (+ 2 n)))
           (equal (redex-shape-p kw (nthcdr n l))
                  (and (value-head-p (car (nth n l))) (equal (car (cadr (nthcdr n l))) kw))))
  :hints (("Goal" :induct (cdr-n-induct n l) :in-theory (enable redex-shape-p nthcdr nth))))

(defmacro tail-shape-lemma (fn kw j)
  `(make-event
    '(:or (progn (with-prover-step-limit 2000000
                   (defthm ,(shape-name fn)
                     (implies (not (redex-shape-p ,kw l)) (equal (,fn (list :|%;%| z l)) nil))
                     :hints (("Goal" :in-theory (e/d (,fn) (redex-shape-p-of-vals-then-tail))
                              :use ((:instance redex-shape-p-of-vals-then-tail (kw ,kw) (n (+ ,(- j) (len l)))))))))
                 (value-triple (cw "SHAPE ~x0~%" ',fn)))
          (value-triple (cw "SHAPE-FAILED ~x0~%" ',fn)))))
(tail-shape-lemma w3t::step_read/split/r-block :block 1)
(tail-shape-lemma w3t::step_read/split/r-loop :loop 1)
(tail-shape-lemma w3t::step_read/split/r-try_table :try_table 1)
(tail-shape-lemma w3t::step/r-throw :throw 1)
(tail-shape-lemma w3t::step/r-struct.new :struct.new 1)
(tail-shape-lemma w3t::step/r-array.new_fixed :array.new_fixed 1)
(tail-shape-lemma w3t::step/r-call_ref-func :call_ref 2)
(tail-shape-lemma w3t::step/r-call_ref-hostfunc-res :call_ref 2)
(tail-shape-lemma w3t::step/r-call_ref-hostfunc-div :call_ref 2)

; --- the two rules on a whole block: val* TRAP instr*, val* ref THROW_REF instr*
; Their searches accept only a value prefix, so the first element that is
; not a value is the TRAP (the exception reference or the THROW_REF).
(defthm prefix7-when-vals-then-nonval
  (implies (and (vals-p (take k l)) (natp k) (< k (len l)) (not (w3t::val-p (nth k l))))
           (equal (w3t::step/prefix7 l) k))
  :hints (("Goal" :induct (cdr-n-induct k l) :in-theory (enable w3t::step/prefix7 take nth vals-p))))
(defthm not-val-p-when-head-not-value
  (implies (not (value-head-p (car x))) (not (w3t::val-p x))))
(defthm step_pure/search171-gives-trap
  (implies (w3t::step_pure/search171 k lo hi l)
           (equal (car (nth (w3t::step/prefix7 l) l)) :trap))
  :hints (("Goal" :induct (w3t::step_pure/search171 k lo hi l)
           :in-theory (enable w3t::step_pure/search171 (:e value-head-p)))))
(defthm head-of-first-non-value-when-vals-then-throw_ref
  (implies (and (vals-p (take k l)) (natp k) (consp (cdr (nthcdr k l)))
                (equal (car (cadr (nthcdr k l))) :throw_ref))
           (equal (car (nth (w3t::step/prefix7 l) l))
                  (if (w3t::val-p (nth k l)) :throw_ref (car (nth k l)))))
  :hints (("Goal" :induct (cdr-n-induct k l)
           :in-theory (enable w3t::step/prefix7 take nth nthcdr vals-p (:e value-head-p)))))
(defthm step_read/split/search134-gives-throw_ref
  (implies (w3t::step_read/split/search134 k lo hi l)
           (member-equal (car (nth (w3t::step/prefix7 l) l)) '(:ref.exn_addr :throw_ref)))
  :hints (("Goal" :induct (w3t::step_read/split/search134 k lo hi l)
           :in-theory (enable w3t::step_read/split/search134 (:e value-head-p)))))
(defthm step_pure/r-trap-instrs-fails-when-first-instr-not-trap
  (implies (not (equal (car (nth (w3t::step/prefix7 l) l)) :trap))
           (equal (w3t::step_pure/r-trap-instrs l) nil))
  :hints (("Goal" :in-theory (enable w3t::step_pure/r-trap-instrs))))
(defthm step_read/split/r-throw_ref-instrs-fails-when-first-instr-not-throw_ref
  (implies (not (member-equal (car (nth (w3t::step/prefix7 l) l)) '(:ref.exn_addr :throw_ref)))
           (equal (w3t::step_read/split/r-throw_ref-instrs (list :|%;%| z l)) nil))
  :hints (("Goal" :in-theory (e/d (w3t::step_read/split/r-throw_ref-instrs) (step_read/split/search134-gives-throw_ref))
           :use ((:instance step_read/split/search134-gives-throw_ref
                            (k (w3t::%tag-lo :ref.exn_addr 0 l)) (lo (w3t::%tag-lo :ref.exn_addr 0 l)) (hi (len l)))))))

; --- v ++ (i) ++ r -----------------------------------------------------------
(defthm prefix7-of-append-of-vals-and-instr
  (implies (and (vals-p v) (not (w3t::val-p i)))
           (equal (w3t::step/prefix7 (append v (cons i r))) (len v)))
  :hints (("Goal" :induct (len v) :in-theory (enable w3t::step/prefix7 vals-p))))
(defthm redex-shape-p-of-append-of-vals-and-instr
  (implies (and (vals-p v) (not (value-head-p (car i))))
           (equal (redex-shape-p kw (append v (cons i r)))
                  (and (atom r) (equal (car i) kw))))
  :hints (("Goal" :induct (len v) :in-theory (enable redex-shape-p vals-p))))
(defthm consp-when-vals-p-and-non-nil
  (implies (and (vals-p v) v) (consp v))
  :hints (("Goal" :in-theory (enable vals-p)))
  :rule-classes :forward-chaining)
(defthm len-of-append-of-cons-not-1
  (implies (or (consp v) (consp r))
           (not (equal (len (append v (cons i r))) 1))))

; --- nop ---------------------------------------------------------------------
(defthm step_pure/r-nop-fails-when-not-one
  (implies (not (equal (len l) 1)) (equal (w3t::step_pure/r-nop l) nil))
  :hints (("Goal" :in-theory (enable w3t::step_pure/r-nop))))

(defthm step_pure/r-nop-of-append-of-vals-and-instr
  (implies (or (consp v) (consp r))
           (equal (w3t::step_pure/r-nop (append v (cons i r))) nil))
  :hints (("Goal" :use ((:instance step_pure/r-nop-fails-when-not-one (l (append v (cons i r))))
                        (:instance len-of-append-of-cons-not-1))
           :in-theory (disable step_pure/r-nop-fails-when-not-one len-of-append-of-cons-not-1))))

(set-inhibit-output-lst '(proof-tree prove event common-lisp::warning warning! observation))
; The relation functions are opened; every rule function stays closed and
; is rewritten to NIL by its lemma.
(defthm step_pure-of-vals-nop-rest
  (implies (and (vals-p v) (or (consp v) (consp r)))
           (equal (w3t::step_pure (append v (cons '(:nop) r))) nil))
  :hints (("Goal" :in-theory (enable w3t::step_pure (:e value-head-p)) :do-not-induct t)))
(defthm step_read/split-of-vals-nop-rest
  (implies (and (vals-p v) (or (consp v) (consp r)))
           (equal (w3t::step_read/split (list :|%;%| z (append v (cons '(:nop) r)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step_read/split (:e value-head-p)) :do-not-induct t)))

; The V1 exit statement for nop.
(defthm step/r-pure-of-vals-nop-rest
  (implies (and (vals-p v) (or (consp v) (consp r)))
           (equal (w3t::step/r-pure (list :|%;%| z (append v (cons '(:nop) r)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-pure) :do-not-induct t)))
(defthm step/r-read-of-vals-nop-rest
  (implies (and (vals-p v) (or (consp v) (consp r)))
           (equal (w3t::step/r-read (list :|%;%| z (append v (cons '(:nop) r)))) nil))
  :hints (("Goal" :in-theory (enable w3t::step/r-read) :do-not-induct t)))
(value-triple (cw "SPIKE-DONE~%"))
