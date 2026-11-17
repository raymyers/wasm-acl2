; E7: the fast machine. Logic mode, guards verified (it runs as compiled
; Lisp). Tested against the list machine of E6 at every step (fasttest.lsp);
; the refinement theorem comes next, from the lemmas of frame.lisp and
; memory.lisp. Code generators are in program mode.
;
; The state is the stobj FM. Its fields are those of the list machine's
; state, except that memory 0's bytes live in the byte array MEM and the
; store holds an empty byte list for memory 0. FM->MS puts them back.
;
; A rule function is applied in one of three ways:
;   - a memory rule of D5 (loads, stores, their bounds rules, memory.size,
;     memory.fill, memory.copy): its fast version, generated below from the
;     rule's own body by replacing the three forms in which it touches
;     memory, (len bytes), (take n (nthcdr a bytes)) and
;     ($with_mem z x i j new), by array operations;
;   - a pure rule, or a rule with a frame lemma in frame.lisp: the rule
;     function itself, on the store without bytes;
;   - any other rule: the slow fallback, exact for every rule: the bytes are
;     copied into the store, the rule runs, and the result's bytes are copied
;     back into the array.
; One memory is assumed, as in memory.lisp (ONE-MEMORY-P); MuPDF and the
; slide renderer have one.
(in-package "WE")
(include-book "memory")

(defstobj fm
  (fm-store :type t) (fm-frame :type t) (fm-vals :type t) (fm-is :type t)
  (fm-ctrl :type t) (fm-status :type t)
  (fm-mem :type (common-lisp::array (common-lisp::unsigned-byte 8) (0)) :resizable t :initially 0))

(set-irrelevant-formals-ok t)
(set-ignore-ok t)

; --- the array -----------------------------------------------------------

(defun mem-to-list-loop (i fm acc)       ; bytes 0..i-1 consed onto ACC, in order
  (declare (xargs :stobjs fm :guard (and (natp i) (<= i (fm-mem-length fm))) :measure (nfix i)))
  (if (zp i) acc
    (mem-to-list-loop (1- i) fm (cons (fm-memi (1- i) fm) acc))))

(defun mem-to-list (fm)
  (declare (xargs :stobjs fm))
  (mem-to-list-loop (fm-mem-length fm) fm nil))

(defun byte-or-zero (b)
  (declare (xargs :guard t))
  (if (and (natp b) (< b 256)) b 0))

(defun list-to-mem-loop (l i fm)
  (declare (xargs :stobjs fm :guard (natp i)))
  (if (or (atom l) (not (and (natp i) (< i (fm-mem-length fm))))) fm
    (let ((fm (update-fm-memi i (byte-or-zero (car l)) fm))) (list-to-mem-loop (cdr l) (1+ i) fm))))

(defun list-to-mem (l fm)                ; the array becomes the byte list L
  (declare (xargs :stobjs fm))
  (let ((fm (resize-fm-mem (len-t l) fm))) (list-to-mem-loop l 0 fm)))

(defun mem-window (a n fm)               ; (take n (nthcdr a bytes)); NTHCDR reads a non-natural A as 0
  (declare (xargs :stobjs fm :guard (natp n)))
  (if (zp n) nil
    (let ((a (nfix a)))
      (cons (if (< a (fm-mem-length fm)) (fm-memi a fm) nil)
            (mem-window (1+ a) (1- n) fm)))))

(defun mem-write (a bytes fm)            ; write BYTES at A (the splice of $WITH_MEM)
  (declare (xargs :stobjs fm :guard t))
  (if (atom bytes) fm
    (let ((fm (if (and (natp a) (< a (fm-mem-length fm)) (natp (car bytes)) (< (car bytes) 256))
                  (update-fm-memi a (car bytes) fm)
                fm)))
      (mem-write (1+ (nfix a)) (cdr bytes) fm))))

; --- the store without its bytes -------------------------------------------

(defun store-without-bytes (s) (declare (xargs :guard t)) (ec-call (put-mem0-bytes s nil)))
(defun mem0-of-store (s)
  (declare (xargs :guard t))
  (wrt::%get-field (car-t (wrt::%get-field s :mems)) :bytes))

; --- generated fast versions of the memory rules ---------------------------

(defun bytes-form-p (x)                  ; (%get-field ($mem z x) ':bytes)
  (declare (xargs :mode :program))
  (and (consp x) (eq (car x) 'wrt::%get-field)
       (consp (cadr x)) (eq (car (cadr x)) 'w3t::$mem)
       (equal (caddr x) '':bytes)))

(mutual-recursion
 (defun subst-memory (term)
   (declare (xargs :mode :program))
   (cond ((or (atom term) (eq (car term) 'quote)) term)
         ((and (eq (car term) 'len) (bytes-form-p (cadr term)))
          '(fm-mem-length fm))
         ((and (eq (car term) 'take) (consp (caddr term)) (eq (car (caddr term)) 'nthcdr)
               (bytes-form-p (caddr (caddr term))))
          `(mem-window ,(subst-memory (cadr (caddr term))) ,(subst-memory (cadr term)) fm))
         ((eq (car term) 'w3t::$with_mem)    ; ($with_mem z x i j b) -> (:write z i j b)
          `(list :write ,(subst-memory (cadr term)) ,(subst-memory (cadddr term))
                 ,(subst-memory (car (cddddr term))) ,(subst-memory (cadr (cddddr term)))))
         ((bytes-form-p term) '(:unsupported-bytes-access))
         ((consp (car term))
          (cons (list 'lambda (cadr (car term)) (subst-memory (caddr (car term))))
                (subst-memory-list (cdr term))))
         (t (cons (car term) (subst-memory-list (cdr term))))))
 (defun subst-memory-list (terms)
   (declare (xargs :mode :program))
   (if (atom terms) nil (cons (subst-memory (car terms)) (subst-memory-list (cdr terms))))))

(defconst *fast-memory-rules*
  '(w3t::step_read/split/r-load-num-oob w3t::step_read/split/r-load-num-val
    w3t::step_read/split/r-load-pack-oob w3t::step_read/split/r-load-pack-val
    w3t::step/r-store-num-oob w3t::step/r-store-num-val
    w3t::step/r-store-pack-oob w3t::step/r-store-pack-val
    w3t::step_read/split/r-memory.size
    w3t::step_read/split/r-memory.fill-oob w3t::step_read/split/r-memory.fill-zero
    w3t::step_read/split/r-memory.fill-succ
    w3t::step_read/split/r-memory.copy-oob w3t::step_read/split/r-memory.copy-zero
    w3t::step_read/split/r-memory.copy-le w3t::step_read/split/r-memory.copy-gt
    w3t::step_read/split/r-memory.init-oob w3t::step_read/split/r-memory.init-zero
    w3t::step_read/split/r-memory.init-succ))

(defconst *fast-memory-step-rules*
  '(w3t::step/r-store-num-oob w3t::step/r-store-num-val w3t::step/r-store-pack-oob w3t::step/r-store-pack-val))

(defun fast-name (fn)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string "FAST-" (symbol-name fn)) 'we::here))

(defun fast-defuns (fns wrld)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (let* ((fn (car fns)) (formals (acl2::formals fn wrld))
           (body (getpropc fn 'acl2::unnormalized-body nil wrld)))
      (cons `(defun ,(fast-name fn) (,@formals fm)
               (declare (xargs :stobjs fm :verify-guards nil) (ignorable fm))
               ,(subst-memory body))
            (fast-defuns (cdr fns) wrld)))))

(defun fast-dispatch-cases (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (cons `(,(car fns) (,(fast-name (car fns)) arg fm)) (fast-dispatch-cases (cdr fns)))))

(make-event
 `(progn ,@(fast-defuns *fast-memory-rules* (w state))
         (defun fast-memory-rule (fn arg fm)
           (declare (xargs :stobjs fm :verify-guards nil))
           (case fn ,@(fast-dispatch-cases *fast-memory-rules*) (otherwise nil)))))

; --- applying a rule --------------------------------------------------------

(defun frame-safe-rules (rules)          ; pure, or a frame lemma in frame.lisp
  (declare (xargs :mode :program))
  (cond ((endp rules) nil)
        ((or (eq (rule-kind (car rules)) :pure)
             (and (d5-rule-p (car rules)) (not (memory-rule-p (car rules)))
                  (not (member-eq (car rules) *frame-not-yet*))))
         (cons (car rules) (frame-safe-rules (cdr rules))))
        (t (frame-safe-rules (cdr rules)))))

; computed once (the test per rule application used string operations)
(make-event `(defconst *frame-safe-rules* ',(frame-safe-rules *step-rules*)))

(defun frame-safe-p (fn) (declare (xargs :guard t)) (sym-member fn *frame-safe-rules*))

(defun fm-z (fm) (declare (xargs :stobjs fm)) (list :|%;%| (fm-store fm) (fm-frame fm)))

; The fallback copies the memory twice, so it is not entered for a rule that
; cannot match: every rule's pattern has its opcode at the head of an
; instruction at the top level of the redex, or of the body of the one
; administrative term the redex is (entry rules). (Rule ids are OPCODE-...;
; the keyword is computed once per rule.)
(defun rule-op-keywords (rules)
  (declare (xargs :mode :program))
  (if (endp rules) nil
    (let* ((id (rule-id (car rules))) (dash (search "-" id))
           (op (if dash (subseq id 0 dash) id)) (op (if (equal op "IF") "IFELSE" op)))
      (cons (cons (car rules) (intern op "KEYWORD")) (rule-op-keywords (cdr rules))))))

(make-event `(defconst *rule-op-keyword* ',(rule-op-keywords *step-rules*)))

(defun head-in-p (kw instrs)
  (declare (xargs :guard t))
  (and (consp instrs)
       (or (and (consp (car instrs)) (equal (car (car instrs)) kw))
           (head-in-p kw (cdr instrs)))))

(defun rule-may-match (fn redex)
  (declare (xargs :guard t))
  (let ((kw (cdr (assoc-equal fn *rule-op-keyword*))))
    (or (head-in-p kw redex)
        (and (consp redex) (null (cdr redex)) (admin-kind (car redex))
             (head-in-p kw (car-t (drop-n 3 (car redex))))))))

(verify-guards all-zero-p)

(defun fast-one-memory-p (z)             ; ONE-MEMORY-P, with its guard verified
  (declare (xargs :guard t))
  (let ((mems (wrt::%get-field (car-t (cdr-t z)) :mems)))
    (and (consp mems) (atom (cdr mems))
         (all-zero-p (wrt::%get-field (wrt::%get-field (car-t (cdr-t (cdr-t z))) :module) :mems)))))

(defthm fast-one-memory-p-is-one-memory-p
  (equal (fast-one-memory-p z) (one-memory-p z))
  :hints (("Goal" :in-theory (enable car-t cdr-t))))

(defun byte-list-p (l)
  (declare (xargs :guard t))
  (if (atom l) (null l) (and (natp (car l)) (< (car l) 256) (byte-list-p (cdr l)))))

(defun mem0-shape-ok (s)                 ; memory 0 a record with a byte list
  (declare (xargs :guard t))
  (let ((mems (wrt::%get-field s :mems)))
    (and (consp s) (alistp (cdr s)) (assoc-equal :mems (cdr s))
         (consp mems) (consp (car mems)) (alistp (cdr (car mems)))
         (assoc-equal :bytes (cdr (car mems)))
         (byte-list-p (wrt::%get-field (car mems) :bytes)))))

(defun config-shape-ok (z)
  (declare (xargs :guard t))
  (and (true-listp z) (equal (len z) 3) (equal (car z) :|%;%|) (mem0-shape-ok (cadr z))))

(defun fallback-shape-ok (z)             ; what the fast machine can hold
  (declare (xargs :guard t))
  (and (config-shape-ok z) (ec-call (store-fields-p (cadr z)))))

; the slow fallback: the rule on the full store (bytes copied out of the
; array), the result's bytes copied back. A result the fast machine cannot
; hold (memory 0 not a byte list, a store field missing) is refused: the
; step then stops with status :unsupported.
(defun fast-apply-fallback (fn z redex fm)
  (declare (xargs :stobjs fm :guard t))
  (let* ((zfull (ec-call (put-z-bytes z (mem-to-list fm)))))
    (mv-let (ok z2 res) (apply-rule fn zfull redex)
      (cond ((not ok) (mv nil z nil fm))
            ((not (fallback-shape-ok z2)) (mv :refuse z nil fm))
            (t (let* ((fm (list-to-mem (mem0-of-store (car-t (drop-n 1 z2))) fm)))
                 (mv t (ec-call (put-z-bytes z2 nil)) res fm)))))))

; (mv fired z' instrs' fm): rule FN on REDEX in state Z (whose store has no bytes)
(defun fast-apply-rule (fn z redex fm)
  (declare (xargs :stobjs fm :guard t))
  (cond
   ((and (sym-member fn *fast-memory-rules*)
         ; the fast versions read the array as the instruction's memory: one
         ; memory in the store, and the module's memory index maps to it.
         ; Otherwise (several modules' memories) the exact fallback below.
         (fast-one-memory-p z))
    ; every memory rule is a STEP_READ/SPLIT rule (configuration in,
    ; instructions out) or a STEP rule (configuration in, configuration out)
    (let* ((step-rule (sym-member fn *fast-memory-step-rules*))
           (r (ec-call (fast-memory-rule fn (list :|%;%| z redex) fm))))
      (cond ((atom r) (mv nil z nil fm))
            (step-rule
             (let* ((cfg (car r)) (z2 (car-t (drop-n 1 cfg))) (res (car-t (drop-n 2 cfg))))
               (if (and (consp z2) (eq (car z2) :write))
                   ; ($with_mem z x i j b): the store is z; the J bytes at I
                   ; become B. Written into the array when B is J bytes that
                   ; fit; otherwise refused (the store rules check the bounds
                   ; and write $nbytes_, which is J bytes: not met in practice)
                   (let ((i (car-t (drop-n 2 z2))) (j (car-t (drop-n 3 z2))) (b (car-t (drop-n 4 z2))))
                     (if (and (natp i) (byte-list-p b) (equal (len-t b) j) (<= (+ i j) (fm-mem-length fm)))
                         (let ((fm (mem-write i b fm)))
                           (mv t (car-t (drop-n 1 z2)) res fm))
                       (mv :refuse z nil fm)))
                 (mv t z2 res fm))))
            (t (mv t z (car r) fm)))))
   ((sym-member fn *fast-memory-rules*)
    (if (rule-may-match fn redex) (fast-apply-fallback fn z redex fm) (mv nil z nil fm)))
   ((frame-safe-p fn)
    (mv-let (ok z2 res) (apply-rule fn z redex) (mv ok z2 res fm)))
   ((not (rule-may-match fn redex)) (mv nil z nil fm))
   (t (fast-apply-fallback fn z redex fm))))

(defun fast-try-rules (rules z redex fm)
  (declare (xargs :stobjs fm :guard t))
  (if (atom rules) (mv nil z nil fm)
    (mv-let (ok z2 res fm) (fast-apply-rule (car rules) z redex fm)
      (if ok (mv ok z2 res fm) (fast-try-rules (cdr rules) z redex fm)))))

; --- direct dispatch (performance) -------------------------------------------
; FAST-TRY-RULES looks the rule list up by an EQUAL key (RULES-FOR) and
; FAST-APPLY-RULE then finds each rule's path and calls it through a CASE over
; 212 rule names. Measured on one i32.sub step (0.86 us): the arithmetic
; ($BINOP_) is 0.05 us, the rule's pattern match 0.08 us, the dispatch 0.36
; us. Here, for every place (an opcode, an entry kind, :anyprefix), one
; generated function calls that place's rules in STEP's order, each through
; its fixed path. It computes what FAST-TRY-RULES computes.

(defun rule-call-form (fn)
  (declare (xargs :mode :program))
  ; (mv fired z' instrs' fm) for rule FN, with Z, REDEX, FM bound
  (cond ((member-eq fn *fast-memory-rules*) `(fast-apply-rule ',fn z redex fm))
        ((not (frame-safe-p fn)) `(fast-apply-rule ',fn z redex fm))
        ((eq (rule-kind fn) :pure)
         `(let ((r (ec-call (,fn redex)))) (if (consp r) (mv t z (car r) fm) (mv nil z nil fm))))
        ((eq (rule-kind fn) :read)
         `(let ((r (ec-call (,fn (list :|%;%| z redex))))) (if (consp r) (mv t z (car r) fm) (mv nil z nil fm))))
        (t `(let ((r (ec-call (,fn (list :|%;%| z redex)))))
              (if (consp r) (mv t (car-t (drop-n 1 (car r))) (car-t (drop-n 2 (car r))) fm)
                (mv nil z nil fm))))))

(defun chain-form (rules)
  (declare (xargs :mode :program))
  (if (endp rules) '(mv nil z nil fm)
    `(mv-let (ok z2 res fm) ,(rule-call-form (car rules))
       (if ok (mv ok z2 res fm) ,(chain-form (cdr rules))))))

(defun place-fn-name (place)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (if (consp place)
       (concatenate 'string "FAST-TRY-" (symbol-name (car place)) "-" (symbol-name (cadr place)))
     (concatenate 'string "FAST-TRY-" (symbol-name place)))
   'we::here))

(defun place-defuns (alist)
  (declare (xargs :mode :program))
  (if (endp alist) nil
    (cons `(defun ,(place-fn-name (caar alist)) (z redex fm)
             (declare (xargs :stobjs fm :guard t))
             ,(chain-form (cdar alist)))
          (place-defuns (cdr alist)))))

(defun op-dispatch-cases (alist)
  (declare (xargs :mode :program))
  (cond ((endp alist) nil)
        ((and (consp (caar alist)) (eq (car (caar alist)) :op))
         (cons `(,(cadr (caar alist)) (,(place-fn-name (caar alist)) z redex fm))
               (op-dispatch-cases (cdr alist))))
        (t (op-dispatch-cases (cdr alist)))))

(defun op-keys (places)
  (declare (xargs :mode :program))
  (cond ((endp places) nil)
        ((and (consp (car places)) (eq (car (car places)) :op))
         (cons (cadr (car places)) (op-keys (cdr places))))
        (t (op-keys (cdr places)))))

(make-event
 `(progn ,@(place-defuns *rule-places*)
         (defun fast-try-op (kw z redex fm)
           (declare (xargs :stobjs fm :guard t))
           (case kw ,@(op-dispatch-cases *rule-places*) (otherwise (mv nil z nil fm))))
         (defun op-has-rules (kw)
           (declare (xargs :guard t))
           (case kw (,(op-keys (strip-cars *rule-places*)) t)
             (otherwise nil)))
         (defun fast-try-entry (k z redex fm)
           (declare (xargs :stobjs fm :guard t))
           (case k (:l (fast-try-entry-l z redex fm)) (:h (fast-try-entry-h z redex fm))
             (otherwise (fast-try-entry-f z redex fm))))))

; --- one step: MACHINE-STEP over FM (after the dispatch it calls) -------------------------------------------

(defun fm-set (store frame vals is ctrl status fm)
  (declare (xargs :stobjs fm))
  (let* ((fm (update-fm-store store fm)) (fm (update-fm-frame frame fm))
         (fm (update-fm-vals vals fm)) (fm (update-fm-is is fm))
         (fm (update-fm-ctrl ctrl fm)))
    (update-fm-status status fm)))

(defun fast-enter-step (fm)
  (declare (xargs :stobjs fm))
  (let* ((i (car-t (fm-is fm))) (k (admin-kind i)))
    (if (enterable-p i)
        (let ((e (list k (entry-n i) (if (eq k :f) (fm-frame fm) (entry-x i)) (fm-vals fm) (cdr-t (fm-is fm)))))
          (fm-set (fm-store fm) (if (eq k :f) (entry-x i) (fm-frame fm)) nil (entry-v i)
                  (cons e (fm-ctrl fm)) :run fm))
      (update-fm-status :stuck fm))))



(defun fast-exit-step (fm)
  (declare (xargs :stobjs fm))
  (let* ((e (car-t (fm-ctrl fm))) (k (entry-kind e))
         (term (admin-term k (entry-n e) (if (eq k :f) (fm-frame fm) (entry-x e))
                           (rev-onto (fm-vals fm) (fm-is fm))))
         (outer-frame (if (eq k :f) (entry-x e) (fm-frame fm))))
    (mv-let (ok z2 res fm)
      (fast-try-entry k (list :|%;%| (fm-store fm) outer-frame) (list term) fm)
      (cond ((eq ok :refuse) (update-fm-status :unsupported fm))
            (ok (fm-set (car-t (drop-n 1 z2)) (car-t (drop-n 2 z2)) (entry-v e) (app res (entry-r e))
                        (cdr-t (fm-ctrl fm)) :run fm))
            (t (update-fm-status :stuck fm))))))

(defun fast-anyprefix-step (fm)
  (declare (xargs :stobjs fm))
  (mv-let (ok z2 res fm)
    (fast-try-anyprefix (fm-z fm) (rev-onto (fm-vals fm) (fm-is fm)) fm)
    (cond ((eq ok :refuse) (update-fm-status :unsupported fm))
          ((and ok (true-listp res))
           (fm-set (car-t (drop-n 1 z2)) (car-t (drop-n 2 z2)) nil res (fm-ctrl fm) :run fm))
          (t (update-fm-status :stuck fm)))))

(defun fast-op-step (fm)
  (declare (xargs :stobjs fm))
  (let* ((i (car-t (fm-is fm))) (vals (fm-vals fm)) (kw (entry-kind i))
         (k (redex-arity i (fm-z fm) vals)))
    (cond ((or (not (op-has-rules kw)) (not (natp k))) (update-fm-status :unsupported fm))
          ((< (len-t vals) k) (update-fm-status :stuck fm))
          (t (mv-let (ok z2 res fm)
               (fast-try-op kw (fm-z fm) (rev-onto (take-n k vals) (list i)) fm)
               (cond ((eq ok :refuse) (update-fm-status :unsupported fm))
                     (ok (fm-set (car-t (drop-n 1 z2)) (car-t (drop-n 2 z2)) (drop-n k vals)
                                 (app res (cdr-t (fm-is fm))) (fm-ctrl fm) :run fm))
                     (t (update-fm-status :stuck fm))))))))

; --- fast paths for the hottest instructions (performance) ---------------------
; Each computes the state the general path (FAST-OP-STEP: redex, place
; function, rule) computes, with the same spec functions, when the operands
; have the rule's shape; otherwise it declines and the general path runs.
; Measured on the slides: value pushes 45% of the steps, local.get 14.5,
; binop 11.7, local.set 5.6, br_if 4.2, relop 3.9, local.tee 3.1.

(defun i32-const-p (v)                   ; (:const (:i32) c), c an unsigned 32-bit integer
  (declare (xargs :guard t))
  (and (consp v) (eq (car v) :const) (consp (cdr v)) (equal (cadr v) '(:i32))
       (consp (cddr v)) (null (cdddr v)) (natp (caddr v)) (< (caddr v) 4294967296)))

(defthm i32-const-p-is-val-p
  (implies (i32-const-p v) (w3t::val-p v))
  :hints (("Goal" :in-theory (enable w3t::val-p))))

(defun fast-val-p (v)                    ; = VALUE-INSTR-P, the common case first
  (declare (xargs :guard t))
  (or (i32-const-p v) (value-instr-p v)))

(defun const-shape-p (v)                 ; (:const nt c)
  (declare (xargs :guard t))
  (and (consp v) (eq (car v) :const) (consp (cdr v)) (consp (cddr v)) (null (cdddr v))))

; (mv handled fm)
(defun fast-hot-step (i fm)
  (declare (xargs :stobjs fm :guard (consp i)))
  (let ((kw (car i)) (is (fm-is fm)) (vals (fm-vals fm)))
    (case kw
      (:local.get
       (if (and (consp (cdr i)) (null (cddr i)))
           (let ((cell (ec-call (w3t::$local (fm-z fm) (cadr i)))))
             (if (consp cell)
                 (let ((fm (update-fm-is (cons (car cell) (cdr-t is)) fm))) (mv t fm))
               (mv nil fm)))
         (mv nil fm)))
      (:local.set
       (if (and (consp (cdr i)) (null (cddr i)) (consp vals) (fast-val-p (car vals)))
           (let* ((z2 (ec-call (w3t::$with_local (fm-z fm) (cadr i) (car vals))))
                  (fm (update-fm-store (car-t (drop-n 1 z2)) fm))
                  (fm (update-fm-frame (car-t (drop-n 2 z2)) fm))
                  (fm (update-fm-vals (cdr vals) fm)))
             (let ((fm (update-fm-is (cdr-t is) fm))) (mv t fm)))
         (mv nil fm)))
      (:local.tee
       (if (and (consp (cdr i)) (null (cddr i)) (consp vals) (fast-val-p (car vals)))
           (let* ((v (car vals))
                  (fm (update-fm-vals (cdr vals) fm)))
             (let ((fm (update-fm-is (list* v v (list :local.set (cadr i)) (cdr-t is)) fm))) (mv t fm)))
         (mv nil fm)))
      ((:binop :relop)
       (if (and (consp (cdr i)) (consp (cddr i)) (null (cdddr i))
                (consp vals) (consp (cdr vals))
                (const-shape-p (car vals)) (const-shape-p (cadr vals))
                (equal (cadr (cadr vals)) (cadr i)) (equal (cadr (car vals)) (cadr i)))
           (let ((nt (cadr i)) (op (caddr i)) (c1 (caddr (cadr vals))) (c2 (caddr (car vals))))
             (if (eq kw :binop)
                 (let ((r (ec-call (w3t::$binop_ nt op c1 c2))))
                   (cond ((consp r)
                          (let ((fm (update-fm-vals (cddr vals) fm)))
                            (let ((fm (update-fm-is (cons (list :const nt (car r)) (cdr-t is)) fm))) (mv t fm))))
                         ((null r)
                          (let ((fm (update-fm-vals (cddr vals) fm)))
                            (let ((fm (update-fm-is (cons (list :trap) (cdr-t is)) fm))) (mv t fm))))
                         (t (mv nil fm))))
               (let* ((c (ec-call (w3t::$relop_ nt op c1 c2)))
                      (fm (update-fm-vals (cddr vals) fm)))
                 (let ((fm (update-fm-is (cons (list :const (list :i32) c) (cdr-t is)) fm))) (mv t fm)))))
         (mv nil fm)))
      (:br_if
       (if (and (consp (cdr i)) (null (cddr i)) (consp vals)
                (const-shape-p (car vals)) (equal (cadr (car vals)) '(:i32)))
           (let ((fm (update-fm-vals (cdr vals) fm)))
             (if (equal (caddr (car vals)) 0)
                 (let ((fm (update-fm-is (cdr-t is) fm))) (mv t fm))
               (let ((fm (update-fm-is (cons (list :br (cadr i)) (cdr-t is)) fm))) (mv t fm))))
         (mv nil fm)))
      (otherwise (mv nil fm)))))

(defun fast-step (fm)
  (declare (xargs :stobjs fm))
  (if (not (eq (fm-status fm) :run)) fm
    (let ((is (fm-is fm)) (vals (fm-vals fm)) (ctrl (fm-ctrl fm)))
      (if (atom is)
          (if (atom ctrl) (update-fm-status :done fm) (fast-exit-step fm))
        (let ((i (car is)))
          (cond ((and (consp i) (sym-member (car i) '(:local.get :local.set :local.tee :binop :relop :br_if)))
                 ; none of the tests below holds for these: the general path is FAST-OP-STEP
                 (mv-let (handled fm) (fast-hot-step i fm)
                   (if handled fm (fast-op-step fm))))
                ((fast-val-p i)
                 (let* ((fm (update-fm-vals (cons i vals) fm))) (update-fm-is (cdr is) fm)))
                ((admin-kind i) (fast-enter-step fm))
                ((and (eq (entry-kind i) :throw_ref) (eq (entry-kind (car-t vals)) :ref.null))
                 (fast-op-step fm))
                ((and (sym-member (entry-kind i) '(:trap :throw_ref))
                      (or (consp (cdr is))
                          (if (eq (entry-kind i) :trap) (consp vals) (consp (cdr-t vals)))))
                 (fast-anyprefix-step fm))
                ((and (equal i '(:trap)) (atom ctrl)) (update-fm-status :trap fm))
                ((and (equal i '(:throw_ref)) (atom ctrl) (eq (entry-kind (car-t vals)) :ref.exn_addr))
                 (update-fm-status :throw fm))
                ((and (exit-instr-p i) (consp ctrl)) (fast-exit-step fm))
                ((exit-instr-p i) (update-fm-status :stuck fm))
                (t (fast-op-step fm))))))))

(defun fast-run (n fm)                   ; at most N steps
  (declare (xargs :stobjs fm :guard (natp n) :measure (nfix n)))
  (if (or (zp n) (not (eq (fm-status fm) :run))) fm
    (let ((fm (fast-step fm))) (fast-run (1- n) fm))))


; the step parts, with the direct dispatch

; --- between the two machines -----------------------------------------------

(defun fm-load-ms (s fm)                  ; list state -> FM
  (declare (xargs :stobjs fm :guard t))
  (let* ((store (ms-store s))
         (fm (list-to-mem (mem0-of-store store) fm)))
    (fm-set (store-without-bytes store) (ms-frame s) (ms-vals s) (ms-is s) (ms-ctrl s) (ms-status s) fm)))

(defun fm->ms (fm)                        ; FM -> list state (bytes put back)
  (declare (xargs :stobjs fm))
  (ms (ec-call (put-mem0-bytes (fm-store fm) (mem-to-list fm)))
      (fm-frame fm) (fm-vals fm) (fm-is fm) (fm-ctrl fm) (fm-status fm)))
