; E7: the fast machine. Phase A (test before proving, D7): the machine runs
; and is compared with the list machine of E6; the refinement theorem comes
; next, from the lemmas of frame.lisp and memory.lisp.
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

(program)
(set-irrelevant-formals-ok t)
(set-ignore-ok t)

; --- the array -----------------------------------------------------------

(defun mem-to-list-loop (i fm acc)       ; bytes 0..i-1 consed onto ACC, in order
  (declare (xargs :stobjs fm))
  (if (zp i) acc
    (mem-to-list-loop (1- i) fm (cons (fm-memi (1- i) fm) acc))))

(defun mem-to-list (fm)
  (declare (xargs :stobjs fm))
  (mem-to-list-loop (fm-mem-length fm) fm nil))

(defun list-to-mem-loop (l i fm)
  (declare (xargs :stobjs fm))
  (if (atom l) fm
    (let ((fm (update-fm-memi i (car l) fm))) (list-to-mem-loop (cdr l) (1+ i) fm))))

(defun list-to-mem (l fm)                ; the array becomes the byte list L
  (declare (xargs :stobjs fm))
  (let ((fm (resize-fm-mem (len l) fm))) (list-to-mem-loop l 0 fm)))

(defun mem-window (a n fm)               ; (take n (nthcdr a bytes))
  (declare (xargs :stobjs fm))
  (if (zp n) nil
    (cons (if (and (natp a) (< a (fm-mem-length fm))) (fm-memi a fm) nil)
          (mem-window (1+ (nfix a)) (1- n) fm))))

(defun mem-write (a bytes fm)            ; write BYTES at A (the splice of $WITH_MEM)
  (declare (xargs :stobjs fm))
  (if (atom bytes) fm
    (let ((fm (if (and (natp a) (< a (fm-mem-length fm)) (natp (car bytes)) (< (car bytes) 256))
                  (update-fm-memi a (car bytes) fm)
                fm)))
      (mem-write (1+ (nfix a)) (cdr bytes) fm))))

; --- the store without its bytes -------------------------------------------

(defun store-without-bytes (s) (put-mem0-bytes s nil))
(defun mem0-of-store (s) (wrt::%get-field (car (wrt::%get-field s :mems)) :bytes))

; --- generated fast versions of the memory rules ---------------------------

(defun bytes-form-p (x)                  ; (%get-field ($mem z x) ':bytes)
  (and (consp x) (eq (car x) 'wrt::%get-field)
       (consp (cadr x)) (eq (car (cadr x)) 'w3t::$mem)
       (equal (caddr x) '':bytes)))

(mutual-recursion
 (defun subst-memory (term)
   (cond ((or (atom term) (eq (car term) 'quote)) term)
         ((and (eq (car term) 'len) (bytes-form-p (cadr term)))
          '(fm-mem-length fm))
         ((and (eq (car term) 'take) (consp (caddr term)) (eq (car (caddr term)) 'nthcdr)
               (bytes-form-p (caddr (caddr term))))
          `(mem-window ,(subst-memory (cadr (caddr term))) ,(subst-memory (cadr term)) fm))
         ((eq (car term) 'w3t::$with_mem)    ; ($with_mem z x i j b) -> (:write z i b)
          `(list :write ,(subst-memory (cadr term)) ,(subst-memory (cadddr term))
                 ,(subst-memory (cadr (cddddr term)))))
         ((bytes-form-p term) '(:unsupported-bytes-access))
         ((consp (car term))
          (cons (list 'lambda (cadr (car term)) (subst-memory (caddr (car term))))
                (subst-memory-list (cdr term))))
         (t (cons (car term) (subst-memory-list (cdr term))))))
 (defun subst-memory-list (terms)
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
    w3t::step_read/split/r-memory.copy-le w3t::step_read/split/r-memory.copy-gt))

(defun fast-name (fn)
  (intern-in-package-of-symbol (concatenate 'string "FAST-" (symbol-name fn)) 'we::here))

(defun fast-defuns (fns wrld)
  (if (endp fns) nil
    (let* ((fn (car fns)) (formals (acl2::formals fn wrld))
           (body (getpropc fn 'acl2::unnormalized-body nil wrld)))
      (cons `(defun ,(fast-name fn) (,@formals fm)
               (declare (xargs :stobjs fm :mode :program) (ignorable fm))
               ,(subst-memory body))
            (fast-defuns (cdr fns) wrld)))))

(defun fast-dispatch-cases (fns)
  (if (endp fns) nil
    (cons `(,(car fns) (,(fast-name (car fns)) arg fm)) (fast-dispatch-cases (cdr fns)))))

(make-event
 `(progn ,@(fast-defuns *fast-memory-rules* (w state))
         (defun fast-memory-rule (fn arg fm)
           (declare (xargs :stobjs fm :mode :program))
           (case fn ,@(fast-dispatch-cases *fast-memory-rules*) (otherwise nil)))))

; --- applying a rule --------------------------------------------------------

(defun frame-safe-rules (rules)          ; pure, or a frame lemma in frame.lisp
  (cond ((endp rules) nil)
        ((or (eq (rule-kind (car rules)) :pure)
             (and (d5-rule-p (car rules)) (not (memory-rule-p (car rules)))
                  (not (member-eq (car rules) *frame-not-yet*))))
         (cons (car rules) (frame-safe-rules (cdr rules))))
        (t (frame-safe-rules (cdr rules)))))

; computed once (the test per rule application used string operations)
(make-event `(defconst *frame-safe-rules* ',(frame-safe-rules *step-rules*)))

(defun frame-safe-p (fn) (member-eq fn *frame-safe-rules*))

(defun fm-z (fm) (declare (xargs :stobjs fm)) (list :|%;%| (fm-store fm) (fm-frame fm)))

; The fallback copies the memory twice, so it is not entered for a rule that
; cannot match: every rule's pattern has its opcode at the head of an
; instruction at the top level of the redex, or of the body of the one
; administrative term the redex is (entry rules). (Rule ids are OPCODE-...;
; the keyword is computed once per rule.)
(defun rule-op-keywords (rules)
  (if (endp rules) nil
    (let* ((id (rule-id (car rules))) (dash (search "-" id))
           (op (if dash (subseq id 0 dash) id)) (op (if (equal op "IF") "IFELSE" op)))
      (cons (cons (car rules) (intern op "KEYWORD")) (rule-op-keywords (cdr rules))))))

(make-event `(defconst *rule-op-keyword* ',(rule-op-keywords *step-rules*)))

(defun head-in-p (kw instrs)
  (and (consp instrs)
       (or (and (consp (car instrs)) (eq (car (car instrs)) kw))
           (head-in-p kw (cdr instrs)))))

(defun rule-may-match (fn redex)
  (let ((kw (cdr (assoc-eq fn *rule-op-keyword*))))
    (or (head-in-p kw redex)
        (and (consp redex) (null (cdr redex)) (admin-kind (car redex))
             (head-in-p kw (car (drop-n 3 (car redex))))))))

; (mv fired z' instrs' fm): rule FN on REDEX in state Z (whose store has no bytes)
(defun fast-apply-rule (fn z redex fm)
  (declare (xargs :stobjs fm))
  (cond
   ((member-eq fn *fast-memory-rules*)
    (let* ((arg (if (eq (rule-kind fn) :pure) redex (list :|%;%| z redex)))
           (r (fast-memory-rule fn arg fm)))
      (cond ((atom r) (mv nil z nil fm))
            ((eq (rule-kind fn) :step)
             (let* ((cfg (car r)) (z2 (cadr cfg)))
               (if (and (consp z2) (eq (car z2) :write))
                   ; ($with_mem z x i j b): the store is z, b is spliced in at i;
                   ; $with_mem gives no state when b is not a true list
                   (if (true-listp (cadddr z2))
                       (let ((fm (mem-write (caddr z2) (cadddr z2) fm)))
                         (mv t (cadr z2) (caddr cfg) fm))
                     (mv t nil (caddr cfg) fm))
                 (mv t z2 (caddr cfg) fm))))
            (t (mv t z (car r) fm)))))
   ((frame-safe-p fn)
    (mv-let (ok z2 res) (apply-rule fn z redex) (mv ok z2 res fm)))
   ((not (rule-may-match fn redex)) (mv nil z nil fm))
   (t ; the slow fallback
    (let* ((zfull (put-z-bytes z (mem-to-list fm))))
      (mv-let (ok z2 res) (apply-rule fn zfull redex)
        (if (not ok) (mv nil z nil fm)
          (let* ((fm (list-to-mem (mem0-of-store (cadr z2)) fm)))
            (mv t (put-z-bytes z2 nil) res fm))))))))

(defun fast-try-rules (rules z redex fm)
  (declare (xargs :stobjs fm))
  (if (atom rules) (mv nil z nil fm)
    (mv-let (ok z2 res fm) (fast-apply-rule (car rules) z redex fm)
      (if ok (mv t z2 res fm) (fast-try-rules (cdr rules) z redex fm)))))

; --- one step: MACHINE-STEP over FM -------------------------------------------

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
  (let* ((e (car (fm-ctrl fm))) (k (entry-kind e))
         (term (admin-term k (entry-n e) (if (eq k :f) (fm-frame fm) (entry-x e))
                           (rev-onto (fm-vals fm) (fm-is fm))))
         (outer-frame (if (eq k :f) (entry-x e) (fm-frame fm))))
    (mv-let (ok z2 res fm)
      (fast-try-rules (rules-for (list :entry k)) (list :|%;%| (fm-store fm) outer-frame) (list term) fm)
      (if ok
          (fm-set (car-t (drop-n 1 z2)) (car-t (drop-n 2 z2)) (entry-v e) (app res (entry-r e))
                  (cdr (fm-ctrl fm)) :run fm)
        (update-fm-status :stuck fm)))))

(defun fast-anyprefix-step (fm)
  (declare (xargs :stobjs fm))
  (mv-let (ok z2 res fm)
    (fast-try-rules (rules-for :anyprefix) (fm-z fm) (rev-onto (fm-vals fm) (fm-is fm)) fm)
    (if (and ok (true-listp res))
        (fm-set (car-t (drop-n 1 z2)) (car-t (drop-n 2 z2)) nil res (fm-ctrl fm) :run fm)
      (update-fm-status :stuck fm))))

(defun fast-op-step (fm)
  (declare (xargs :stobjs fm))
  (let* ((i (car (fm-is fm))) (vals (fm-vals fm))
         (rules (rules-for (list :op (entry-kind i))))
         (k (redex-arity i (fm-z fm) vals)))
    (cond ((or (atom rules) (not (natp k))) (update-fm-status :unsupported fm))
          ((< (len-t vals) k) (update-fm-status :stuck fm))
          (t (mv-let (ok z2 res fm)
               (fast-try-rules rules (fm-z fm) (rev-onto (take-n k vals) (list i)) fm)
               (if ok
                   (fm-set (car-t (drop-n 1 z2)) (car-t (drop-n 2 z2)) (drop-n k vals)
                           (app res (cdr (fm-is fm))) (fm-ctrl fm) :run fm)
                 (update-fm-status :stuck fm)))))))

(defun fast-step (fm)
  (declare (xargs :stobjs fm))
  (if (not (eq (fm-status fm) :run)) fm
    (let ((is (fm-is fm)) (vals (fm-vals fm)) (ctrl (fm-ctrl fm)))
      (if (atom is)
          (if (atom ctrl) (update-fm-status :done fm) (fast-exit-step fm))
        (let ((i (car is)))
          (cond ((value-instr-p i)
                 (let* ((fm (update-fm-vals (cons i vals) fm))) (update-fm-is (cdr is) fm)))
                ((admin-kind i) (fast-enter-step fm))
                ((and (eq (entry-kind i) :throw_ref) (eq (entry-kind (car-t vals)) :ref.null))
                 (fast-op-step fm))
                ((and (sym-member (entry-kind i) '(:trap :throw_ref))
                      (or (consp (cdr is))
                          (if (eq (entry-kind i) :trap) (consp vals) (consp (cdr vals)))))
                 (fast-anyprefix-step fm))
                ((and (equal i '(:trap)) (atom ctrl)) (update-fm-status :trap fm))
                ((and (equal i '(:throw_ref)) (atom ctrl) (eq (entry-kind (car-t vals)) :ref.exn_addr))
                 (update-fm-status :throw fm))
                ((and (exit-instr-p i) (consp ctrl)) (fast-exit-step fm))
                ((exit-instr-p i) (update-fm-status :stuck fm))
                (t (fast-op-step fm))))))))

(defun fast-run (n fm)                   ; at most N steps
  (declare (xargs :stobjs fm))
  (if (or (zp n) (not (eq (fm-status fm) :run))) fm
    (let ((fm (fast-step fm))) (fast-run (1- n) fm))))

; --- between the two machines -----------------------------------------------

(defun fm-load-ms (s fm)                  ; list state -> FM
  (declare (xargs :stobjs fm))
  (let* ((store (ms-store s))
         (fm (list-to-mem (mem0-of-store store) fm)))
    (fm-set (store-without-bytes store) (ms-frame s) (ms-vals s) (ms-is s) (ms-ctrl s) (ms-status s) fm)))

(defun fm->ms (fm)                        ; FM -> list state (bytes put back)
  (declare (xargs :stobjs fm))
  (ms (put-mem0-bytes (fm-store fm) (mem-to-list fm))
      (fm-frame fm) (fm-vals fm) (fm-is fm) (fm-ctrl fm) (fm-status fm)))
