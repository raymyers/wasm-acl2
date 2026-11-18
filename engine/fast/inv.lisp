; License: MIT. See the file LICENSE at the top of the repository.
;
; V6 of plan/wasm-engine/plan2.md: the invariant of the fast machine, the
; run and the loader.
;   - FM-INV: the stobj is well formed (FMP), its store is the fast store
;     (FAST-INV-STORE) and the list state it stands for has the invariant of
;     the list machine (MACHINE-OK of FM->MS).
;   - FAST-STEP-KEEPS-FM-INV: a step keeps it.
;   - FAST-RUN-IS-MACHINE-RUN: a run that does not end :unsupported is, seen
;     through FM->MS, the run of the list machine, and keeps FM-INV.
;   - FM-INV-OF-FM-LOAD-MS, FM->MS-OF-FM-LOAD-MS: the loader gives a state
;     with the invariant that stands for the list state it was given.
;   - MACHINE-ABS-OF-MS-OF-CONFIG: a configuration of the shape
;     CONFIG-SHAPE-P is the abstraction of the list state made from it.
; One hypothesis is carried and is V7's to remove: the head instruction is
; not call_ref (FAST-STEP-REFINES has it; NO-CALL-REF-RUN says it of a run).
;
; Normal forms. The accessors and updaters of the stobj are enabled, as in
; the books below this one: a term about a field is (NTH k FM) and
; (UPDATE-NTH k v FM). The results of a function that returns several values
; are written with MV-NTH, which is disabled here; the lemmas of the older
; books that say CADDDR are restated.
(in-package "WE")
(include-book "ctrl-kinds")

(set-prover-step-limit 2000000)

(in-theory (disable mv-nth mv-nth-1-2-3 drop-n take-n rev-onto app sym-member update-nth nth
                    value-instr-p w3t::val-p fast-val-p exit-instr-p admin-kind enterable-p machine-step
                    fmp fm-set fm->ms fast-inv-store
                    apply-rule fast-apply-rule fast-apply-fallback fast-memory-rule
                    fast-try-rules rule-may-match frame-safe-p
                    fast-one-memory-p fast-one-memory-p-is-one-memory-p
                    list-to-mem mem-write mem-to-list
                    redex-arity entry-kind entry-n entry-x entry-v entry-r admin-term
                    fast-step fast-op-step fast-exit-step fast-anyprefix-step
                    fast-enter-step fast-hot-step
                    fast-step-refines))

; ---------------------------------------------------------------------------
; 1. The stobj stays well formed

(defthm fm-memp-becomes-byte-list-p
  (equal (fm-memp l) (byte-list-p l)))

(defthm fmp-of-update-nth
  (implies (and (fmp fm) (natp k) (< k *fm-memi*))
           (fmp (update-nth k v fm)))
  :hints (("Goal" :in-theory (enable fmp))))

(defthm fmp-of-update-nth-of-bytes
  (implies (and (fmp fm) (byte-list-p m))
           (fmp (update-nth *fm-memi* m fm)))
  :hints (("Goal" :in-theory (enable fmp))))

(defthm fmp-of-fm-set
  (implies (fmp fm)
           (fmp (fm-set s f v is c st fm)))
  :hints (("Goal" :in-theory (enable fm-set))))

(defthm nth-of-fm-set
  (and (equal (nth *fm-store* (fm-set s f v is c st fm)) s)
       (equal (nth *fm-frame* (fm-set s f v is c st fm)) f)
       (equal (nth *fm-vals* (fm-set s f v is c st fm)) v)
       (equal (nth *fm-is* (fm-set s f v is c st fm)) is)
       (equal (nth *fm-ctrl* (fm-set s f v is c st fm)) c)
       (equal (nth *fm-status* (fm-set s f v is c st fm)) st)
       (equal (nth *fm-memi* (fm-set s f v is c st fm)) (nth *fm-memi* fm)))
  :hints (("Goal" :in-theory (enable fm-set))))

(defthm byte-list-p-of-resize-list
  (implies (byte-list-p l)
           (byte-list-p (resize-list l n 0))))

(defthm fmp-of-mem-write
  (implies (fmp fm)
           (fmp (mem-write a b fm)))
  :hints (("Goal" :induct (mem-write a b fm) :in-theory (enable mem-write))))

(defthm fmp-of-list-to-mem-loop
  (implies (fmp fm)
           (fmp (list-to-mem-loop l i fm)))
  :hints (("Goal" :induct (list-to-mem-loop l i fm))))

(defthm fmp-of-list-to-mem
  (implies (fmp fm)
           (fmp (list-to-mem l fm)))
  :hints (("Goal" :in-theory (enable list-to-mem))))

(defthm fmp-of-fast-apply-fallback
  (implies (fmp fm)
           (fmp (mv-nth 3 (fast-apply-fallback fn z redex fm))))
  :hints (("Goal" :in-theory (enable fast-apply-fallback))))

(defthm fmp-of-fast-apply-rule
  (implies (fmp fm)
           (fmp (mv-nth 3 (fast-apply-rule fn z redex fm))))
  :hints (("Goal" :in-theory (enable fast-apply-rule))))

(defthm fmp-of-fast-try-rules
  (implies (fmp fm)
           (fmp (mv-nth 3 (fast-try-rules rules z redex fm))))
  :hints (("Goal" :induct (fast-try-rules rules z redex fm)
                  :in-theory (enable fast-try-rules))))

; FAST-TRY-RULES-OTHER of refine-op.lisp, with MV-NTH
(defthm nth-of-fast-try-rules-stobj
  (implies (not (equal k *fm-memi*))
           (equal (nth k (mv-nth 3 (fast-try-rules rules z redex fm)))
                  (nth k fm)))
  :hints (("Goal" :in-theory (enable mv-nth-1-2-3))))

; ---------------------------------------------------------------------------
; 2. A rule that fires and is not refused leaves a fast store

(defthm fast-inv-store-of-put-mem0-bytes-nil
  (implies (and (mem0-shape-ok s) (store-fields-p s))
           (fast-inv-store (put-mem0-bytes s nil)))
  :hints (("Goal" :in-theory (enable fast-inv-store fast-store-ok mem0-record-p mem0-shape-ok))))

; the fallback: the machine accepts a result only with FALLBACK-SHAPE-OK
(defthm fast-apply-fallback-keeps-inv-store
  (implies (and (mv-nth 0 (fast-apply-fallback fn z redex fm))
                (not (equal (mv-nth 0 (fast-apply-fallback fn z redex fm)) :refuse)))
           (fast-inv-store (cadr (mv-nth 1 (fast-apply-fallback fn z redex fm)))))
  :hints (("Goal" :in-theory (e/d (fast-apply-fallback fallback-shape-ok config-shape-ok)
                                  (put-mem0-bytes mem0-shape-ok store-fields-p)))))

; a pure or a read rule returns the state it was given
(defun state-rules (rules)
  (declare (xargs :mode :program))
  (cond ((endp rules) nil)
        ((eq (rule-kind (car rules)) :step) (cons (car rules) (state-rules (cdr rules))))
        (t (state-rules (cdr rules)))))

(make-event `(defconst *state-rules* ',(state-rules *step-rules*)))

(make-event
 `(defthm apply-rule-keeps-state-when-not-state-rule
    (implies (not (sym-member fn *state-rules*))
             (equal (mv-nth 1 (apply-rule fn z redex)) z))
    ; the rule functions stay closed: with them open the preprocessing does
    ; not end (125 s, interrupted)
    :hints (("Goal" :in-theory (e/d (apply-rule sym-member) ,*step-rules*)
                    :do-not-induct t))))

; the state rules that the fast machine applies to the store without bytes
(defun frame-safe-state-rules (rules)
  (declare (xargs :mode :program))
  (cond ((endp rules) nil)
        ((member-eq (car rules) *frame-safe-rules*)
         (cons (car rules) (frame-safe-state-rules (cdr rules))))
        (t (frame-safe-state-rules (cdr rules)))))

(make-event `(defconst *frame-safe-state-rules* ',(frame-safe-state-rules *state-rules*)))

(defthm frame-safe-state-rule-is-one-of-them
  (implies (and (frame-safe-p fn) (sym-member fn *state-rules*))
           (sym-member fn *frame-safe-state-rules*))
  :hints (("Goal" :in-theory (enable frame-safe-p sym-member)))
  :rule-classes nil)

(defthm store-fields-p-of-put-field-other
  (implies (and (store-fields-p s) (assoc-equal k (cdr s)))
           (store-fields-p (wrt::%put-field s k v))))

(defthm mems-of-put-field-other
  (implies (and (store-fields-p s) (not (equal k :mems)))
           (equal (wrt::%get-field (wrt::%put-field s k v) :mems)
                  (wrt::%get-field s :mems))))

(defthm mem0-record-p-of-put-field-other
  (implies (and (store-fields-p s) (not (equal k :mems)) (mem0-record-p s))
           (mem0-record-p (wrt::%put-field s k v)))
  :hints (("Goal" :in-theory (e/d (mem0-record-p)
                                  (wrt::%put-field wrt::%get-field store-fields-p)))))

(defthm fast-inv-store-of-put-field-other
  (implies (and (fast-inv-store s) (not (equal k :mems)) (assoc-equal k (cdr s)))
           (fast-inv-store (wrt::%put-field s k v)))
  :hints (("Goal" :in-theory (e/d (fast-inv-store fast-store-ok)
                                  (put-mem0-bytes wrt::%put-field wrt::%get-field
                                   store-fields-p mem0-record-p)))))

(defthm fast-inv-store-gives-fields
  (implies (fast-inv-store s)
           (and (assoc-equal :tags (cdr s)) (assoc-equal :globals (cdr s))
                (assoc-equal :tables (cdr s)) (assoc-equal :funcs (cdr s))
                (assoc-equal :datas (cdr s)) (assoc-equal :elems (cdr s))
                (assoc-equal :structs (cdr s)) (assoc-equal :arrays (cdr s))
                (assoc-equal :exns (cdr s))))
  :hints (("Goal" :in-theory (enable fast-inv-store fast-store-ok store-fields-p))))

; Generated, one lemma per frame-safe state rule: the store of its result is
; a fast store. The functions that expand a type stay closed (with them open
; STEP/R-THROW passed 2,000,000 prover steps).
(defun keeps-inv-store-name (fn)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name fn) "-KEEPS-INV-STORE") 'we::here))

(defun keeps-inv-store-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (with-prover-step-limit
           1000000
           (defthm ,(keeps-inv-store-name fn)
             (implies (and (fast-inv-store s)
                           (consp (,fn (list :|%;%| (list :|%;%| s f) l))))
                      (fast-inv-store
                       (cadr (cadr (car (,fn (list :|%;%| (list :|%;%| s f) l)))))))
             :hints (("Goal" :in-theory (e/d (,fn nth update-nth)
                                             (put-mem0-bytes wrt::%put-field wrt::%get-field
                                              store-fields-p mem0-record-p
                                              w3t::expand w3t::$unrolldt w3t::$as_deftype
                                              w3t::$unrollrt w3t::deftype-p w3t::rectype-p))
                             :do-not-induct t))))
          (value-triple (cw "INV-FAILED ~x0~%" ',fn)))))

(defun keeps-inv-store-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (list* `(value-triple (cw "INV-LEMMA ~x0~%" ',(car fns)))
           (keeps-inv-store-lemma (car fns))
           (keeps-inv-store-lemmas (cdr fns)))))

(make-event `(progn ,@(keeps-inv-store-lemmas *frame-safe-state-rules*)))

(defun keeps-inv-store-missing (fns wrld)
  (declare (xargs :mode :program))
  (cond ((endp fns) nil)
        ((getpropc (keeps-inv-store-name (car fns)) 'acl2::theorem nil wrld)
         (keeps-inv-store-missing (cdr fns) wrld))
        (t (cons (car fns) (keeps-inv-store-missing (cdr fns) wrld)))))

; the census: no frame-safe state rule is without its lemma
(make-event
 (let ((missing (keeps-inv-store-missing *frame-safe-state-rules* (w state))))
   (if missing
       (er soft 'inv "No -KEEPS-INV-STORE lemma for ~x0." missing)
     (value '(value-triple :all-keeps-inv-store-lemmas-proved)))))

(make-event
 `(defthm apply-rule-of-frame-safe-state-rule-keeps-inv-store
    (implies (and (sym-member fn *frame-safe-state-rules*)
                  (fast-inv-store s)
                  (mv-nth 0 (apply-rule fn (list :|%;%| s f) redex)))
             (fast-inv-store (cadr (mv-nth 1 (apply-rule fn (list :|%;%| s f) redex)))))
    :hints (("Goal" :in-theory (e/d (mv-nth sym-member) ,*frame-safe-state-rules*)
                    :do-not-induct t))))

(defthm apply-rule-of-frame-safe-rule-keeps-inv-store
  (implies (and (frame-safe-p fn)
                (fast-inv-store s)
                (mv-nth 0 (apply-rule fn (list :|%;%| s f) redex)))
           (fast-inv-store (cadr (mv-nth 1 (apply-rule fn (list :|%;%| s f) redex)))))
  :hints (("Goal" :use frame-safe-state-rule-is-one-of-them
                  :in-theory (disable (:e sym-member))
                  :do-not-induct t)))

; the four store rules of the fast path: the store is the one they were given
(defun store-rule-keeps-inv-store-name (fn)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (concatenate 'string "FAST-APPLY-RULE-OF-" (symbol-name fn) "-KEEPS-INV-STORE") 'we::here))

(defun store-rule-keeps-inv-store-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (with-prover-step-limit
           2000000
           (defthm ,(store-rule-keeps-inv-store-name fn)
             (implies (and (fast-inv-store s)
                           (mv-nth 0 (fast-apply-rule ',fn (list :|%;%| s f) redex fm))
                           (not (equal (mv-nth 0 (fast-apply-rule ',fn (list :|%;%| s f) redex fm))
                                       :refuse)))
                      (fast-inv-store
                       (cadr (mv-nth 1 (fast-apply-rule ',fn (list :|%;%| s f) redex fm)))))
             :hints (("Goal" :in-theory (e/d (fast-apply-rule fast-memory-rule ,(fast-name fn) mv-nth nth update-nth
                                              (:e sym-member))
                                             (one-memory-p
                                              ; the bytes written stay abstract
                                              wrt::$nbytes_ wrt::$ibytes_ wrt::$fbytes_
                                              wrt::%le-bytes wrt::%get-field))
                             :do-not-induct t))))
          (value-triple (cw "INV-FAILED ~x0~%" ',fn)))))

(defun store-rule-keeps-inv-store-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (list* `(value-triple (cw "INV-LEMMA ~x0~%" ',(car fns)))
           (store-rule-keeps-inv-store-lemma (car fns))
           (store-rule-keeps-inv-store-lemmas (cdr fns)))))

(make-event `(progn ,@(store-rule-keeps-inv-store-lemmas *fast-memory-step-rules*)))

(defun store-rule-keeps-inv-store-missing (fns wrld)
  (declare (xargs :mode :program))
  (cond ((endp fns) nil)
        ((getpropc (store-rule-keeps-inv-store-name (car fns)) 'acl2::theorem nil wrld)
         (store-rule-keeps-inv-store-missing (cdr fns) wrld))
        (t (cons (car fns) (store-rule-keeps-inv-store-missing (cdr fns) wrld)))))

(make-event
 (let ((missing (store-rule-keeps-inv-store-missing *fast-memory-step-rules* (w state))))
   (if missing
       (er soft 'inv "No store rule lemma for ~x0." missing)
     (value '(value-triple :all-store-rule-lemmas-proved)))))

(defthm fast-apply-rule-of-store-rule-keeps-inv-store
  (implies (and (sym-member fn *fast-memory-step-rules*)
                (fast-inv-store s)
                (mv-nth 0 (fast-apply-rule fn (list :|%;%| s f) redex fm))
                (not (equal (mv-nth 0 (fast-apply-rule fn (list :|%;%| s f) redex fm)) :refuse)))
           (fast-inv-store (cadr (mv-nth 1 (fast-apply-rule fn (list :|%;%| s f) redex fm)))))
  :hints (("Goal" :in-theory (enable sym-member) :do-not-induct t)))

; every other rule: a memory rule that reads (the state it was given, or the
; fallback), a frame-safe rule, or the fallback
(defthm fast-apply-rule-of-other-rule-keeps-inv-store
  (implies (and (not (sym-member fn *fast-memory-step-rules*))
                (fast-inv-store s)
                (mv-nth 0 (fast-apply-rule fn (list :|%;%| s f) redex fm))
                (not (equal (mv-nth 0 (fast-apply-rule fn (list :|%;%| s f) redex fm)) :refuse)))
           (fast-inv-store (cadr (mv-nth 1 (fast-apply-rule fn (list :|%;%| s f) redex fm)))))
  :hints (("Goal" :in-theory (e/d (fast-apply-rule) ((:e sym-member)))
                  :do-not-induct t)))

(defthm fast-apply-rule-keeps-inv-store
  (implies (and (fast-inv-store s)
                (mv-nth 0 (fast-apply-rule fn (list :|%;%| s f) redex fm))
                (not (equal (mv-nth 0 (fast-apply-rule fn (list :|%;%| s f) redex fm)) :refuse)))
           (fast-inv-store (cadr (mv-nth 1 (fast-apply-rule fn (list :|%;%| s f) redex fm)))))
  :hints (("Goal" :cases ((sym-member fn *fast-memory-step-rules*))
                  :do-not-induct t)))

(defthm fast-try-rules-keeps-inv-store
  (implies (and (fast-inv-store s)
                (mv-nth 0 (fast-try-rules rules (list :|%;%| s f) redex fm))
                (not (equal (mv-nth 0 (fast-try-rules rules (list :|%;%| s f) redex fm)) :refuse)))
           (fast-inv-store (cadr (mv-nth 1 (fast-try-rules rules (list :|%;%| s f) redex fm)))))
  :hints (("Goal" :induct (fast-try-rules rules (list :|%;%| s f) redex fm)
                  :in-theory (enable fast-try-rules))))

; ---------------------------------------------------------------------------
; 3. The parts of a step keep FMP and the fast store

(defthm fast-enter-step-keeps-fmp
  (implies (fmp fm)
           (fmp (fast-enter-step fm)))
  :hints (("Goal" :in-theory (e/d (fast-enter-step) (enterable-p admin-kind)))))

(defthm fast-enter-step-keeps-inv-store
  (implies (fast-inv-store (fm-store fm))
           (fast-inv-store (nth *fm-store* (fast-enter-step fm))))
  :hints (("Goal" :in-theory (e/d (fast-enter-step) (enterable-p admin-kind)))))

(defthm fast-op-step-keeps-fmp
  (implies (and (fmp fm)
                (not (equal (entry-kind (car (fm-is fm))) :call_ref)))
           (fmp (fast-op-step fm)))
  :hints (("Goal" :in-theory (e/d (fast-op-step) (fast-try-op op-has-rules rules-for))
                  :do-not-induct t)))

(defthm fast-op-step-keeps-inv-store
  (implies (and (fast-inv-store (fm-store fm))
                (not (equal (entry-kind (car (fm-is fm))) :call_ref)))
           (fast-inv-store (nth *fm-store* (fast-op-step fm))))
  :hints (("Goal" :in-theory (e/d (fast-op-step) (fast-try-op op-has-rules rules-for))
                  :do-not-induct t)))

(defthm fast-exit-step-keeps-fmp
  (implies (and (fmp fm)
                (sym-member (entry-kind (car (fm-ctrl fm))) '(:l :h :f)))
           (fmp (fast-exit-step fm)))
  :hints (("Goal" :in-theory (e/d (fast-exit-step) (fast-try-entry rules-for))
                  :do-not-induct t)))

(defthm fast-exit-step-keeps-inv-store
  (implies (and (fast-inv-store (fm-store fm))
                (sym-member (entry-kind (car (fm-ctrl fm))) '(:l :h :f)))
           (fast-inv-store (nth *fm-store* (fast-exit-step fm))))
  :hints (("Goal" :in-theory (e/d (fast-exit-step) (fast-try-entry rules-for))
                  :do-not-induct t)))

(defthm fast-anyprefix-step-keeps-fmp
  (implies (fmp fm)
           (fmp (fast-anyprefix-step fm)))
  :hints (("Goal" :in-theory (e/d (fast-anyprefix-step) (fast-try-anyprefix rules-for (:e rules-for)))
                  :do-not-induct t)))

(defthm fast-anyprefix-step-keeps-inv-store
  (implies (fast-inv-store (fm-store fm))
           (fast-inv-store (nth *fm-store* (fast-anyprefix-step fm))))
  :hints (("Goal" :in-theory (e/d (fast-anyprefix-step) (fast-try-anyprefix rules-for (:e rules-for)))
                  :do-not-induct t)))

; the fast paths, with MV-NTH (HOT-STEP-IS-OP-STEP and
; HOT-STEP-DECLINED-KEEPS-FM of refine-op.lisp)
(defthm fast-hot-step-when-handled
  (implies (and (fmp fm) (equal (fm-status fm) :run) (consp (fm-is fm))
                (sym-member (car (car (fm-is fm)))
                            '(:local.get :local.set :local.tee :binop :relop :br_if))
                (mv-nth 0 (fast-hot-step (car (nth *fm-is* fm)) fm)))
           (equal (mv-nth 1 (fast-hot-step (car (nth *fm-is* fm)) fm))
                  (fast-op-step fm)))
  :hints (("Goal" :use hot-step-is-op-step
                  :in-theory (e/d (mv-nth mv-nth-1-2-3 sym-member) (hot-step-is-op-step)))))

(defthm fast-hot-step-when-declined
  (implies (not (mv-nth 0 (fast-hot-step i fm)))
           (equal (mv-nth 1 (fast-hot-step i fm)) fm))
  :hints (("Goal" :use hot-step-declined-keeps-fm
                  :in-theory (e/d (mv-nth mv-nth-1-2-3) (hot-step-declined-keeps-fm)))))

; a hot instruction is not call_ref
(defthm entry-kind-when-hot
  (implies (sym-member (car i) '(:local.get :local.set :local.tee :binop :relop :br_if))
           (not (equal (entry-kind i) :call_ref)))
  :hints (("Goal" :in-theory (enable entry-kind sym-member))))

(defthm fast-step-keeps-fmp
  (implies (and (fmp fm)
                (ctrl-kinds-ok (fm-ctrl fm))
                (not (equal (entry-kind (car (fm-is fm))) :call_ref)))
           (fmp (fast-step fm)))
  :hints (("Goal" :in-theory (e/d (fast-step) (fast-val-p exit-instr-p admin-kind ctrl-kinds-ok
                                               (:e sym-member)))
                  :do-not-induct t)))

(defthm fast-step-keeps-inv-store
  (implies (and (fmp fm)
                (fast-inv-store (fm-store fm))
                (ctrl-kinds-ok (fm-ctrl fm))
                (not (equal (entry-kind (car (fm-is fm))) :call_ref)))
           (fast-inv-store (nth *fm-store* (fast-step fm))))
  :hints (("Goal" :in-theory (e/d (fast-step) (fast-val-p exit-instr-p admin-kind ctrl-kinds-ok
                                               (:e sym-member)))
                  :do-not-induct t)))

; ---------------------------------------------------------------------------
; 4. The invariant, and a step

(defun fm-inv (fm)
  (declare (xargs :stobjs fm))
  (and (fmp fm)
       (fast-inv-store (fm-store fm))
       (machine-ok (fm->ms fm))))

(defthm ctrl-kinds-ok-when-machine-ok-of-fm->ms
  (implies (machine-ok (fm->ms fm))
           (ctrl-kinds-ok (nth *fm-ctrl* fm)))
  :hints (("Goal" :use ((:instance ctrl-kinds-ok-of-ms-ctrl-when-machine-ok (s (fm->ms fm))))
                  :in-theory (disable ctrl-kinds-ok-of-ms-ctrl-when-machine-ok))))

(defthm fast-step-when-not-running
  (implies (not (equal (fm-status fm) :run))
           (equal (fast-step fm) fm))
  :hints (("Goal" :in-theory (enable fast-step))))

(defthm machine-ok-of-fast-step
  (implies (and (fm-inv fm)
                (not (equal (entry-kind (car (fm-is fm))) :call_ref))
                (not (equal (fm-status (fast-step fm)) :unsupported)))
           (machine-ok (fm->ms (fast-step fm))))
  :hints (("Goal" :cases ((equal (fm-status fm) :run))
                  :in-theory (enable fast-step-refines machine-running)
                  :do-not-induct t)))

(defthm fast-step-keeps-fm-inv
  (implies (and (fm-inv fm)
                (not (equal (entry-kind (car (fm-is fm))) :call_ref))
                (not (equal (fm-status (fast-step fm)) :unsupported)))
           (fm-inv (fast-step fm)))
  :hints (("Goal" :use machine-ok-of-fast-step
                  :in-theory (disable machine-ok-of-fast-step)
                  :do-not-induct t)))

; FAST-STEP-REFINES of refine-op.lisp, from the invariant
(defthm fm->ms-of-fast-step
  (implies (and (fm-inv fm)
                (not (equal (entry-kind (car (fm-is fm))) :call_ref))
                (not (equal (fm-status (fast-step fm)) :unsupported)))
           (equal (fm->ms (fast-step fm))
                  (machine-step (fm->ms fm))))
  :hints (("Goal" :in-theory (enable fast-step-refines)
                  :do-not-induct t)))

; ---------------------------------------------------------------------------
; 5. The run

; every status but :run is absorbing
(defthm fast-run-when-not-running
  (implies (not (equal (fm-status fm) :run))
           (equal (fast-run n fm) fm)))

; the run takes no step that ends :unsupported
(defun-nx fast-run-supported (n fm)
  (declare (xargs :measure (nfix n)))
  (or (zp n)
      (not (equal (fm-status fm) :run))
      (and (not (equal (fm-status (fast-step fm)) :unsupported))
           (fast-run-supported (1- n) (fast-step fm)))))

(defthm fast-run-supported-when-not-unsupported
  (implies (not (equal (fm-status (fast-run n fm)) :unsupported))
           (fast-run-supported n fm))
  :hints (("Goal" :induct (fast-run n fm))))

; the hypothesis that V7 removes: the list machine's run of N steps has no
; call_ref at the head of its instructions
(defun no-call-ref-run (n s)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (or (zp n)
      (not (machine-running s))
      (and (not (equal (entry-kind (car-t (ms-is s))) :call_ref))
           (no-call-ref-run (1- n) (machine-step s)))))

(defthm no-call-ref-run-when-running
  (implies (and (not (zp n)) (machine-running s))
           (equal (no-call-ref-run n s)
                  (and (not (equal (entry-kind (car-t (ms-is s))) :call_ref))
                       (no-call-ref-run (1- n) (machine-step s))))))

(defthm machine-run-when-running
  (implies (and (not (zp n)) (machine-running s))
           (equal (machine-run n s)
                  (machine-run (1- n) (machine-step s)))))

(defthm fast-run-is-machine-run-when-supported
  (implies (and (fm-inv fm)
                (no-call-ref-run n (fm->ms fm))
                (fast-run-supported n fm))
           (and (equal (fm->ms (fast-run n fm))
                       (machine-run n (fm->ms fm)))
                (fm-inv (fast-run n fm))))
  :hints (("Goal" :induct (fast-run n fm)
                  :in-theory (e/d (machine-running) (fm-inv)))))

(defthm fast-run-is-machine-run
  (implies (and (fm-inv fm)
                (no-call-ref-run n (fm->ms fm))
                (not (equal (fm-status (fast-run n fm)) :unsupported)))
           (equal (fm->ms (fast-run n fm))
                  (machine-run n (fm->ms fm)))))

(defthm fast-run-keeps-fm-inv
  (implies (and (fm-inv fm)
                (no-call-ref-run n (fm->ms fm))
                (not (equal (fm-status (fast-run n fm)) :unsupported)))
           (fm-inv (fast-run n fm))))

; ---------------------------------------------------------------------------
; 6. The loader

; what FM-LOAD-MS can load: a list state with the invariant whose store has
; all its fields and a memory 0 that is a record with a byte list. A store
; with no memory is not loadable (FAST-INV-STORE asks for a memory); a store
; with several is, and the memory rules then take the exact fallback.
(defun fm-loadable-p (s)
  (declare (xargs :guard t))
  (and (machine-ok s)
       (mem0-shape-ok (ms-store s))
       (ec-call (store-fields-p (ms-store s)))))

(defthm ms-of-its-fields
  (implies (and (true-listp s) (equal (len s) 6))
           (equal (ms (ms-store s) (ms-frame s) (ms-vals s) (ms-is s) (ms-ctrl s) (ms-status s))
                  s))
  :hints (("Goal" :in-theory (enable ms ms-store ms-frame ms-vals ms-is ms-ctrl ms-status drop-n))))

(defthm machine-ok-gives-shape
  (implies (machine-ok s)
           (and (true-listp s) (equal (len s) 6)))
  :hints (("Goal" :in-theory (enable machine-ok)))
  :rule-classes :forward-chaining)

(defthm fm->ms-of-fm-load-ms
  (implies (fm-loadable-p s)
           (equal (fm->ms (fm-load-ms s fm)) s))
  :hints (("Goal" :in-theory (e/d (fm->ms) (put-mem0-bytes mem0-shape-ok store-fields-p mem0-of-store))
                  :do-not-induct t)))

(defthm fm-inv-of-fm-load-ms
  (implies (and (fmp fm) (fm-loadable-p s))
           (fm-inv (fm-load-ms s fm)))
  :hints (("Goal" :use fm->ms-of-fm-load-ms
                  :in-theory (e/d () (fm->ms-of-fm-load-ms put-mem0-bytes mem0-shape-ok
                                      store-fields-p mem0-of-store))
                  :do-not-induct t)))

; A configuration ((s; f); instrs) that the engine can load.
(defun config-shape-p (c)
  (declare (xargs :guard t))
  (and (true-listp c) (equal (len c) 3) (equal (car c) :|%;%|)
       (true-listp (cadr c)) (equal (len (cadr c)) 3) (equal (car (cadr c)) :|%;%|)
       (true-listp (caddr c))
       (mem0-shape-ok (cadr (cadr c)))
       (ec-call (store-fields-p (cadr (cadr c))))))

(defthm machine-ok-of-ms-of-config
  (implies (config-shape-p c)
           (machine-ok (ms-of-config c)))
  :hints (("Goal" :in-theory (enable val-list-p ctrl-ok status-ok))))

(defthm machine-abs-of-ms-of-config
  (implies (config-shape-p c)
           (equal (machine-abs (ms-of-config c)) c))
  :hints (("Goal" :in-theory (enable machine-abs abs-ctrl rev-onto mv-nth))))

(defthm fm-loadable-p-of-ms-of-config
  (implies (config-shape-p c)
           (fm-loadable-p (ms-of-config c)))
  :hints (("Goal" :use machine-ok-of-ms-of-config
                  :in-theory (disable machine-ok-of-ms-of-config mem0-shape-ok store-fields-p))))

(in-theory (disable fm-inv fm-loadable-p config-shape-p no-call-ref-run fast-run-supported
                    ms-of-config fm-load-ms fast-run))
