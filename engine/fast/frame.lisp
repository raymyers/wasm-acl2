; E7, part 3 of the design in notes/E6-list-machine.md: every rule
; function that does not touch memory ignores memory 0's byte list. The
; stobj machine keeps the bytes in an array and gives these rules a store
; with no bytes; this book is the fact that makes that equal to the list
; machine. One lemma per rule function, generated from the relation bodies
; and tried with (:or ...); a rule whose lemma does not prove prints
; FRAME-FAILED in the certification output.
(in-package "WE")
(include-book "../machine/machine")

; --- records (the spec's %GET-FIELD / %PUT-FIELD are alist operations) ---

(defthm assoc-of-put-assoc
  (equal (assoc-equal k (put-assoc-equal k2 v al))
         (if (equal k k2) (cons k v) (assoc-equal k al))))

(defthm put-assoc-of-put-assoc-same
  (equal (put-assoc-equal k v2 (put-assoc-equal k v1 al)) (put-assoc-equal k v2 al)))

(defthm alistp-put-assoc
  (implies (alistp al) (alistp (put-assoc-equal k v al))))

(defthm put-assoc-of-assoc-same
  (implies (and (alistp al) (assoc-equal k al))
           (equal (put-assoc-equal k (cdr (assoc-equal k al)) al) al)))

(defthm assoc-present-when-value-consp
  (implies (consp (cdr (assoc-equal k al))) (assoc-equal k al))
  :rule-classes :forward-chaining)

(defthm put-assoc-commute
  (implies (and (not (equal k1 k2)) (alistp al) (assoc-equal k1 al) (assoc-equal k2 al))
           (equal (put-assoc-equal k1 v1 (put-assoc-equal k2 v2 al))
                  (put-assoc-equal k2 v2 (put-assoc-equal k1 v1 al)))))

(defthm put-assoc-same-value-over-other-key
  (implies (and (alistp al) (assoc-equal k al) (not (equal k k2)))
           (equal (put-assoc-equal k (cdr (assoc-equal k al)) (put-assoc-equal k2 v al))
                  (put-assoc-equal k2 v al))))

; A store record has all its fields. (Stores made by $instantiate do; the
; stobj machine keeps this as part of its invariant.)
(defun store-fields-p (s)
  (and (consp s) (alistp (cdr s))
       (assoc-equal :tags (cdr s)) (assoc-equal :globals (cdr s)) (assoc-equal :mems (cdr s))
       (assoc-equal :tables (cdr s)) (assoc-equal :funcs (cdr s)) (assoc-equal :datas (cdr s))
       (assoc-equal :elems (cdr s)) (assoc-equal :structs (cdr s)) (assoc-equal :arrays (cdr s))
       (assoc-equal :exns (cdr s)) t))

; --- the store with memory 0's bytes replaced -------------------------------

(defun put-mem0-bytes (s b)
  (let ((mems (wrt::%get-field s :mems)))
    (if (consp mems)
        (wrt::%put-field s :mems (cons (wrt::%put-field (car mems) :bytes b) (cdr mems)))
      s)))

(defun put-z-bytes (z b)                ; z = (:|%;%| store frame)
  (list :|%;%| (put-mem0-bytes (cadr z) b) (caddr z)))

(defun put-result-bytes (r b)           ; a step rule's result: (list config)
  (if (consp r)
      (list (list :|%;%| (put-z-bytes (cadr (car r)) b) (caddr (car r))))
    r))

; --- the generated lemmas ----------------------------------------------------

(defun memory-rule-p (fn)                ; the rules that read or write the bytes
  (declare (xargs :mode :program))
  (let ((id (rule-id fn)))
    (or (search "LOAD" id) (search "STORE" id) (search "MEMORY." id))))

(defun frame-lemma (fn kind)
  (declare (xargs :mode :program))
  (let ((name (intern-in-package-of-symbol
               (concatenate 'string (symbol-name fn) "-IGNORES-BYTES") 'we::here)))
    `(make-event
      '(:or (defthm ,name
              ,(if (eq kind :read)
                   `(equal (,fn (list :|%;%| (put-z-bytes z b) l))
                           (,fn (list :|%;%| (put-z-bytes z nil) l)))
                 `(implies (and (consp (wrt::%get-field (cadr z) :mems)) (true-listp z) (equal (len z) 3)
                                (store-fields-p (cadr z)))
                           (equal (,fn (list :|%;%| (put-z-bytes z b) l))
                                  (put-result-bytes (,fn (list :|%;%| (put-z-bytes z nil) l)) b))))
              :hints (("Goal" :in-theory (enable ,fn) :do-not-induct t)))
            (value-triple (cw "FRAME-FAILED ~x0~%" ',fn))))))

; Rules whose frame lemma does not prove with this library: they read a
; type or a function through the store (casts, ref.test, return_call_ref)
; or call the host (H). Left out here, so that the book stays fast; the two
; host-call rules are needed for group H.
(defconst *frame-not-yet*
  '(w3t::step_read/split/r-br_on_cast-succeed w3t::step_read/split/r-br_on_cast_fail-succeed
    w3t::step_read/split/r-return_call_ref-frame-addr w3t::step_read/split/r-ref.test-true
    w3t::step_read/split/r-ref.cast-succeed w3t::step/r-call_ref-hostfunc-res
    w3t::step/r-call_ref-hostfunc-div))

; The opcodes of D5 (E1 census): only their rules, and the rules of the
; control entries, get a frame lemma here. Rules outside D5 (GC, tables,
; segments) are not needed by the engine; table.grow alone took 1,152 s.
(defconst *d5-opcodes*
  '(:unreachable :nop :drop :select :ifelse :block :loop :br :br_if :br_table :return
    :call :call_indirect :call_ref :local.get :local.set :local.tee :global.get :global.set
    :load :store :memory.size :memory.grow :memory.copy :memory.fill
    :unop :binop :testop :relop :cvtop :try_table :throw :throw_ref :table.get :ref.cast))

(defun d5-rule-p (fn)
  (declare (xargs :mode :program))
  (let ((place (rule-place fn)))
    (or (not (and (consp place) (eq (car place) :op)))
        (member-eq (cadr place) *d5-opcodes*))))

(defun frame-lemmas (rules)
  (declare (xargs :mode :program))
  (cond ((endp rules) nil)
        ((or (eq (rule-kind (car rules)) :pure) (memory-rule-p (car rules))
             (member-eq (car rules) *frame-not-yet*) (not (d5-rule-p (car rules))))
         (frame-lemmas (cdr rules)))
        (t (cons (frame-lemma (car rules) (rule-kind (car rules))) (frame-lemmas (cdr rules))))))

(make-event `(progn ,@(frame-lemmas *step-rules*)))
