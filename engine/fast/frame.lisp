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
                 `(implies (and (consp (wrt::%get-field (cadr z) :mems)) (true-listp z) (equal (len z) 3))
                           (equal (,fn (list :|%;%| (put-z-bytes z b) l))
                                  (put-result-bytes (,fn (list :|%;%| (put-z-bytes z nil) l)) b))))
              :hints (("Goal" :in-theory (enable ,fn) :do-not-induct t)))
            (value-triple (cw "FRAME-FAILED ~x0~%" ',fn))))))

(defun frame-lemmas (rules)
  (declare (xargs :mode :program))
  (cond ((endp rules) nil)
        ((or (eq (rule-kind (car rules)) :pure) (memory-rule-p (car rules)))
         (frame-lemmas (cdr rules)))
        (t (cons (frame-lemma (car rules) (rule-kind (car rules))) (frame-lemmas (cdr rules))))))

(make-event `(progn ,@(frame-lemmas *step-rules*)))
