; E7 Phase B: the fast machine refines the list machine.
; Built bottom-up: (1) the array as a list; (2) per rule, the direct call
; in the generated dispatch agrees with APPLY-RULE on the full store; (3)
; per place; (4) per step part. This book: (1) and (2) for the rules that
; ignore the bytes (pure rules and the frame lemmas of frame.lisp).
(in-package "WE")
(include-book "fast")

; --- (1) the array as a list ----------------------------------------------

(defthm mem-to-list-loop-is-take
  (implies (and (natp i) (<= i (len (nth *fm-memi* fm))) (true-listp acc))
           (equal (mem-to-list-loop i fm acc)
                  (append (take i (nth *fm-memi* fm)) acc)))
  :hints (("Goal" :induct (mem-to-list-loop i fm acc))))

(defthm take-of-len
  (implies (true-listp l) (equal (take (len l) l) l)))

(defthm mem-to-list-is-the-field
  (implies (true-listp (nth *fm-memi* fm))
           (equal (mem-to-list fm) (nth *fm-memi* fm))))

; --- the store of the fast machine -------------------------------------------

; The fast machine's store has an empty byte list for memory 0, a memory,
; and all its fields (the hypotheses of the frame lemmas).
(defun fast-store-ok (s)
  (and (equal (put-mem0-bytes s nil) s)
       (consp (wrt::%get-field s :mems))
       (store-fields-p s)))

(defthm put-z-bytes-nil-of-ok
  (implies (fast-store-ok (cadr z))
           (equal (put-z-bytes (list :|%;%| (cadr z) (caddr z)) nil)
                  (list :|%;%| (cadr z) (caddr z)))))

; --- (2) per rule: the frame-safe rules -----------------------------------------
; For a frame-safe rule R, with the fast store OK:
;   read rule: R on the full store = R on the fast store;
;   step rule: R on the full store = R on the fast store, bytes put back;
;              and R's resulting store is OK again.

(defun frame-use-lemma (fn kind)
  (declare (xargs :mode :program))
  (let* ((pkg 'we::here)
         (frame (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-IGNORES-BYTES") pkg))
         (name (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-ON-FAST-STORE") pkg))
         (zz '(list :|%;%| s f)))
    (if (eq kind :read)
        `(defthm ,name
           (implies (fast-store-ok s)
                    (equal (,fn (list :|%;%| (list :|%;%| (put-mem0-bytes s b) f) l))
                           (,fn (list :|%;%| ,zz l))))
           :hints (("Goal" :use ((:instance ,frame (z ,zz)))
                           :in-theory (disable ,frame ,fn))))
      `(defthm ,name
         (implies (fast-store-ok s)
                  (equal (,fn (list :|%;%| (list :|%;%| (put-mem0-bytes s b) f) l))
                         (put-result-bytes (,fn (list :|%;%| ,zz l)) b)))
         :hints (("Goal" :use ((:instance ,frame (z ,zz)))
                         :in-theory (disable ,frame ,fn)))))))

(defun frame-use-lemmas (rules)
  (declare (xargs :mode :program))
  (cond ((endp rules) nil)
        ((eq (rule-kind (car rules)) :pure) (frame-use-lemmas (cdr rules)))
        (t (cons `(make-event
                   '(:or ,(frame-use-lemma (car rules) (rule-kind (car rules)))
                         (value-triple (cw "REFINE-FAILED ~x0~%" ',(car rules)))))
                 (frame-use-lemmas (cdr rules))))))

(make-event `(progn ,@(frame-use-lemmas *frame-safe-rules*)))

; --- records at the level of %GET-FIELD / %PUT-FIELD -------------------------

(defthm get-field-of-put-field
  (implies (and (consp r) (alistp (cdr r)))
           (equal (wrt::%get-field (wrt::%put-field r k v) k2)
                  (if (equal k k2) v (wrt::%get-field r k2)))))

(defthm consp-put-field
  (implies (and (consp r) (alistp (cdr r)))
           (and (consp (wrt::%put-field r k v)) (alistp (cdr (wrt::%put-field r k v))))))

(defthm assoc-of-put-field
  (implies (and (consp r) (alistp (cdr r)) (assoc-equal k2 (cdr r)))
           (assoc-equal k2 (cdr (wrt::%put-field r k v)))))

(defthm store-fields-p-of-put-field
  (implies (and (store-fields-p s) (assoc-equal k (cdr s)))
           (store-fields-p (wrt::%put-field s k v))))

(defthm put-mem0-bytes-of-put-field-other
  (implies (and (store-fields-p s) (not (equal k :mems)) (assoc-equal k (cdr s)))
           (equal (put-mem0-bytes (wrt::%put-field s k v) b)
                  (wrt::%put-field (put-mem0-bytes s b) k v))))

; A frame-safe step rule leaves the fast store OK.
(defun store-ok-lemma (fn)
  (declare (xargs :mode :program))
  (let ((name (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-KEEPS-FAST-STORE") 'we::here)))
    `(make-event
      '(:or (defthm ,name
              (implies (and (fast-store-ok s) (consp (,fn (list :|%;%| (list :|%;%| s f) l))))
                       (fast-store-ok (car-t (drop-n 1 (car-t (drop-n 1 (car (,fn (list :|%;%| (list :|%;%| s f) l)))))))))
              :hints (("Goal" :in-theory (e/d (,fn) (put-mem0-bytes wrt::%put-field)) :do-not-induct t)))
            (value-triple (cw "REFINE-FAILED ~x0~%" ',fn))))))

(defun store-ok-lemmas (rules)
  (declare (xargs :mode :program))
  (cond ((endp rules) nil)
        ((eq (rule-kind (car rules)) :step) (cons (store-ok-lemma (car rules)) (store-ok-lemmas (cdr rules))))
        (t (store-ok-lemmas (cdr rules)))))

(make-event `(progn ,@(store-ok-lemmas *frame-safe-rules*)))
