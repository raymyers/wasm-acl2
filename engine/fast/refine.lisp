; E7 Phase B: the fast machine refines the list machine.
; Built bottom-up: (1) the array as a list; (2) per rule, the direct call
; in the generated dispatch agrees with APPLY-RULE on the full store; (3)
; per place; (4) per step part. Done: (1); (2) and (3) for the rules that
; ignore the bytes (pure rules and the frame lemmas of frame.lisp): 60 of
; the 103 places of the generated dispatch.
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

; --- (3) per place, for the places whose rules are all frame-safe ---------------

; APPLY-RULE on a constant rule name is a direct call of that rule.
(defun apply-rule-lemma (fn)
  (declare (xargs :mode :program))
  (let ((name (intern-in-package-of-symbol (concatenate 'string "APPLY-RULE-OF-" (symbol-name fn)) 'we::here)))
    `(defthm ,name
       (equal (apply-rule ',fn z redex)
              ,(case (rule-kind fn)
                 (:pure `(let ((r (,fn redex))) (if (consp r) (mv t z (car r)) (mv nil z nil))))
                 (:read `(let ((r (,fn (list :|%;%| z redex)))) (if (consp r) (mv t z (car r)) (mv nil z nil))))
                 (t `(let ((r (,fn (list :|%;%| z redex))))
                       (if (consp r) (mv t (car-t (drop-n 1 (car r))) (car-t (drop-n 2 (car r))))
                         (mv nil z nil))))))
       :hints (("Goal" :in-theory (e/d (apply-rule) (,fn)))))))

(defun apply-rule-lemmas (rules)
  (declare (xargs :mode :program))
  (if (endp rules) nil (cons (apply-rule-lemma (car rules)) (apply-rule-lemmas (cdr rules)))))

(make-event `(progn ,@(apply-rule-lemmas *step-rules*)))

(defthm car-t-drop-n-1-of-put-result-bytes
  (implies (consp r)
           (and (equal (car-t (drop-n 1 (car (put-result-bytes r b))))
                       (put-z-bytes (car-t (drop-n 1 (car r))) b))
                (equal (car-t (drop-n 2 (car (put-result-bytes r b))))
                       (car-t (drop-n 2 (car r))))
                (consp (put-result-bytes r b))))
  :hints (("Goal" :in-theory (enable put-result-bytes car-t drop-n))))

(defthm consp-of-put-result-bytes
  (equal (consp (put-result-bytes r b)) (consp r))
  :hints (("Goal" :in-theory (enable put-result-bytes))))

(defthm put-z-bytes-of-config
  (equal (put-z-bytes (list :|%;%| s f) b) (list :|%;%| (put-mem0-bytes s b) f)))

(defun all-frame-safe-p (rules)
  (declare (xargs :mode :program))
  (or (endp rules) (and (member-eq (car rules) *frame-safe-rules*) (all-frame-safe-p (cdr rules)))))

(defun place-lemma (place rules)
  (declare (xargs :mode :program))
  (let* ((fast (place-fn-name place))
         (name (intern-in-package-of-symbol (concatenate 'string (symbol-name fast) "-REFINES") 'we::here))
         (fm-name (intern-in-package-of-symbol (concatenate 'string (symbol-name fast) "-KEEPS-ARRAY") 'we::here)))
    `(make-event
      '(:or (progn
              (defthm ,name
                (implies (fast-store-ok s)
                         (equal (try-rules ',rules (list :|%;%| (put-mem0-bytes s b) f) redex)
                                (mv-let (ok z2 res fm2) (,fast (list :|%;%| s f) redex fm)
                                  (declare (ignore fm2))
                                  (mv ok (put-z-bytes z2 b) res))))
                :hints (("Goal" :in-theory (e/d (,fast try-rules) (put-z-bytes put-result-bytes put-mem0-bytes
                                                                   ,@rules))
                                :do-not-induct t)))
              (defthm ,fm-name
                (equal (mv-nth 3 (,fast z redex fm)) fm)
                :hints (("Goal" :in-theory (e/d (,fast) ,rules)))))
            (value-triple (cw "REFINE-FAILED ~x0~%" ',place))))))

(defun place-lemmas (alist)
  (declare (xargs :mode :program))
  (cond ((endp alist) nil)
        ((all-frame-safe-p (cdar alist))
         (cons (place-lemma (caar alist) (cdar alist)) (place-lemmas (cdr alist))))
        (t (place-lemmas (cdr alist)))))

(make-event `(progn ,@(place-lemmas *rule-places*)))
