; License: MIT. See the file LICENSE at the top of the repository.
;
; E7 Phase B: the fast machine refines the list machine.
; Built bottom-up: (1) the array as a list; (2) per rule, the direct call
; in the generated dispatch agrees with APPLY-RULE on the full store; (3)
; per place; (4) per step part. Done: (1); (2) and (3) for the rules that
; ignore the bytes (pure rules and the frame lemmas of frame.lisp): 60 of
; the 103 places of the generated dispatch; (2') the general fallback, with
; its two per-rule facts for 87 of the 90 rules that use it.
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

; --- (2') per rule: the general fallback ---------------------------------------
; A rule with no fast path runs on the full store (the bytes copied from the
; array), and the array becomes the result's bytes. It agrees with the list
; machine when the result is a configuration whose memory 0 has a byte list
; (FALLBACK-RESULT-OK: a hypothesis per rule, discharged in layer 4).

(defthm byte-list-p-true-listp (implies (byte-list-p l) (true-listp l)) :rule-classes :forward-chaining)

(defthm take-of-update-nth-at
  (implies (natp i) (equal (take i (update-nth i v l)) (take i l))))

(defthm take-1+-of-update-nth
  (implies (and (natp i) (< i (len l)))
           (equal (append (take i l) (cons v rest))
                  (append (take (+ 1 i) (update-nth i v l)) rest))))

(defthm list-to-mem-loop-array
  (implies (and (natp i) (byte-list-p l) (true-listp (nth *fm-memi* fm))
                (equal (len (nth *fm-memi* fm)) (+ i (len l))))
           (equal (nth *fm-memi* (list-to-mem-loop l i fm))
                  (append (take i (nth *fm-memi* fm)) l)))
  :hints (("Goal" :induct (list-to-mem-loop l i fm) :in-theory (disable take))))

(defthm len-resize-list (equal (len (resize-list l n d)) (nfix n)))
(defthm true-listp-resize-list (true-listp (resize-list l n d)))
(defthm len-t-is-len (equal (len-t l) (len l)) :hints (("Goal" :in-theory (enable len-t))))

(defthm list-to-mem-array
  (implies (byte-list-p l) (equal (nth *fm-memi* (list-to-mem l fm)) l)))

(defthm list-to-mem-loop-other
  (implies (not (equal k *fm-memi*))
           (equal (nth k (list-to-mem-loop l i fm)) (nth k fm))))

(defthm list-to-mem-other
  (implies (not (equal k *fm-memi*))
           (equal (nth k (list-to-mem l fm)) (nth k fm))))

(defthm put-assoc-same-value
  (implies (and (alistp a) (assoc-equal k a))
           (equal (put-assoc-equal k (cdr (assoc-equal k a)) a) a)))

(defthm put-assoc-twice
  (equal (put-assoc-equal k v2 (put-assoc-equal k v1 a)) (put-assoc-equal k v2 a)))

(defthm put-mem0-bytes-roundtrip
  (implies (mem0-shape-ok s)
           (equal (put-mem0-bytes (put-mem0-bytes s nil) (mem0-of-store s)) s)))

(defthm byte-list-p-of-mem0-when-shape-ok
  (implies (mem0-shape-ok s) (byte-list-p (mem0-of-store s))))

(defun fallback-result-ok (fn z redex)
  (declare (xargs :guard t))
  (mv-let (ok z2 res) (apply-rule fn z redex)
    (declare (ignore res))
    (or (not ok) (fallback-shape-ok z2))))

(defthm car-t-drop-n-of-config
  (implies (and (true-listp z) (equal (len z) 3))
           (and (equal (car-t (drop-n 1 z)) (cadr z))
                (equal (car-t (drop-n 2 z)) (caddr z))))
  :hints (("Goal" :in-theory (enable car-t drop-n) :expand ((drop-n 1 z) (drop-n 2 z) (drop-n 1 (cdr z))))))

;; Two facts per rule, proved per rule below: it fails with the state
;; unchanged and no instructions, and it fires only on its opcode.
(defun rule-fails-plainly (fn z redex)
  (declare (xargs :guard t))
  (mv-let (ok z2 res) (apply-rule fn z redex)
    (if ok (equal ok t) (and (equal z2 z) (equal res nil)))))

(defun rule-needs-opcode (fn z redex)
  (declare (xargs :guard t))
  (mv-let (ok z2 res) (apply-rule fn z redex)
    (declare (ignore z2 res))
    (or (rule-may-match fn redex) (not ok))))

(defthm config-rebuild
  (implies (and (true-listp z) (equal (len z) 3) (equal (car z) :|%;%|))
           (equal (list :|%;%| (cadr z) (caddr z)) z)))

; The fallback, for any rule FN with no fast path.
(defthm fast-apply-rule-fallback
  (implies (and (not (sym-member fn *fast-memory-rules*)) (not (frame-safe-p fn))
                (fast-store-ok s) (byte-list-p (nth *fm-memi* fm))
                (fallback-result-ok fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex)
                (rule-fails-plainly fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex)
                (rule-needs-opcode fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))
           (let ((full (apply-rule fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))
                 (fast (fast-apply-rule fn (list :|%;%| s f) redex fm)))
             (and (equal (mv-nth 0 full) (mv-nth 0 fast))
                  (equal (mv-nth 1 full) (put-z-bytes (mv-nth 1 fast) (nth *fm-memi* (mv-nth 3 fast))))
                  (equal (mv-nth 2 full) (mv-nth 2 fast)))))
  :hints (("Goal" :in-theory (disable apply-rule put-mem0-bytes mem0-of-store mem0-shape-ok
                                      fast-store-ok frame-safe-p rule-may-match list-to-mem)
                  :do-not-induct t)))

(defthm head-in-p-of-nthcdr
  (implies (and (equal (car (car (nthcdr n l))) kw) (consp (car (nthcdr n l))))
           (head-in-p kw l))
  :hints (("Goal" :induct (nthcdr n l))))

(defthm head-in-p-of-nthcdr-cdr
  (implies (and (equal (car (car (nthcdr n l))) kw) (consp (car (nthcdr n l))) (not (zp n)))
           (head-in-p kw (cdr l)))
  :hints (("Goal" :use ((:instance head-in-p-of-nthcdr (n (1- n)) (l (cdr l)))))))

(defthm head-in-p-of-last-cdr
  (implies (and (consp (cdr l))
                (consp (car (nthcdr (len (cdr l)) l)))
                (equal (car (car (nthcdr (len (cdr l)) l))) kw))
           (head-in-p kw (cdr l)))
  :hints (("Goal" :use ((:instance head-in-p-of-nthcdr-cdr (n (len (cdr l)))))
                  :in-theory (disable head-in-p-of-nthcdr-cdr head-in-p-of-nthcdr)
                  :expand ((len (cdr l))))))

(defthm nthcdr-len-cdr-of-single
  (implies (not (consp (cdr l))) (equal (nthcdr (len (cdr l)) l) l)))

(defun rule-arg (fn)
  (declare (xargs :mode :program))
  (if (eq (rule-kind fn) :pure) 'redex '(list :|%;%| z redex)))

(defun fallback-lemma (fn)
  (declare (xargs :mode :program))
  (let ((plain (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-FAILS-PLAINLY") 'we::here))
        (mm (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-NEEDS-ITS-OPCODE") 'we::here)))
    `(make-event
      '(:or (progn
              (defthm ,mm
                (implies (not (rule-may-match ',fn redex)) (not (consp (,fn ,(rule-arg fn)))))
                :hints (("Goal" :in-theory (enable ,fn) :do-not-induct t
                                :cases ((consp (cdr redex))))))
              (defthm ,plain
                (and (rule-fails-plainly ',fn z redex) (rule-needs-opcode ',fn z redex))
                :hints (("Goal" :in-theory (disable ,fn rule-may-match)))))
            (value-triple (cw "REFINE-FAILED ~x0~%" ',fn))))))

(defun fallback-lemmas (rules)
  (declare (xargs :mode :program))
  (cond ((endp rules) nil)
        ((or (member-eq (car rules) *fast-memory-rules*) (member-eq (car rules) *frame-safe-rules*))
         (fallback-lemmas (cdr rules)))
        (t (cons (fallback-lemma (car rules)) (fallback-lemmas (cdr rules))))))

(make-event `(progn ,@(fallback-lemmas *step-rules*)))

; return_call_ref in a frame: its rule looks for the instruction with a
; generated search (SEARCH119) from the first RETURN_CALL_REF on; without one
; the search starts past its end. The generic attempt above does not see
; that, so the lemma is tried again here with these facts.
(encapsulate ()
  (local (defthm tag-lo1-when-no-head
           (implies (not (head-in-p tag s))
                    (equal (wrt::%tag-lo1 tag off s i) (+ 1 i (len s))))))
  (local (defthm search119-past-hi
           (implies (< hi k) (equal (w3t::step_read/split/search119 k lo hi l z) nil))
           :hints (("Goal" :expand ((w3t::step_read/split/search119 k lo hi l z)) :do-not-induct t))))
  (local (defthm len-pos-of-consp (implies (consp x) (< 0 (len x))) :rule-classes :linear))
  (make-event (fallback-lemma 'w3t::step_read/split/r-return_call_ref-frame-addr)))

; The lemmas of this section are tried with a fallback that prints
; REFINE-FAILED. The rules without one must be exactly the two host-call
; rules of call_ref (a failed or an interrupted proof of any other rule
; stops certification).
(defconst *fallback-not-yet*
  '(w3t::step/r-call_ref-hostfunc-res w3t::step/r-call_ref-hostfunc-div))

(defun fallback-lemmas-missing (rules wrld)
  (declare (xargs :mode :program))
  (cond ((endp rules) nil)
        ((or (member-eq (car rules) *fast-memory-rules*) (member-eq (car rules) *frame-safe-rules*)
             (getpropc (intern-in-package-of-symbol
                        (concatenate 'string (symbol-name (car rules)) "-FAILS-PLAINLY") 'we::here)
                       'acl2::theorem nil wrld))
         (fallback-lemmas-missing (cdr rules) wrld))
        (t (cons (car rules) (fallback-lemmas-missing (cdr rules) wrld)))))

(make-event
 (let ((missing (fallback-lemmas-missing *step-rules* (w state))))
   (if (equal missing *fallback-not-yet*)
       (value '(value-triple :refine-gaps-as-recorded))
     (er soft 'refine "No fallback lemma for ~x0 (recorded: ~x1)." missing *fallback-not-yet*))))
