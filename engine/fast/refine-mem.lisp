; E7 Phase B, the memory rules: the generated fast versions (FAST-<rule> in
; fast.lisp) on the fast store and the array agree with the spec's rules on
; the full store. One memory (ONE-MEMORY-P), the fast store invariant, and
; memory 0 a record.
(in-package "WE")
(include-book "refine")

(defun mem0-record-p (s)
  (declare (xargs :guard t))
  (let ((mems (wrt::%get-field s :mems)))
    (and (consp (car-t mems)) (alistp (cdr (car-t mems))))))

; --- the array ---------------------------------------------------------------

(defun window (a n l)
  (if (zp n) nil (let ((a (nfix a))) (cons (nth a l) (window (1+ a) (1- n) l)))))

(defthm car-nthcdr (equal (car (nthcdr a l)) (nth a l)))
(defthm cdr-nthcdr (equal (cdr (nthcdr a l)) (nthcdr (1+ (nfix a)) l)))

(defthm window-is-take
  (equal (window a n l) (take n (nthcdr a l)))
  :hints (("Goal" :induct (window a n l))
          ("Subgoal *1/2" :expand ((take n (nthcdr a l))))))

(defthm nth-past-len (implies (<= (len l) (nfix a)) (equal (nth a l) nil)))

(defthm mem-window-is-window
  (equal (mem-window a n fm) (window a n (nth *fm-memi* fm))))

(defthm mem-window-is-take
  (equal (mem-window a n fm) (take n (nthcdr a (nth *fm-memi* fm)))))

(in-theory (disable mem-window-is-window))

(defthm fm-mem-length-is-len (equal (fm-mem-length fm) (len (nth *fm-memi* fm))))
(in-theory (disable fm-mem-length))

(defthm len-update-nth-in (implies (< (nfix i) (len l)) (equal (len (update-nth i v l)) (len l))))

(defthm append-take-nthcdr
  (implies (and (natp i) (<= i (len l)) (true-listp l))
           (equal (append (take i l) (nthcdr i l)) l)))

(defthm nthcdr-of-update-nth-before
  (implies (and (natp i) (natp n) (< i n))
           (equal (nthcdr n (update-nth i v l)) (nthcdr n l))))

(defthm mem-write-array
  (implies (and (natp i) (byte-list-p b) (true-listp (nth *fm-memi* fm))
                (<= (+ i (len b)) (len (nth *fm-memi* fm))))
           (equal (nth *fm-memi* (mem-write i b fm))
                  (append (take i (nth *fm-memi* fm)) b (nthcdr (+ i (len b)) (nth *fm-memi* fm)))))
  :hints (("Goal" :induct (mem-write i b fm) :in-theory (disable take nthcdr))))

; --- the store ---------------------------------------------------------------

(defthm mem-of-full
  (implies (and (one-memory-p (list :|%;%| s f)) (fast-store-ok s) (mem0-record-p s))
           (equal (w3t::$mem (list :|%;%| (put-mem0-bytes s b) f) x)
                  (wrt::%put-field (w3t::$mem (list :|%;%| s f) x) :bytes b)))
  :hints (("Goal" :do-not-induct t)))

(defthm mem-of-fast-is-record
  (implies (and (one-memory-p (list :|%;%| s f)) (fast-store-ok s) (mem0-record-p s))
           (and (consp (w3t::$mem (list :|%;%| s f) x))
                (alistp (cdr (w3t::$mem (list :|%;%| s f) x)))))
  :hints (("Goal" :do-not-induct t)))

(defthm with-mem-of-full
  (implies (and (one-memory-p (list :|%;%| s f)) (fast-store-ok s) (mem0-record-p s) (true-listp b))
           (equal (w3t::$with_mem (list :|%;%| (put-mem0-bytes s a) f) x i j b)
                  (list :|%;%| (put-mem0-bytes s (append (take i a) b (nthcdr (+ i j) a))) f)))
  :hints (("Goal" :do-not-induct t)))

(defthm get-field-of-put-mem0-bytes-other
  (implies (not (equal k :mems))
           (equal (wrt::%get-field (put-mem0-bytes s b) k) (wrt::%get-field s k))))

(defthm put-mem0-bytes-keeps-record
  (implies (and (consp s) (alistp (cdr s)))
           (and (consp (put-mem0-bytes s b)) (alistp (cdr (put-mem0-bytes s b))))))

; --- the read rules: the fast version is the rule on the full store ---------

(defun memory-read-lemma (fn)
  (declare (xargs :mode :program))
  `(make-event
    '(:or (defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-FAST-IS-FULL") 'we::here)
            (implies (and (one-memory-p (list :|%;%| s f)) (fast-store-ok s) (mem0-record-p s))
                     (equal (,(fast-name fn) (list :|%;%| (list :|%;%| s f) redex) fm)
                            (,fn (list :|%;%| (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))))
            :hints (("Goal" :in-theory (e/d (,fn) (w3t::$mem put-mem0-bytes wrt::%put-field one-memory-p
                                                   fast-store-ok mem0-record-p))
                            :do-not-induct t)))
          (value-triple (cw "REFINE-MEM-FAILED ~x0~%" ',fn)))))

(defun memory-read-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (memory-read-lemma (car fns)) (memory-read-lemmas (cdr fns)))))

(make-event `(progn ,@(memory-read-lemmas (set-difference-eq *fast-memory-rules* *fast-memory-step-rules*))))

; --- the fallback, as rewrites of the fast side --------------------------------

(defthm mv-nth-1-2-3
  (and (equal (mv-nth 1 x) (cadr x)) (equal (mv-nth 2 x) (caddr x)) (equal (mv-nth 3 x) (cadddr x))))

(defmacro fallback-hyps ()
  '(and (fast-store-ok s) (byte-list-p (nth *fm-memi* fm))
        (fallback-result-ok fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex)
        (rule-fails-plainly fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex)))

(defthm fast-apply-fallback-car
  (implies (fallback-hyps)
           (equal (car (fast-apply-fallback fn (list :|%;%| s f) redex fm))
                  (car (apply-rule fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))))
  :hints (("Goal" :in-theory (disable apply-rule put-mem0-bytes mem0-of-store mem0-shape-ok fast-store-ok list-to-mem)
                  :do-not-induct t)))

(defthm fast-apply-fallback-caddr
  (implies (fallback-hyps)
           (equal (caddr (fast-apply-fallback fn (list :|%;%| s f) redex fm))
                  (caddr (apply-rule fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))))
  :hints (("Goal" :in-theory (disable apply-rule put-mem0-bytes mem0-of-store mem0-shape-ok fast-store-ok list-to-mem)
                  :do-not-induct t)))

(defthm fast-apply-fallback-cadr
  (implies (fallback-hyps)
           (equal (put-z-bytes (cadr (fast-apply-fallback fn (list :|%;%| s f) redex fm))
                               (nth *fm-memi* (cadddr (fast-apply-fallback fn (list :|%;%| s f) redex fm))))
                  (cadr (apply-rule fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))))
  :hints (("Goal" :in-theory (disable apply-rule put-mem0-bytes mem0-of-store mem0-shape-ok fast-store-ok list-to-mem)
                  :do-not-induct t)))

; --- the store rules: written into the array, or the exact fallback -----------

(defun memory-store-lemma (fn)
  (declare (xargs :mode :program))
  (let ((plain (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-FAILS-PLAINLY") 'we::here))
        (name (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-FAST-REFINES") 'we::here)))
    `(make-event
      '(:or (progn
              (defthm ,plain
                (rule-fails-plainly ',fn z redex)
                :hints (("Goal" :in-theory (disable ,fn))))
              (defthm ,name
                (implies (and (one-memory-p (list :|%;%| s f)) (fast-store-ok s) (mem0-record-p s)
                              (byte-list-p (nth *fm-memi* fm))
                              (not (equal (mv-nth 0 (fast-apply-rule ',fn (list :|%;%| s f) redex fm)) :refuse)))
                         (let ((full (apply-rule ',fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))
                               (fast (fast-apply-rule ',fn (list :|%;%| s f) redex fm)))
                           (and (equal (mv-nth 0 full) (mv-nth 0 fast))
                                (equal (mv-nth 1 full) (put-z-bytes (mv-nth 1 fast) (nth *fm-memi* (mv-nth 3 fast))))
                                (equal (mv-nth 2 full) (mv-nth 2 fast)))))
                :hints (("Goal" :in-theory (e/d (fast-apply-rule)
                                                (w3t::$mem put-mem0-bytes w3t::$with_mem wrt::%put-field one-memory-p
                                                 fast-store-ok mem0-record-p fast-apply-fallback fallback-result-ok
                                                 rule-fails-plainly
                                                 ; the bytes written stay abstract: the fast path checks them
                                                 wrt::$nbytes_ wrt::$ibytes_ wrt::$fbytes_ wrt::%le-bytes))
                                :do-not-induct t))))
            (value-triple (cw "REFINE-MEM-FAILED ~x0~%" ',fn))))))

(defun memory-store-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (memory-store-lemma (car fns)) (memory-store-lemmas (cdr fns)))))

(make-event `(progn ,@(memory-store-lemmas *fast-memory-step-rules*)))
