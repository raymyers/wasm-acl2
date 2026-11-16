; E7 Phase B, layer 4: towards the step theorem.
; (U) Per rule, one statement for every rule on STEP's path: unless the
; fast machine refuses (:refuse, a fallback result it cannot hold), the
; rule applied by FAST-APPLY-RULE on the fast store and the array agrees
; with APPLY-RULE on the full store: it fires exactly when the list
; machine's does, with the same instructions, and the full state is the
; fast state with the array put back as memory 0's bytes.
(in-package "WE")
(include-book "refine-mem")

(in-theory (disable load-num-val-is-window))

(defun fast-inv-store (s)
  (declare (xargs :guard t))
  (and (ec-call (fast-store-ok s)) (mem0-record-p s)))

(defthm not-refuse-gives-result-ok
  (implies (and (not (equal (car (fast-apply-fallback fn (list :|%;%| s f) redex fm)) :refuse))
                (byte-list-p (nth *fm-memi* fm)))
           (fallback-result-ok fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))
  :hints (("Goal" :in-theory (disable apply-rule put-mem0-bytes fallback-shape-ok list-to-mem))))

(defthm fast-apply-fallback-car-exact
  (implies (byte-list-p (nth *fm-memi* fm))
           (equal (car (fast-apply-fallback fn (list :|%;%| s f) redex fm))
                  (if (car (apply-rule fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))
                      (if (fallback-shape-ok (cadr (apply-rule fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex)))
                          t :refuse)
                    nil)))
  :hints (("Goal" :in-theory (disable apply-rule put-mem0-bytes fallback-shape-ok list-to-mem))))

(in-theory (disable fast-apply-fallback-car))

; the opcode and plain-failure facts for the memory rules (the others are in
; refine.lisp); names apart from refine-mem's
(defun memory-facts-lemma (fn)
  (declare (xargs :mode :program))
  (let ((plain (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-FACTS") 'we::here))
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
            (value-triple (cw "REFINE-STEP-FAILED ~x0~%" ',fn))))))

(defun memory-facts-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (memory-facts-lemma (car fns)) (memory-facts-lemmas (cdr fns)))))

(make-event `(progn ,@(memory-facts-lemmas *fast-memory-rules*)))

; --- (U) ---------------------------------------------------------------------

(defun u-hints (fn)
  (declare (xargs :mode :program))
  (cond ((member-eq fn *fast-memory-step-rules*)
         (let ((refines (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-FAST-REFINES") 'we::here)))
           `(("Goal" :cases ((one-memory-p (list :|%;%| s f))) :do-not-induct t)
             ("Subgoal 1" :use ((:instance ,refines))
                          :in-theory (disable ,refines fast-apply-rule apply-rule ,fn put-mem0-bytes fast-store-ok
                                              one-memory-p mem0-record-p put-z-bytes))
             ("Subgoal 2" :in-theory (e/d (fast-apply-rule fallback-result-ok)
                                          (,fn put-mem0-bytes fast-store-ok put-result-bytes fast-apply-fallback
                                               apply-rule rule-may-match fallback-shape-ok one-memory-p mem0-record-p))))))
        ((member-eq fn *fast-memory-rules*)
         `(("Goal" :cases ((one-memory-p (list :|%;%| s f)))
                   :in-theory (e/d (fast-apply-rule fallback-result-ok fast-memory-rule)
                                   (,fn put-mem0-bytes fast-store-ok put-result-bytes
                                    fast-apply-fallback apply-rule rule-may-match fallback-shape-ok one-memory-p
                                    mem0-record-p ,(fast-name fn)))
                   :do-not-induct t)))
        ((member-eq fn *frame-safe-rules*)
         `(("Goal" :in-theory (e/d (fast-apply-rule) (,fn put-mem0-bytes fast-store-ok put-result-bytes))
                   :do-not-induct t)))
        (t
         `(("Goal" :in-theory (e/d (fast-apply-rule fallback-result-ok)
                                   (,fn put-mem0-bytes fast-store-ok put-result-bytes fast-apply-fallback apply-rule
                                    rule-may-match fallback-shape-ok))
                   :do-not-induct t)))))

(defun u-lemma (fn)
  (declare (xargs :mode :program))
  (let ((name (intern-in-package-of-symbol (concatenate 'string (symbol-name fn) "-U") 'we::here)))
    `(make-event
      '(:or (defthm ,name
              (let ((full (apply-rule ',fn (list :|%;%| (put-mem0-bytes s (nth *fm-memi* fm)) f) redex))
                    (fast (fast-apply-rule ',fn (list :|%;%| s f) redex fm)))
                (implies (and (fast-inv-store s) (byte-list-p (nth *fm-memi* fm))
                              (not (equal (car fast) :refuse)))
                         (and (iff (car full) (car fast))
                              (implies (car fast)
                                       (and (equal (cadr full)
                                                   (put-z-bytes (cadr fast) (nth *fm-memi* (cadddr fast))))
                                            (equal (caddr full) (caddr fast)))))))
              :hints ,(u-hints fn))
            (value-triple (cw "REFINE-STEP-FAILED ~x0~%" ',fn))))))

(defun u-lemmas (fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (u-lemma (car fns)) (u-lemmas (cdr fns)))))

(make-event `(progn ,@(u-lemmas *step-rules*)))
