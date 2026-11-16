; Facts about the specification that constraint C3 of E3 needs (plan
; E3 item 2): the configurations the machine reports as results do not
; step, for any state Z.
;   - a list of values (the machine's :done)
;   - TRAP alone (:trap)
;   - an exception reference followed by THROW_REF (:throw)
; Nothing about the machine is used here.
(in-package "WE")
(include-book "first-lemmas")

(defun vals-p (l)
  (if (atom l) (null l) (and (w3t::val-p (car l)) (vals-p (cdr l)))))

(defun value-head-p (k)
  (declare (xargs :guard t))
  (member-equal k '(:const :vconst :ref.null_addr :ref.i31_num :ref.struct_addr :ref.array_addr
                    :ref.func_addr :ref.exn_addr :ref.host_addr :ref.extern)))

(defthm val-p-head
  (implies (w3t::val-p x) (and (consp x) (value-head-p (car x))))
  :hints (("Goal" :in-theory (enable w3t::val-p)))
  :rule-classes :forward-chaining)

; --- lists of values -------------------------------------------------------

(defthm vals-p-true-listp
  (implies (vals-p l) (true-listp l))
  :rule-classes :forward-chaining)

(defthm vals-p-of-nthcdr
  (implies (vals-p l) (vals-p (nthcdr k l))))

(defthm vals-p-of-take
  (implies (and (vals-p l) (<= (nfix k) (len l))) (vals-p (take k l))))

(defthm val-p-car-nthcdr
  (implies (and (vals-p l) (consp (nthcdr k l))) (w3t::val-p (car (nthcdr k l)))))

(defthm prefix7-of-vals
  (implies (vals-p l) (equal (w3t::step/prefix7 l) (len l)))
  :hints (("Goal" :in-theory (enable w3t::step/prefix7))))

(in-theory (disable w3t::val-p))

; --- lists of values or NIL (what TAKE and NTHCDR of a value list give) -----

(defun vn-list-p (l)
  (if (atom l) t
    (and (or (null (car l)) (w3t::val-p (car l))) (vn-list-p (cdr l)))))

(defthm vals-p-vn-list-p
  (implies (vals-p l) (vn-list-p l)))

(defthm vn-list-p-of-take
  (implies (vn-list-p l) (vn-list-p (take k l))))

(defthm vn-list-p-of-nthcdr
  (implies (vn-list-p l) (vn-list-p (nthcdr k l))))

(defthm vn-list-p-of-cdr
  (implies (vn-list-p l) (vn-list-p (cdr l))))

; An element of such a list never has the head of an instruction that is
; not a value.
(defthm vn-list-p-car-head
  (implies (and (vn-list-p l) (syntaxp (quotep kw)) kw (not (value-head-p kw)))
           (not (equal (car (car l)) kw)))
  :hints (("Goal" :in-theory (enable w3t::val-p))))

(defthm vn-list-p-car-head-2
  (implies (and (vn-list-p l) (syntaxp (quotep kw)) kw (not (value-head-p kw)))
           (not (equal kw (car (car l)))))
  :hints (("Goal" :use vn-list-p-car-head)))

(defthm vn-list-p-car-nthcdr-head-2
  (implies (and (vn-list-p l) (syntaxp (quotep kw)) kw (not (value-head-p kw)))
           (not (equal kw (car (car (nthcdr j l))))))
  :hints (("Goal" :use ((:instance vn-list-p-car-head (l (nthcdr j l)))))))

(defthm vn-list-p-car-nthcdr-head
  (implies (and (vn-list-p l) (syntaxp (quotep kw)) kw (not (value-head-p kw)))
           (not (equal (car (car (nthcdr j l))) kw)))
  :hints (("Goal" :use ((:instance vn-list-p-car-head (l (nthcdr j l)))))))

; --- one lemma per function, generated ---------------------------------------
; For every search function of the step group (STEP*/SEARCHnn: the list it
; searches is its fourth argument) and every rule function of STEP_PURE,
; STEP_READ/SPLIT and STEP, a lemma that it fails on a list of values. Each
; is tried with (:or ...): one that does not prove prints TERMINAL-FAILED
; in the certification output instead of stopping the book. (Three
; searches fail: STEP/SEARCH21, which a value list never reaches since
; STEP/PREFIX7 is its length, and STEP_READ/SPLIT/SEARCH118 and 119, which
; no rule lemma below needs.)

(defun search-fn-p (fn)
  (declare (xargs :mode :program))
  (let ((s (symbol-name fn)))
    (and (equal (symbol-package-name fn) "W3T")
         (<= 4 (length s)) (equal (subseq s 0 4) "STEP")
         (search "/SEARCH" s)
         (not (search "STEP_READ/SEARCH" s)))))   ; the predicate form, not on STEP's path

(defun search-fns (runes wrld)
  (declare (xargs :mode :program))
  (cond ((endp runes) nil)
        ((and (consp (car runes)) (eq (car (car runes)) :definition)
              (search-fn-p (cadr (car runes)))
              (getpropc (cadr (car runes)) 'acl2::recursivep nil wrld))
         (cons (cadr (car runes)) (search-fns (cdr runes) wrld)))
        (t (search-fns (cdr runes) wrld))))

(defun search-lemma (fn wrld)
  (declare (xargs :mode :program))
  (let* ((formals (acl2::formals fn wrld))
         (name (intern-in-package-of-symbol
                (concatenate 'string (symbol-name fn) "-OF-VALS") 'we::here)))
    `(make-event
      '(:or (defthm ,name
              (implies (vn-list-p ,(nth 3 formals)) (not (,fn ,@formals)))
              :hints (("Goal" :in-theory (enable ,fn) :induct (,fn ,@formals) :do-not-induct t)))
            (value-triple (cw "TERMINAL-FAILED ~x0~%" ',fn))))))

(defun search-lemmas (fns wrld)
  (declare (xargs :mode :program))
  (if (endp fns) nil (cons (search-lemma (car fns) wrld) (search-lemmas (cdr fns) wrld))))

(make-event
 `(progn ,@(search-lemmas (search-fns (acl2::function-theory-fn :here (w state)) (w state)) (w state))))

; Every rule function of STEP_PURE, STEP_READ/SPLIT and STEP (the context
; rules included) fails on a list of values, for any state.
(mutual-recursion
(defun rule-calls-of (term)
  (declare (xargs :mode :program))
  (cond ((or (atom term) (eq (car term) 'quote)) nil)
        ((consp (car term))
         (append (rule-calls-of-list (cdr term)) (rule-calls-of (caddr (car term)))))
        (t (append (and (symbolp (car term)) (equal (symbol-package-name (car term)) "W3T")
                        (search "/R-" (symbol-name (car term))) (list (car term)))
                   (rule-calls-of-list (cdr term))))))
(defun rule-calls-of-list (terms)
  (declare (xargs :mode :program))
  (if (atom terms) nil (append (rule-calls-of (car terms)) (rule-calls-of-list (cdr terms))))))

(defun rule-lemma (fn pure hyp lst suffix)
  (declare (xargs :mode :program))
  (let* ((name (intern-in-package-of-symbol
                (concatenate 'string (symbol-name fn) suffix) 'we::here))
         (call (if pure `(,fn ,lst) `(,fn (list :|%;%| z ,lst)))))
    `(make-event
      '(:or (defthm ,name (implies ,hyp (not ,call))
              :hints (("Goal" :in-theory (enable ,fn) :do-not-induct t)))
            (value-triple (cw "TERMINAL-FAILED ~x0~%" ',fn))))))

(defun rule-lemmas (fns pure hyp lst suffix)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (cons (rule-lemma (car fns) pure hyp lst suffix) (rule-lemmas (cdr fns) pure hyp lst suffix))))

; all rule lemmas for the instruction list LST under hypothesis HYP
(defun all-rule-lemmas (hyp lst suffix wrld)
  (declare (xargs :mode :program))
  (append
   (rule-lemmas (rule-calls-of (getpropc 'w3t::step_pure 'acl2::unnormalized-body nil wrld)) t hyp lst suffix)
   (rule-lemmas (rule-calls-of (getpropc 'w3t::step_read/split 'acl2::unnormalized-body nil wrld)) nil hyp lst suffix)
   (rule-lemmas (set-difference-eq
                 (rule-calls-of (getpropc 'w3t::step 'acl2::unnormalized-body nil wrld))
                 '(w3t::step/r-pure w3t::step/r-read w3t::step/r-ctxt-instrs))
                nil hyp lst suffix)))

(make-event `(progn ,@(all-rule-lemmas '(vals-p l) 'l "-OF-VALS" (w state))))

; The recursive members of STEP's clique are opened by :expand.
(defthm step/r-ctxt-instrs-of-vals
  (implies (vals-p l) (not (w3t::step/r-ctxt-instrs (list :|%;%| z l))))
  :hints (("Goal" :expand ((w3t::step/r-ctxt-instrs (list :|%;%| z l))))))

(defthm step_pure-of-vals
  (implies (vals-p l) (not (w3t::step_pure l)))
  :hints (("Goal" :in-theory (enable w3t::step_pure))))

(defthm step_read/split-of-vals
  (implies (vals-p l) (not (w3t::step_read/split (list :|%;%| z l))))
  :hints (("Goal" :in-theory (enable w3t::step_read/split))))

; C3, part 1: a list of values does not step (the machine's :done).
(defthm step-of-vals
  (implies (vals-p l) (not (w3t::step (list :|%;%| z l))))
  :hints (("Goal" :in-theory (enable w3t::step/r-pure w3t::step/r-read)
                  :expand ((w3t::step (list :|%;%| z l))))))

; C3, part 2: TRAP alone does not step (the machine's :trap).
(defthm step-of-trap-alone
  (equal (w3t::step (list :|%;%| z '((:trap)))) nil)
  :hints (("Goal" :in-theory (enable step-rule-defs)
                  :expand ((:free (x) (w3t::step x))
                           (:free (x) (w3t::step/r-ctxt-instrs x))
                           (:free (k lo hi a b zz c) (w3t::step/search21 k lo hi a b zz c))))))

;
; THROW_REF alone (no reference) does not step either; ctxt-instrs reaches
; it below.
(defthm step-of-throw_ref-alone
  (equal (w3t::step (list :|%;%| z '((:throw_ref)))) nil)
  :hints (("Goal" :in-theory (enable step-rule-defs)
                  :expand ((:free (x) (w3t::step x))
                           (:free (x) (w3t::step/r-ctxt-instrs x))
                           (:free (k lo hi a b zz c) (w3t::step/search21 k lo hi a b zz c))))))

; C3, part 3: an exception reference and THROW_REF do not step (the
; machine's :throw). The two rules whose redex is "anything around TRAP or
; THROW_REF" search a list that is not a value list, and the generated
; lemma does not cover them; they are proved with their search expanded.
(make-event `(progn ,@(all-rule-lemmas t '(list (list :ref.exn_addr a) '(:throw_ref)) "-OF-EXN" (w state))))

(defthm step_pure/r-trap-instrs-of-exn
  (not (w3t::step_pure/r-trap-instrs (list (list :ref.exn_addr a) '(:throw_ref))))
  :hints (("Goal" :in-theory (enable w3t::step_pure/r-trap-instrs)
                  :expand ((:free (k lo hi x) (w3t::step_pure/search171 k lo hi x))))))

(defthm step_read/split/r-throw_ref-instrs-of-exn
  (not (w3t::step_read/split/r-throw_ref-instrs
        (list :|%;%| z (list (list :ref.exn_addr a) '(:throw_ref)))))
  :hints (("Goal" :in-theory (enable w3t::step_read/split/r-throw_ref-instrs)
                  :expand ((:free (k lo hi x) (w3t::step_read/split/search134 k lo hi x))))))

(defthm step/r-ctxt-instrs-of-exn
  (implies (w3t::val-p (list :ref.exn_addr a))
           (not (w3t::step/r-ctxt-instrs (list :|%;%| z (list (list :ref.exn_addr a) '(:throw_ref))))))
  :hints (("Goal" :in-theory (enable w3t::step/prefix7)
                  :expand ((:free (x) (w3t::step/r-ctxt-instrs x))
                           (:free (k lo hi aa b zz c) (w3t::step/search21 k lo hi aa b zz c))))))

(defthm step_pure-of-exn
  (not (w3t::step_pure (list (list :ref.exn_addr a) '(:throw_ref))))
  :hints (("Goal" :in-theory (enable w3t::step_pure))))

(defthm step_read/split-of-exn
  (not (w3t::step_read/split (list :|%;%| z (list (list :ref.exn_addr a) '(:throw_ref)))))
  :hints (("Goal" :in-theory (enable w3t::step_read/split))))

(defthm step-of-uncaught-exception
  (implies (w3t::val-p (list :ref.exn_addr a))
           (not (w3t::step (list :|%;%| z (list (list :ref.exn_addr a) '(:throw_ref))))))
  :hints (("Goal" :in-theory (enable w3t::step/r-pure w3t::step/r-read)
                  :expand ((w3t::step (list :|%;%| z (list (list :ref.exn_addr a) '(:throw_ref))))))))
