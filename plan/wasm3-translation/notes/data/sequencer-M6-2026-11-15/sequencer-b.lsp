; DRAFT (wasm3 M6, option C): the instruction-typing sequencer as a config
; :rel-override of Instrs_ok in check mode, and the three :il-patch entries
; of step 3 (b). For a SCRATCH config only (run.sh appends this to a copy of
; config/wasm-3.0.lsp): step 3 is the user's choice, (a) or (b).
;
; INSTRS_OK C instr* (t_1* ->_(x*) t_2*): simulate the stack, starting from
; t_1* (top first in STK), for each instruction propose a type a ->_(x*) b
; (the kept variant INSTR_OK/OUT2, else the table below), CHECK it with the
; generated INSTR_OK, pop a with the generated RESULTTYPE_SUB, push b, set
; the locals x* (Instrs_ok/seq), and after a stack-polymorphic instruction
; let missing operands be anything (the spec's algorithm). At the end the
; stack must be a subtype of t_2* and x* must be among the initialized
; locals. Soundness rests on the generated checks; a wrong proposal can only
; make it reject.

 (:rel-override "Instrs_ok" :mode :check
  :defuns
  ((defun seq-put-field (r k v)
     ;; record R (:%rec (k . v) ...) with field K set to V
     (cond ((atom r) r)
           ((and (consp (car r)) (eq (car (car r)) k)) (cons (cons k v) (cdr r)))
           (t (cons (car r) (seq-put-field (cdr r) k v)))))
   (defun seq-set-locals (ls xs)
     ;; locals LS with the indices XS set: ((:set) t)
     (if (atom xs) ls
       (seq-set-locals (update-nth (car xs) (list (quote (:set)) (cadr (nth (car xs) ls))) ls) (cdr xs))))
   (defun seq-with-locals (c xs)
     (seq-put-field c :locals (seq-set-locals (%get-field c :locals) xs)))
   (defun seq-nonnull (rt) (if (and (consp rt) (eq (car rt) :ref)) (list :ref nil (caddr rt)) rt))
   (defun seq-null-like (rt ht)
     (if (and (consp rt) (eq (car rt) :ref)) (list :ref (cadr rt) ht) (list :ref (quote ((:null))) ht)))
   (defun seq-label (c l) (nth l (%get-field c :labels)))
   (defun seq-params (dt)
     ;; parameters of a function type or tag type (a deftype)
     (let ((ct (car (expand dt)))) (and (consp ct) (eq (car ct) :func%->%) (cadr ct))))
   (defun seq-poly-p (i)
     (member-eq (car i) (quote (:unreachable :br :br_table :return :return_call :return_call_ref
                                :return_call_indirect :throw :throw_ref))))
   (defun seq-table (c i stk)
     ;; (a b) for the 18 rules INSTR_OK/OUT2 leaves out, or nil
     (let ((top (if (consp stk) (car stk) (quote (:bot)))) (snd (if (consp (cdr stk)) (cadr stk) (quote (:bot)))))
       (case (car i)
         (:unreachable (list nil nil))
         (:drop (list (list top) nil))
         (:select (list (list snd snd (quote (:i32))) (list snd)))
         (:br (list (seq-label c (cadr i)) nil))
         (:br_table (list (append (seq-label c (caddr i)) (list (quote (:i32)))) nil))
         (:return (list (car (%get-field c :return)) nil))
         (:return_call (list (seq-params (nth (cadr i) (%get-field c :funcs))) nil))
         (:throw (list (seq-params (nth (cadr i) (%get-field c :tags))) nil))
         (:throw_ref (list (list (quote (:ref ((:null)) (:exn)))) nil))
         (:ref.is_null (list (list top) (list (quote (:i32)))))
         (:ref.as_non_null (list (list top) (list (seq-nonnull top))))
         (:br_on_null (list (append (seq-label c (cadr i)) (list top))
                            (append (seq-label c (cadr i)) (list (seq-nonnull top)))))
         (:ref.test (list (list top) (list (quote (:i32)))))
         (:ref.cast (list (list top) (list (cadr i))))
         (:any.convert_extern (list (list top) (list (seq-null-like top (quote (:any))))))
         (:extern.convert_any (list (list top) (list (seq-null-like top (quote (:extern))))))
         (otherwise nil))))
   (defun seq-propose (c i stk)
     ;; (a x b) or nil
     (let ((p (instr_ok/out2 c i)))
       (if (consp p) (cdr (car p))
         (let ((tb (seq-table c i stk))) (and tb (list (car tb) nil (cadr tb)))))))
   (defun seq-run (c is stk xs poly)
     ;; (mv ok stk xs poly): STK top first
     (if (atom is) (mv t stk xs poly)
       (let* ((i (car is)) (p (seq-propose c i stk)))
         (if (null p) (mv nil stk xs poly)
           (let* ((a (first p)) (x (second p)) (b (third p)) (n (len a))
                  (have (min n (len stk)))
                  (top (reverse (take have stk))))
             (if (or (not (instr_ok c i (list :%->_%% a x b)))
                     (and (< (len stk) n) (not poly))
                     (not (resulttype_sub c top (nthcdr (- n have) a))))
                 (mv nil stk xs poly)
               (let ((p2 (seq-poly-p i)))
                 (seq-run (seq-with-locals c x) (cdr is)
                          (if p2 nil (append (reverse b) (nthcdr have stk)))
                          (append xs x) (or p2 (and poly (< (len stk) n)))))))))))
   (defun instrs_ok (c is ty)
     (let ((t1 (cadr ty)) (x (caddr ty)) (t2 (cadddr ty)))
       (mv-let (ok stk xs poly) (seq-run c is (reverse t1) nil nil)
         (and ok
              (if poly (<= (len stk) (len t2)) (equal (len stk) (len t2)))
              (resulttype_sub c (reverse stk) (nthcdr (- (len t2) (len stk)) t2))
              (subsetp-equal x xs)
              t)))))
  :reason "DRAFT of the option C sequencer (scratch only)")

 (:il-patch "Instr_ok" :old (iter (var "x") list (dom "x" (var "x*"))) :new (list)
  :reason "DRAFT step 3 (b): block, loop, try_table call Instrs_ok with x* = [] (equivalent by Instrs_ok/sub)")
 (:il-patch "Instr_ok" :old (iter (var "x_1") list (dom "x_1" (var "x_1*"))) :new (list)
  :reason "DRAFT step 3 (b): if, then branch")
 (:il-patch "Instr_ok" :old (iter (var "x_2") list (dom "x_2" (var "x_2*"))) :new (list)
  :reason "DRAFT step 3 (b): if, else branch")
