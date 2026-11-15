; 3.0 instruction typing, behavioural cases (wasm3 M6): the generated
; EXPR_OK (check variant) on function bodies, against V8's verdict on the
; same body in a module (typing-oracle-3.0.lsp, ../oracle/gen-typing-oracle.mjs).
; The context mirrors that module: functions $f : [(ref null i31)] -> [] and
; $g : [i64] -> [], tag $e : [] -> [], labels and return the result type,
; locals the parameters (set) and the declared locals (set if defaultable).
; The book prints N of M and the failing cases; it does not fail on a wrong
; answer (recorded before the sequencer of option C, plan M6).
(in-package "W3T")
(include-book "../../gen/wasm-3.0/wasm3")

(program)
(set-state-ok t)

(defun fty (params results) (list :_def (list :rec (list (list :sub '((:final)) nil (list :func%->% params results)))) 0))
(defconst *i32* '(:i32))
(defconst *i64* '(:i64))
(defconst *ri31* '(:ref nil (:i31)))
(defconst *rni31* '(:ref ((:null)) (:i31)))
(defconst *anyref* '(:ref ((:null)) (:any)))
(defun lset (t1) (list '(:set) t1))
(defun lunset (t1) (list '(:unset) t1))
(defun ctx (locals results)
  (list :%rec '(:types) (list :tags (fty nil nil)) '(:globals) '(:mems) '(:tables)
        (list :funcs (fty (list *rni31*) nil) (fty (list *i64*) nil))
        '(:datas) '(:elems) (cons :locals locals) (list :labels results) (list :return results)
        '(:refs) '(:recs)))
(defun k32 (n) (list :const *i32* n))
(defconst *add* '(:binop (:i32) (:add)))
(defun blk (results body) (list :block (list :_result results) body))

; (name locals results instrs)
(defconst *cases*
  `(("const add : i32" nil (,*i32*) (,(k32 1) ,(k32 2) ,*add*))
    ("add without operands" nil (,*i32*) (,*add*))
    ("empty : []" nil nil nil)
    ("empty : i32" nil (,*i32*) nil)
    ("const drop : []" nil nil (,(k32 1) (:drop)))
    ("two results left" nil (,*i32*) (,(k32 1) ,(k32 2)))
    ("frame: param kept below" (,(lset *i32*)) (,*i32*) ((:local.get 0) ,(k32 1) (:drop)))
    ("subsumption at block end" nil (,*rni31*) (,(blk (list *rni31*) (list (k32 1) '(:ref.i31)))))
    ("subsumption at function end" nil (,*anyref*) (,(k32 1) (:ref.i31)))
    ("no subsumption downward" nil (,*ri31*) ((:ref.null (:i31))))
    ("subsumption at a call" nil nil (,(k32 1) (:ref.i31) (:call 0)))
    ("call with a wrong operand" nil nil (,(k32 1) (:call 1)))
    ("uninitialized non-defaultable local" (,(lunset *ri31*)) nil ((:local.get 0) (:drop)))
    ("initialized non-defaultable local" (,(lunset *ri31*)) nil (,(k32 1) (:ref.i31) (:local.set 0) (:local.get 0) (:drop)))
    ("dead code after unreachable" nil (,*i32*) ((:unreachable) ,*add*))
    ("dead code after br" nil nil (,(blk nil (list '(:br 0) *add* '(:drop)))))
    ("dead code after throw" nil (,*i32*) ((:throw 0) ,*add*))
    ("dead code with a wrong type" nil (,*i32*) ((:unreachable) (:const (:i64) 0) ,*add*))
    ("br with a value" nil (,*i32*) (,(blk (list *i32*) (list (k32 1) '(:br 0)))))
    ("br_if" nil (,*i32*) (,(blk (list *i32*) (list (k32 1) (k32 0) '(:br_if 0)))))
    ("select" nil (,*i32*) (,(k32 1) ,(k32 2) ,(k32 0) (:select nil)))
    ("return" nil (,*i32*) (,(k32 1) (:return)))
    ("return with a wrong type" nil (,*i32*) ((:const (:i64) 1) (:return)))
    ("nested blocks" nil (,*i32*) (,(blk (list *i32*) (list (blk (list *i32*) (list (k32 7)))))))))

(defun run-cases (cs oracle)
  ;; ((name expected got) ...) with expected from V8
  (if (atom cs) nil
    (let* ((c (car cs)) (name (first c))
           (want (cdr (assoc-equal name oracle)))
           (got (and (expr_ok (ctx (second c) (third c)) (fourth c) (third c)) t)))
      (cons (list name want got) (run-cases (cdr cs) oracle)))))

(defun wrong (rs) (cond ((atom rs) nil) ((equal (second (car rs)) (third (car rs))) (wrong (cdr rs))) (t (cons (car rs) (wrong (cdr rs))))))
(defun instrs-p (is) (or (atom is) (and (instr-p (car is)) (instrs-p (cdr is)))))
(defun encodings-ok (cs)
  (or (atom cs)
      (and (context-p (ctx (second (car cs)) (third (car cs))))
           (instrs-p (fourth (car cs)))
           (encodings-ok (cdr cs)))))

(make-event
 (mv-let (channel state) (open-input-channel "typing-oracle-3.0.lsp" :object state)
   (mv-let (eofp oracle state) (read-object channel state)
     (let* ((state (close-input-channel channel state))
            (rs (and (not eofp) (run-cases *cases* oracle))) (bad (wrong rs)))
       (prog2$ (cw "~%T6 instruction typing (3.0): ~x0 of ~x1 cases agree with V8 (encodings ~x2).~%Wrong (name V8 generated): ~x3~%"
                   (- (acl2::len rs) (acl2::len bad)) (acl2::len rs) (encodings-ok *cases*) bad)
               (if (encodings-ok *cases*) (mv nil '(value-triple :t6-instr-typing-3.0) state)
                 (mv (msg "a case uses an encoding the generated recognizers reject") nil state)))))))
