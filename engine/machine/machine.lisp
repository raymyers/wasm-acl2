; License: MIT. See the file LICENSE at the top of the repository.
;
; The list machine of the verified engine (plan/wasm-engine E6), after the
; design of notes/E5-machine.md.
;
; A state keeps the spec's own data: the store, the frame of the innermost
; activation, the operand stack VALS of the innermost block (top first),
; the instructions IS still to run there, and an explicit control stack
; CTRL of label, handler and frame entries, innermost first. MACHINE-ABS rebuilds
; the spec configuration, with the nested LABEL_/HANDLER_/FRAME_ terms.
;
; How a step is made. The machine does not restate the rules of the spec.
; It chooses the redex, by the head instruction, and applies the spec's own
; rule functions to it (the functions W3T::STEP_PURE/R-<rule>,
; W3T::STEP_READ/SPLIT/R-<rule> and W3T::STEP/R-<rule> that the translator
; emits since E2), in the order in which W3T::STEP tries them:
;
; - a value at the head moves to VALS (no spec step: MACHINE-ABS is unchanged);
; - a LABEL_, HANDLER_ or FRAME_ at the head is entered: a control entry is
;   pushed (no spec step);
; - an instruction I with K operands: the redex is the top K values and I,
;   and the rules for I's opcode are tried on it (one spec step);
; - TRAP (or THROW_REF) with other values or instructions around it: the
;   rule TRAP-INSTRS (THROW_REF-INSTRS) on the whole block (one spec step);
; - an empty block, or BR, RETURN, TRAP, THROW_REF at the head of a block
;   inside a control entry: the entry's administrative term is rebuilt and
;   the rules whose redex is that term are tried (one spec step).
;
; The rule table (which rule belongs to which opcode or entry, in STEP's
; order) and the function APPLY-RULE that calls a rule by name are made by
; MAKE-EVENT from the bodies of W3T::STEP_PURE, W3T::STEP_READ/SPLIT and
; W3T::STEP, so they follow the specification when it is regenerated.
;
; The arithmetic, the memory and the type checks are those of the rule
; functions (D6). Every function here is in logic mode with guards
; verified; the spec's functions are reached through EC-CALL, since most of
; them are logic mode without verified guards (tests/sem-3.0/modes-3.0.lsp).
(in-package "WE")
(include-book "../../translate/gen/wasm-3.0/wasm3")

; ---------------------------------------------------------------------------
; Lists, with guard T

(defun car-t (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun cdr-t (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))

(defun take-n (n l)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom l)) nil (cons (car l) (take-n (1- n) (cdr l)))))

(defun drop-n (n l)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom l)) l (drop-n (1- n) (cdr l))))

(defun rev-onto (l acc)                 ; (append (reverse l) acc)
  (declare (xargs :guard t))
  (if (atom l) acc (rev-onto (cdr l) (cons (car l) acc))))

(defun app (a b)
  (declare (xargs :guard t))
  (if (atom a) b (cons (car a) (app (cdr a) b))))

(defun nth-t (n l)
  (declare (xargs :guard t))
  (cond ((atom l) nil) ((zp (nfix n)) (car l)) (t (nth-t (1- (nfix n)) (cdr l)))))

(defun len-t (l)
  (declare (xargs :guard t))
  (if (atom l) 0 (1+ (len-t (cdr l)))))

(defun sym-member (x l)
  (declare (xargs :guard t))
  (and (consp l) (or (equal x (car l)) (sym-member x (cdr l)))))

; ---------------------------------------------------------------------------
; Machine state. A plain list; the accessors and updaters below are the
; only functions that know its layout (E7 replaces them by stobj
; primitives).

(defun ms (store frame vals is ctrl status)
  (declare (xargs :guard t))
  (list store frame vals is ctrl status))
(defun ms-store (s) (declare (xargs :guard t)) (if (consp s) (car-t s) nil))
(defun ms-frame (s) (declare (xargs :guard t)) (if (and (consp s) (consp (cdr-t s))) (cadr s) nil))
(defun ms-vals (s) (declare (xargs :guard t)) (car-t (drop-n 2 s)))
(defun ms-is (s) (declare (xargs :guard t)) (car-t (drop-n 3 s)))
(defun ms-ctrl (s) (declare (xargs :guard t)) (car-t (drop-n 4 s)))
(defun ms-status (s) (declare (xargs :guard t)) (car-t (drop-n 5 s)))

(defun ms-with-status (st s)
  (declare (xargs :guard t))
  (ms (ms-store s) (ms-frame s) (ms-vals s) (ms-is s) (ms-ctrl s) st))

; Control entries: (:L n is0 v r) (:H n catches v r) (:F n f v r); V and R
; are the operand stack and the continuation of the enclosing block, F the
; enclosing frame.
(defun entry-kind (e) (declare (xargs :guard t)) (if (consp e) (car-t e) nil))
(defun entry-n (e) (declare (xargs :guard t)) (car-t (drop-n 1 e)))
(defun entry-x (e) (declare (xargs :guard t)) (car-t (drop-n 2 e)))
(defun entry-v (e) (declare (xargs :guard t)) (car-t (drop-n 3 e)))
(defun entry-r (e) (declare (xargs :guard t)) (car-t (drop-n 4 e)))

; ---------------------------------------------------------------------------
; The abstraction: machine state -> spec configuration.

(defun admin-term (kind n x body)
  (declare (xargs :guard t))
  (case kind
    (:L (list :label_%{%}% n x body))
    (:H (list :handler_%{%}% n x body))
    (t  (list :frame_%{%}% n x body))))

(defun abs-ctrl (ctrl cur fr)           ; -> (mv instrs frame)
  (declare (xargs :guard t))
  (if (atom ctrl)
      (mv cur fr)
    (let* ((e (car ctrl))
           (k (entry-kind e))
           (term (admin-term k (entry-n e) (if (eq k :f) fr (entry-x e)) cur))
           (cur (rev-onto (entry-v e) (cons term (entry-r e))))
           (fr (if (eq k :f) (entry-x e) fr)))
      (abs-ctrl (cdr ctrl) cur fr))))

(defun machine-abs (s)
  (declare (xargs :guard t))
  (mv-let (instrs fr)
    (abs-ctrl (ms-ctrl s) (rev-onto (ms-vals s) (ms-is s)) (ms-frame s))
    (list :|%;%| (list :|%;%| (ms-store s) fr) instrs)))

; The loader: a spec configuration as a machine state (MACHINE-ABS gives it back).
(defun ms-of-config (c)
  (declare (xargs :guard t))
  (let* ((z (car-t (drop-n 1 c))) (instrs (car-t (drop-n 2 c))))
    (ms (car-t (drop-n 1 z)) (car-t (drop-n 2 z)) nil instrs nil :run)))

; ---------------------------------------------------------------------------
; The rule table, read from the relation functions of the spec.

(defun rule-fn-p (fn)
  (declare (xargs :mode :program))
  (and (symbolp fn)
       (equal (symbol-package-name fn) "W3T")
       (search "/R-" (symbol-name fn))))

(mutual-recursion
 (defun rule-calls (term)
   (declare (xargs :mode :program))
   (cond ((or (atom term) (eq (car term) 'quote)) nil)
         ((consp (car term))             ; ((lambda formals body) . args)
          (append (rule-calls-list (cdr term)) (rule-calls (caddr (car term)))))
         (t (append (and (rule-fn-p (car term)) (list (car term)))
                    (rule-calls-list (cdr term))))))
 (defun rule-calls-list (terms)
   (declare (xargs :mode :program))
   (if (atom terms) nil
     (append (rule-calls (car terms)) (rule-calls-list (cdr terms))))))

(defun rule-id (fn)                    ; "BINOP-VAL"
  (declare (xargs :mode :program))
  (let* ((s (symbol-name fn)) (i (search "/R-" s :from-end t)))
    (subseq s (+ i 3) (length s))))

; how APPLY-RULE calls the function: :pure (instr list), :read or :step
; (configuration; :step returns a configuration)
(defun rule-kind (fn)
  (declare (xargs :mode :program))
  (let ((s (symbol-name fn)))
    (cond ((equal (subseq s 0 (min 10 (length s))) "STEP_PURE/") :pure)
          ((equal (subseq s 0 (min 16 (length s))) "STEP_READ/SPLIT/") :read)
          (t :step))))

; what the redex of a rule is: (:entry :l), (:entry :h), (:entry :f),
; :anyprefix (val* TRAP instr*), or (:op KEYWORD) for val^k instr
(defun rule-place (fn)
  (declare (xargs :mode :program))
  (let* ((id (rule-id fn)))
    (cond ((member-equal id '("TRAP-INSTRS" "THROW_REF-INSTRS")) :anyprefix)
          ((search "HANDLER" id) '(:entry :h))
          ((search "LABEL" id) '(:entry :l))
          ((search "FRAME" id) '(:entry :f))
          (t (let* ((dash (search "-" id))
                    (op (if dash (subseq id 0 dash) id))
                    (op (if (equal op "IF") "IFELSE" op)))
               (list :op (intern op "KEYWORD")))))))

(defconst *skipped-step-rules*            ; the context rules and the two that call the others
  '(w3t::step/r-pure w3t::step/r-read w3t::step/r-ctxt-instrs w3t::step/r-ctxt-label
    w3t::step/r-ctxt-handler w3t::step/r-ctxt-frame))

(defun rules-in-step-order (wrld)
  (declare (xargs :mode :program))
  (let ((pure (rule-calls (getpropc 'w3t::step_pure 'acl2::unnormalized-body nil wrld)))
        (read (rule-calls (getpropc 'w3t::step_read/split 'acl2::unnormalized-body nil wrld)))
        (step (set-difference-eq
               (rule-calls (getpropc 'w3t::step 'acl2::unnormalized-body nil wrld))
               *skipped-step-rules*)))
    (append pure read step)))

(defun place-alist (rules acc)          ; place -> rules, in STEP's order
  (declare (xargs :mode :program))
  (if (atom rules) acc
    (let* ((p (rule-place (car rules)))
           (old (cdr (assoc-equal p acc))))
      (place-alist (cdr rules) (put-assoc-equal p (append old (list (car rules))) acc)))))

(defun apply-rule-cases (rules)
  (declare (xargs :mode :program))
  (if (atom rules) nil
    (let ((f (car rules)))
      (cons `(,f ,(case (rule-kind f)
                    (:pure `(let ((r (ec-call (,f redex)))) (if (consp r) (mv t z (car r)) (mv nil z nil))))
                    (:read `(let ((r (ec-call (,f (list :|%;%| z redex))))) (if (consp r) (mv t z (car r)) (mv nil z nil))))
                    (t `(let ((r (ec-call (,f (list :|%;%| z redex)))))
                          (if (consp r)
                              (mv t (car-t (drop-n 1 (car r))) (car-t (drop-n 2 (car r))))
                            (mv nil z nil))))))
            (apply-rule-cases (cdr rules))))))

(make-event
 (let* ((rules (rules-in-step-order (w state))))
   `(progn
      (defconst *step-rules* ',rules)
      (defconst *rule-places* ',(place-alist rules nil))
      ; (mv fired z' instrs'): rule FN on the redex REDEX in state Z
      (defun apply-rule (fn z redex)
        (declare (xargs :guard t))
        (case fn
          ,@(apply-rule-cases rules)
          (otherwise (mv nil z nil))))
      (in-theory (disable apply-rule)))))

(defun rules-for (place)
  (declare (xargs :guard t))
  (cdr-t (assoc-equal place *rule-places*)))

; the first rule of RULES that fires: (mv fired z' instrs')
(defun try-rules (rules z redex)
  (declare (xargs :guard t))
  (if (atom rules)
      (mv nil z nil)
    (mv-let (ok z2 res) (apply-rule (car rules) z redex)
      (if ok (mv t z2 res) (try-rules (cdr rules) z redex)))))

; ---------------------------------------------------------------------------
; How many operands an instruction takes (the K of its redex val^K instr),
; or NIL if the machine does not support it. The arities that depend on
; types are computed with the spec's own functions.

(defun functype-params (ft)            ; ($blocktype_ z bt) is (:%->_%% t1* () t2*)
  (declare (xargs :guard t))
  (car-t (drop-n 1 ft)))

(defun func-params (store a)            ; parameters of function address A
  (declare (xargs :guard t))
  (let* ((fi (nth-t a (wrt::%get-field store :funcs)))
         (ex (ec-call (w3t::expand (wrt::%get-field fi :type)))))
    (car-t (drop-n 1 (car-t ex)))))         ; (:FUNC%-> t1* t2*)

(defun redex-arity (i z vals)
  (declare (xargs :guard t))
  (case (entry-kind i)
    ((:unreachable :nop :local.get :global.get :call :call_indirect :memory.size :ref.null :ref.func
      :data.drop :elem.drop) 0)
    ((:drop :ifelse :br_if :br_table :local.tee :local.set :global.set
      :unop :testop :cvtop :load :memory.grow :ref.cast
      :ref.is_null :ref.as_non_null :br_on_null :br_on_non_null :table.get :throw_ref) 1)
    ((:binop :relop :store :ref.eq :table.set :table.grow) 2)
    ((:select :memory.fill :memory.copy :memory.init :table.fill :table.copy :table.init) 3)
    ((:block :loop :try_table)
     (len-t (functype-params (ec-call (w3t::$blocktype_ z (entry-n i))))))
    (:throw                               ; the parameters of the tag's type, as Step/throw
     (let ((ex (ec-call (w3t::expand (ec-call (w3t::$as_deftype
                                               (wrt::%get-field (ec-call (w3t::$tag z (entry-n i))) :type)))))))
       (len-t (car-t (drop-n 1 (car-t ex))))))
    (:call_ref
     (let ((ref (car-t vals)))
       (if (eq (entry-kind ref) :ref.func_addr)
           (let ((a (entry-n ref)))
             (if (natp a)
                 (1+ (len-t (func-params (car-t (drop-n 1 z)) a)))
               nil))
         1)))
    (otherwise nil)))
;
; ---------------------------------------------------------------------------
; One step.

(defun value-instr-p (i)
  (declare (xargs :guard t))
  (and (consp i) (ec-call (w3t::val-p i)) t))

(defun admin-kind (i)                   ; :L :H :F for an administrative term
  (declare (xargs :guard t))
  (case (entry-kind i)
    (:label_%{%}% :l) (:handler_%{%}% :h) (:frame_%{%}% :f) (otherwise nil)))

(defun ms-z (s)                         ; the spec state (store; frame)
  (declare (xargs :guard t))
  (list :|%;%| (ms-store s) (ms-frame s)))

; Enter the administrative term at the head of IS: push its control entry.
; The machine enters only a term of the shape (kind n x body) that
; MACHINE-ABS rebuilds: N a natural, BODY a true list, and X (the label's
; continuation, the handler's catch clauses) a true list; any other term
; makes it stuck. Step/ctxt-label and Step/ctxt-handler ask the same of X
; before they step the body (plan2.md V3: a handler whose clauses were not a
; true list was entered, and the specification does not step under it).
(defun enterable-p (i)
  (declare (xargs :guard t))
  (and (admin-kind i) (true-listp i) (equal (len-t i) 4)
       (natp (entry-n i)) (true-listp (entry-v i))
       (or (eq (admin-kind i) :f) (true-listp (entry-x i)))))

(defun enter-step (s)
  (declare (xargs :guard t))
  (let* ((i (car-t (ms-is s))) (k (admin-kind i))
         (n (entry-n i)) (x (entry-x i)) (body (entry-v i))
         (e (list k n (if (eq k :f) (ms-frame s) x) (ms-vals s) (cdr-t (ms-is s)))))
    (if (enterable-p i)
        (ms (ms-store s) (if (eq k :f) x (ms-frame s)) nil body (cons e (ms-ctrl s)) :run)
      (ms-with-status :stuck s))))

; Leave the innermost control entry: rebuild its administrative term with
; the current block inside, and apply the rules whose redex is that term.
(defun exit-step (s)
  (declare (xargs :guard t))
  (let* ((e (car-t (ms-ctrl s))) (k (entry-kind e))
         (term (admin-term k (entry-n e) (if (eq k :f) (ms-frame s) (entry-x e))
                           (rev-onto (ms-vals s) (ms-is s))))
         (outer-frame (if (eq k :f) (entry-x e) (ms-frame s))))
    (mv-let (ok z2 res)
      (try-rules (rules-for (list :entry k)) (list :|%;%| (ms-store s) outer-frame) (list term))
      (if ok
          (ms (car-t (drop-n 1 z2)) (car-t (drop-n 2 z2)) (entry-v e)
              (app res (entry-r e)) (cdr-t (ms-ctrl s)) :run)
        (ms-with-status :stuck s)))))

; A rule on the whole block: TRAP or THROW_REF among other values and
; instructions (TRAP-INSTRS, THROW_REF-INSTRS).
(defun anyprefix-step (s)
  (declare (xargs :guard t))
  (mv-let (ok z2 res)
    (try-rules (rules-for :anyprefix) (ms-z s) (rev-onto (ms-vals s) (ms-is s)))
    (if (and ok (true-listp res))
        (ms (car-t (drop-n 1 z2)) (car-t (drop-n 2 z2)) nil res (ms-ctrl s) :run)
      (ms-with-status :stuck s))))

; An instruction with K operands: the rules of its opcode on val^K instr.
(defun op-step (s)
  (declare (xargs :guard t))
  (let* ((i (car-t (ms-is s))) (vals (ms-vals s))
         (rules (rules-for (list :op (entry-kind i))))
         (k (redex-arity i (ms-z s) vals)))
    (cond ((or (atom rules) (not (natp k))) (ms-with-status :unsupported s))
          ((< (len-t vals) k) (ms-with-status :stuck s))
          (t (mv-let (ok z2 res)
               (try-rules rules (ms-z s) (rev-onto (take-n k vals) (list i)))
               (if ok
                   (ms (car-t (drop-n 1 z2)) (car-t (drop-n 2 z2)) (drop-n k vals)
                       (app res (cdr-t (ms-is s))) (ms-ctrl s) :run)
                 (ms-with-status :stuck s)))))))

(defun exit-instr-p (i)                 ; leaves the innermost entry
  (declare (xargs :guard t))
  (sym-member (entry-kind i) '(:br :return :trap :throw_ref)))

(defun machine-step (s)
  (declare (xargs :guard t))
  (if (not (eq (ms-status s) :run))
      s
    (let ((is (ms-is s)) (vals (ms-vals s)) (ctrl (ms-ctrl s)))
      (if (atom is)
          (if (atom ctrl) (ms-with-status :done s) (exit-step s))
        (let ((i (car-t is)))
          (cond ((value-instr-p i)
                 (ms (ms-store s) (ms-frame s) (cons i vals) (cdr-t is) ctrl :run))
                ((admin-kind i) (enter-step s))
                ((and (eq (entry-kind i) :throw_ref) (eq (entry-kind (car-t vals)) :ref.null))
                 (op-step s))                ; THROW_REF-NULL: val^1 throw_ref
                ((and (sym-member (entry-kind i) '(:trap :throw_ref))
                      (or (consp (cdr-t is))
                          (if (eq (entry-kind i) :trap) (consp vals) (consp (cdr-t vals)))))
                 (anyprefix-step s))
                ((and (equal i '(:trap)) (atom ctrl)) (ms-with-status :trap s))
                ((and (equal i '(:throw_ref)) (atom ctrl) (eq (entry-kind (car-t vals)) :ref.exn_addr))
                 (ms-with-status :throw s))       ; an uncaught exception
                ((and (exit-instr-p i) (consp ctrl)) (exit-step s))
                ((exit-instr-p i) (ms-with-status :stuck s))
                (t (op-step s))))))))

; How many spec steps the next machine step stands for (E3's M-CLOCK): 0
; when the step only moves a value, enters a control entry or stops the
; machine (MACHINE-ABS is unchanged), else 1.
(defun machine-clock (s)
  (declare (xargs :guard t))
  (if (or (not (eq (ms-status s) :run))
          (not (eq (ms-status (machine-step s)) :run)))
      0
    (let ((is (ms-is s)))
      (cond ((atom is) 1)
            ((value-instr-p (car-t is)) 0)
            ((admin-kind (car-t is)) 0)
            (t 1)))))

(defun machine-running (s) (declare (xargs :guard t)) (eq (ms-status s) :run))
(defun machine-result-p (s) (declare (xargs :guard t)) (sym-member (ms-status s) '(:done :trap :throw)))

; Run with fuel N
(defun machine-run (n s)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (not (machine-running s)))
      s
    (machine-run (1- n) (machine-step s))))
