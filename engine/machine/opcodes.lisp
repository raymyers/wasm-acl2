; License: MIT. See the file LICENSE at the top of the repository.
;
; The table of proved opcodes (plan/wasm-engine/plan2.md V5 item 4, decision
; P3): the heads on which OP-STEP tries a rule. It is computed from the
; machine's own tables: a head is in it when the rule table has a rule of
; that opcode (RULES-FOR) and REDEX-ARITY gives it an operand count.
;   - OP-STEP-OUTSIDE-PROVED-OPCODES: on any other head OP-STEP ends
;     :unsupported and tries no rule.
;   - MACHINE-STEP-OUTSIDE-PROVED-OPCODES: so does MACHINE-STEP, when the
;     head is not a value, not an administrative term and not one of BR,
;     RETURN, TRAP, THROW_REF (whose rules are those of a control entry or of
;     the whole block).
; Constraint C2 is proved for every head of the table and for those other
; steps (spec-result.lisp), with no opcode excluded, so the proved set is the
; supported set. The table contains the opcodes of D5 (plan.md) that are the
; head of an OP-STEP redex, and MEMORY.INIT, DATA.DROP and REF.NULL, which
; every instantiation runs (notes/V0-ground.md); the last event checks it.
(in-package "WE")
(include-book "ok")

(set-prover-step-limit 2000000)

(defun op-heads (places)
  (declare (xargs :mode :program))
  (cond ((atom places) nil)
        ((and (consp (caar places)) (eq (car (caar places)) :op)
              (consp (cdar places))
              (redex-arity (list (cadr (caar places))) nil nil))
         (cons (cadr (caar places)) (op-heads (cdr places))))
        (t (op-heads (cdr places)))))

; REDEX-ARITY calls spec functions outside their guards on the empty state
; given here; the count is not used, only that there is one.
(make-event
 (with-guard-checking :none
   `(defconst *proved-opcodes* ',(op-heads *rule-places*))))

(defthm op-step-outside-proved-opcodes
  (implies (not (member-equal (entry-kind (car-t (ms-is s))) *proved-opcodes*))
           (equal (op-step s) (ms-with-status :unsupported s)))
  :hints (("Goal" :in-theory (enable op-step redex-arity))))

(defthm machine-step-outside-proved-opcodes
  (implies (and (equal (ms-status s) :run)
                (consp (ms-is s))
                (not (value-instr-p (car (ms-is s))))
                (not (admin-kind (car (ms-is s))))
                (not (exit-instr-p (car (ms-is s))))
                (not (member-equal (entry-kind (car (ms-is s))) *proved-opcodes*)))
           (equal (machine-step s) (ms-with-status :unsupported s)))
  :hints (("Goal" :in-theory (enable machine-step exit-instr-p))))

; The census: the table is the recorded one in size, and holds D5 (the
; opcodes of fast/frame.lisp's *d5-opcodes* but BR and RETURN, which are not
; heads of an OP-STEP redex) and the three opcodes of instantiation.
(make-event
 (let ((d5 '(:unreachable :nop :drop :select :ifelse :block :loop :br_if :br_table
             :call :call_indirect :call_ref :local.get :local.set :local.tee
             :global.get :global.set :load :store :memory.size :memory.grow
             :memory.copy :memory.fill :unop :binop :testop :relop :cvtop
             :try_table :throw :throw_ref :table.get :ref.cast))
       (inst '(:memory.init :data.drop :ref.null)))
   (prog2$
    (cw "PROVED-OPCODES-CENSUS ~x0 opcodes; D5 missing ~x1; instantiation missing ~x2~%"
        (len *proved-opcodes*)
        (set-difference-eq d5 *proved-opcodes*)
        (set-difference-eq inst *proved-opcodes*))
    (if (and (equal (len *proved-opcodes*) 48)
             (subsetp-eq d5 *proved-opcodes*)
             (subsetp-eq inst *proved-opcodes*))
        '(value-triple :proved-opcodes-census-ok)
      (er hard 'proved-opcodes "the table of proved opcodes is not the recorded one")))))
