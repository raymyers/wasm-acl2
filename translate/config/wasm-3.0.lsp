; il2acl2 configuration for WASM 3.0 (wasm3 M0: checked in with the IL and
; validated against it on every run; config-entry-errors). The counted,
; named exceptions to the generic translation (plan §1 "Rules of the game").
; Keep this list short; each entry says why the IL cannot be translated
; mechanically. History: it began as the 1.0 config without the 1.0-only
; :il-patch (Bmodule) and :rel-override (Module_ok) entries (prep P2);
; ("bytes_" . "inv_bytes_") went in P2 (no bytes_ here); since P3 the
; inverse pairs come from hint(inverse) in the IL (no :inverse entry).
(
 (:def "utf8" :inverse "inv_utf8"
  :reason "Clauses 2-4 define the bytes b_1..b_4 only through an arithmetic equation on ch (the inverse direction); no matching/binding translation exists. Hand-written in rt/builtins.lisp, with its inverse inv_utf8 (used to solve utf8(x) = bytes in Bname; the other inverse pairs come from hint(inverse) in the IL).")

 (:def "utf8single"
  :reason "Like utf8 (S5): each clause defines the bytes of one character only through an arithmetic equation on ch (ch = 2^6*(b_1 - 0xC0) + $cont(b_2), ...), the inverse direction, so there is no matching translation. Hand-written in rt/builtins-3.0.lisp from the same four clauses (no result for a surrogate or above U+10FFFF). 3.0 defines $utf8 through it, but the utf8 override above replaces that definition, so no generated code calls $utf8single today; the override removes the last stub of a numeric def (wasm3 M1).")

 (:builtins "categories"
  :choice ("ND" "R_fmadd" "R_fmin" "R_fmax" "R_idot" "R_idot_add" "R_iq15mulr"
           "R_trunc_u" "R_trunc_s" "R_swizzle" "R_laneselect")
  :host ("hostcall")
  :numeric ("s33_to_u32")
  :reason "Clause-less defs that are not plain numeric builtins (S7): $ND and the $R_* relaxed-SIMD parameters are nondeterminism choices (fixed by the D4 policy, 3.0-numerics.relaxed.spectec); $hostcall is the host-function hook (4.0-execution.configurations). $s33_to_u32 (3.1-numerics.scalar) is declared without hint(builtin) but is a numeric conversion, so it is listed as :numeric.")

 (:split "Step" "ctxt-instrs"
  :strategy :redex
  :reason "The generic split search of val* ++ admininstr* ++ admininstr_1* is exponential when it fails. Strategy: admininstr* ends right after the first non-value; val* is searched from longest to shortest. Completeness vs. the generic search: T8 obligation.")

 (:decreasing "termination order"
  :pairs (("Instr_ok" . 1) ("Instrs_ok" . 1) ("Step" 0 2) ("Ref_ok" . 1) ("Types_ok" . 1) ("Globals_ok" . 1))
  :reason "Instruction typing recurses into sub-instructions under an EXTENDED context (block/loop/if add a label), so the size of all inputs can grow. The instruction component (index 1) decreases, or stays equal with a smaller stack (frame). Recursive premise calls are ordered lexicographically by (size of component 1, size of all inputs). Step (wasm3 M3): the pair (\"Step\" 0 2) names the instructions of the configuration (:|%;%| state instrs). Every Step rule with a Step premise (ctxt-instrs, ctxt-label, ctxt-handler, ctxt-frame) steps a proper part of the instruction list, so this component decreases in every derivation and no derivation is cut. Without it the check compared the size of the whole configuration, store included: measured 5.39 ms per step with one 64 KiB page in the store against 0.014 ms without (notes M3-execution). Ref_ok (wasm3 M4): the reference (component 1) decreases in Ref_ok/extern (REF.EXTERN ref to ref) and is equal in Ref_ok/sub, where all inputs then decrease. Without it, the output variant Ref_ok/SPLIT, which calls the check variant Ref_ok with the known type REF ANY as a third input, failed the size check (that input made the callee larger), so no externref had a type and $invoke rejected every externref argument (found by the wasm3 M4 conformance run). Types_ok and Globals_ok (wasm3 M7): /cons recurses on the rest of the list (component 1, strictly smaller) under a context extended by the new defined types or global types, which made all inputs larger, so the size check cut every list of two or more and no module with a type or a global validated (found by running the Module_ok proposer on the spectest module).")

 (:memoize "search memo" :recursive nil
  :rels ("Instr_ok" "Instrs_ok")
  :reason "Performance only (memoization is semantically the identity). Instrs_ok/seq splits instr_1* instr_2* at every point and recurses on both halves, so REJECTING an ill-typed sequence explores exponentially many derivations (17 instructions: ~60 s). Memoizing the typing functions on hons-copied arguments makes the search polynomial (sub-sequences x stacks). 3.0 adds :recursive nil: memoize wraps the compiled function instead of recompiling its body (the memoized function R/%M recurses only through its entry R, which calls the memoized R/%M, so recursive calls are still memoized); with the default the four memoize events of 2_3-validation_instructions took 22 s at every include of that book (12 books include it), measured in wasm3 M0.")

 (:sized "||BX||"
  :pairs (("Bsection_" . "len") ("Bcode" . "len"))
  :reason "The source premise `len = ||BX||` (byte length of what BX matched) elaborates to `len = 0` in the IL, which would reject every non-empty section. In these grammars the item after `len` is parsed from exactly `len` bytes instead, and the `len = 0` premise is dropped.")
 (:witness "single-witness premises"
  :rels ("Ref_ok" "Externaddr_ok")
  :reason "wasm3 M6: Instr_ok and Instrs_ok left this entry; with the option C sequencer they are check relations and no premise takes a value from their output variants. The output variant R/SPLIT of these relations drops rules whose output is not computable from the inputs, and some premise takes a value from it and then constrains it, so that premise tries ONE witness (the translator reports any other such premise as an error, `witness choice`; that is how Heaptype_sub/trans is dropped instead of compiled with one arbitrary heaptype'). PROVISIONAL, carried over from WASM 1.0 and not yet argued for 3.0: the premises are Instr_ok/block, loop, if, try_table and Instrs_ok/seq, sub (they take an instruction type from Instr_ok/SPLIT or Instrs_ok/SPLIT, which drop the stack-polymorphic rules and, in 3.0, the subsumption and frame rules), and Ref_ok/sub, Externaddr_ok/sub (they take the type from the relation's own output variant, which drops only `sub`, and then check subtyping; complete if the other rules give one type and subtyping is transitive). Whether one witness is enough for instruction typing under 3.0 subsumption is the go/no-go of wasm3 M6.")

 (:fuel "type validation and subtyping"
  :rels ("Heaptype_ok")
  :reason "The rec group of Heaptype_ok (19 relations: type validation and subtyping) terminates by a depth bound, (%TFUEL) in rt/prelude.lisp, instead of the generated check that every recursive premise has smaller inputs. That check cut valid derivations: a rule that passes its arguments unchanged to another relation of the group (Valtype_sub/ref to Reftype_sub), one that replaces a type index by the defined type (Heaptype_sub/typeidx-l), one that recurses under a larger context (Deftype_ok). Measured: 9 of 22 type cases right with the size check (wasm3 notes, review-checker-blind-spots). A derivation deeper than the bound is not found; a failing search through a cyclic context ends at the bound.")

 (:logic "time-limited attempts" :seconds 20
  :reason "wasm3 M9 (replaces the :program entry of M0): every generated event goes through %TRY-LOGIC-T / %TRY-GUARDS-T (rt/builtins-3.0.lisp): logic mode and guard verification are tried as for 1.0 (%TRY-LOGIC: step limits and the same alternatives), and each attempt also has a prover time limit of :seconds, because the step limits do not bound wall time (one 3.0 guard proof ran more than 15 minutes, prep P5). An attempt that hits a limit falls back (program mode, or guards not verified). The time limit makes the result depend on the machine; tests/sem-3.0/modes-3.0.lsp records it.")

 (:il-patch "Belem"
  :old (list (iter (case "REF.FUNC" (var "y")) list (dom "y" (var "y*"))))
  :new (iter (list (case "REF.FUNC" (var "y"))) list (dom "y" (var "y*")))
  :reason "Elaboration of the source `ELEM rt (REF.FUNC y)* ...` (flags 0-3): the element list has type expr* = (instr*)*, and SpecTec coerces the whole instr* `(REF.FUNC y)*` into a one-element list, [(REF.FUNC y)*]: ONE expression holding every ref.func. The binary format (prose) and flags 4-7 give one expression per element, [REF.FUNC y]*. Unpatched, a decoded segment with n functions has 1 element of n instructions, which Elem_ok rejects and instantiation would get wrong. The patch writes the iteration of the singleton list (all 4 rules; 2.0's IL has the same shape). Found in wasm3 M2.")

 (:keep-variant "Instr_ok" :out 2
  :reason "For the instruction-typing sequencer of option C (wasm3 M6, user decision 2026-11-14): INSTR_OK/OUT2 (C, instr) gives the principal type a ->_(x*) b of an instruction whose type its operands do not decide. It is kept although it leaves out the rules whose type is not computable from the instruction (the stack-polymorphic ones: unreachable, select, br, br_table, return, the return_calls, throw, throw_ref, and those whose operand types are free, listed in the header): the sequencer handles those by a table and checks every proposal with the generated INSTR_OK in check mode, so a left-out rule can cost completeness, never soundness.")

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
   (defun seq-nullable (rt)
     ;; (ref null ht) for the stack top (ref null? ht); bottom: (ref null bot)
     (if (and (consp rt) (eq (car rt) :ref)) (list :ref (quote ((:null))) (caddr rt)) (quote (:ref ((:null)) (:bot)))))
   (defun seq-null-like (rt ht)
     (if (and (consp rt) (eq (car rt) :ref)) (list :ref (cadr rt) ht) (list :ref (quote ((:null))) ht)))
   (defun seq-label (c l) (nth l (%get-field c :labels)))
   (defun seq-stack-or-bot (stk k)
     ;; the k values below the top, bottom first, BOT where the (polymorphic)
     ;; stack has none: br_table's operands, checked against every label
     (if (zp k) nil (append (seq-stack-or-bot (cdr stk) (1- k)) (list (if (consp stk) (car stk) (quote (:bot)))))))
   (defun seq-top-ht (c ht)
     ;; the top heap type of the hierarchy of HT (for the operand of ref.test
     ;; and ref.cast, which must be a supertype of the cast type)
     (cond ((not (consp ht)) (quote (:any)))
           ((member-eq (car ht) (quote (:func :nofunc))) (quote (:func)))
           ((member-eq (car ht) (quote (:extern :noextern))) (quote (:extern)))
           ((member-eq (car ht) (quote (:exn :noexn))) (quote (:exn)))
           ((member-eq (car ht) (quote (:any :eq :i31 :struct :array :none))) (quote (:any)))
           (t (let* ((dt (if (eq (car ht) :_idx) (nth (cadr ht) (%get-field c :types)) ht))
                     (ct (car (expand dt))))
                (if (and (consp ct) (eq (car ct) :func%->%)) (quote (:func)) (quote (:any)))))))
   (defun seq-top-ref (c rt) (list :ref (quote ((:null))) (seq-top-ht c (caddr rt))))
   (defun seq-typeuse-dt (c tu)
     ;; the deftype of a typeuse: (_IDX x) is C.TYPES[x]
     (if (and (consp tu) (eq (car tu) :_idx)) (nth (cadr tu) (%get-field c :types)) tu))
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
         (:br_table (list (append (seq-stack-or-bot (cdr stk) (len (seq-label c (caddr i)))) (list (quote (:i32)))) nil))
         (:return (list (car (%get-field c :return)) nil))
         (:return_call (list (seq-params (nth (cadr i) (%get-field c :funcs))) nil))
         (:return_call_ref (list (append (seq-params (seq-typeuse-dt c (cadr i)))
                                         (list (list :ref (quote ((:null))) (cadr i))))
                                 nil))
         (:return_call_indirect (list (append (seq-params (seq-typeuse-dt c (caddr i)))
                                              (list (car (nth (cadr i) (%get-field c :tables)))))
                                      nil))
         (:throw (list (seq-params (nth (cadr i) (%get-field c :tags))) nil))
         (:throw_ref (list (list (quote (:ref ((:null)) (:exn)))) nil))
         (:ref.is_null (list (list (seq-nullable top)) (list (quote (:i32)))))
         (:ref.as_non_null (list (list (seq-nullable top)) (list (seq-nonnull (seq-nullable top)))))
         (:br_on_null (list (append (seq-label c (cadr i)) (list (seq-nullable top)))
                            (append (seq-label c (cadr i)) (list (seq-nonnull (seq-nullable top))))))
         (:ref.test (list (list (seq-top-ref c (cadr i))) (list (quote (:i32)))))
         (:ref.cast (list (list (seq-top-ref c (cadr i))) (list (cadr i))))
         (:any.convert_extern (list (list (seq-null-like top (quote (:extern)))) (list (seq-null-like top (quote (:any))))))
         (:extern.convert_any (list (list (seq-null-like top (quote (:any)))) (list (seq-null-like top (quote (:extern))))))
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
                          (append xs x) (or p2 poly)))))))))
   (defun instrs_ok (c is ty)
     (let ((t1 (cadr ty)) (x (caddr ty)) (t2 (cadddr ty)))
       (mv-let (ok stk xs poly) (seq-run c is (reverse t1) nil nil)
         (and ok
              (if poly (<= (len stk) (len t2)) (equal (len stk) (len t2)))
              (resulttype_sub c (reverse stk) (nthcdr (- (len t2) (len stk)) t2))
              (subsetp-equal x xs)
              t)))))
  :reason "Option C of wasm3 M6 (user decision 2026-11-14): the five structural rules of Instrs_ok (empty, instr, seq, sub, frame) are replaced by a hand-written sequencer; every instruction type it proposes is checked by the generated INSTR_OK and every pop by the generated RESULTTYPE_SUB, so its mistakes can cost completeness, not soundness. Subsumption has no mechanical reading in the generated rules (notes M6-instruction-typing-strategy). Proposals come from the kept variant INSTR_OK/OUT2 (config :keep-variant), plus a table for the 18 rules it leaves out; The table also covers return_call_ref and return_call_indirect. Measured: 24 of 24 V8 cases (notes M6-typing-cases, 16 without).")

 (:il-patch "Instr_ok" :old (iter (var "x") list (dom "x" (var "x*"))) :new (list)
  :reason "wasm3 M6 step 3, mechanism (b), chosen by Claude within option C and listed for the user (the alternative is (a), sub-component output positions): Instr_ok/block, loop and try_table call Instrs_ok with x* = [] instead of an unbound x*, so the premise is a check with every type given. Equivalent: Instrs_ok/sub with Instrtype_sub (fewer initialized locals is a supertype) derives t_1* ->_[] t_2* from any t_1* ->_(x*) t_2*, and the conclusions do not use x*. The term occurs only in these premises of Instr_ok.")
 (:il-patch "Instr_ok" :old (iter (var "x_1") list (dom "x_1" (var "x_1*"))) :new (list)
  :reason "As the x* entry above, for the then branch of Instr_ok/if (x_1*).")
 (:il-patch "Instr_ok" :old (iter (var "x_2") list (dom "x_2" (var "x_2*"))) :new (list)
  :reason "As the x* entry above, for the else branch of Instr_ok/if (x_2*).")

 (:given-entry "Module_ok" :given ("C" "C'")
  :defuns
  ((defun mo-ctx (types tags globals mems tables funcs datas elems refs)
     (list :%rec (cons :types types) (cons :tags tags) (cons :globals globals) (cons :mems mems)
           (cons :tables tables) (cons :funcs funcs) (cons :datas datas) (cons :elems elems)
           (list :locals) (list :labels) (list :return) (cons :refs refs) (list :recs)))
   (defun mo-map (rel c xs)
     ;; the outputs of a :fun relation (IMPORT_OK, TAG_OK, MEM_OK, TABLE_OK) on each x
     (if (atom xs) nil
       (cons (car (case rel (:import (import_ok c (car xs))) (:tag (tag_ok c (car xs)))
                    (:mem (mem_ok c (car xs))) (t (table_ok c (car xs)))))
             (mo-map rel c (cdr xs)))))
   (defun mo-func-types (funcs dts)
     ;; dt = C.TYPES[x] for each FUNC x local* expr (Func_ok's output, read off the syntax)
     (if (atom funcs) nil (cons (nth (cadr (car funcs)) dts) (mo-func-types (cdr funcs) dts))))
   (defun mo-elem-types (elems)
     ;; rt for each ELEM rt e* mode (Elem_ok's output)
     (if (atom elems) nil (cons (cadr (car elems)) (mo-elem-types (cdr elems)))))
   (defun mo-oks (datas) (if (atom datas) nil (cons (list :ok) (mo-oks (cdr datas)))))
   (defun module_ok (m)
     (let* ((types (nth 1 m)) (imports (nth 2 m)) (tags (nth 3 m)) (globals (nth 4 m))
            (mems (nth 5 m)) (tables (nth 6 m)) (funcs (nth 7 m)) (datas (nth 8 m))
            (elems (nth 9 m)) (exports (nth 11 m))
            (dt1 (car (types_ok (mo-ctx nil nil nil nil nil nil nil nil nil) types)))
            (xti (mo-map :import (mo-ctx dt1 nil nil nil nil nil nil nil nil) imports))
            (dts (mo-func-types funcs dt1))
            (xs ($funcidx_nonfuncs (list globals mems tables elems exports)))
            (cp (mo-ctx dt1 nil ($globalsxt xti) nil nil (append ($funcsxt xti) dts) nil nil xs))
            (jts (mo-map :tag cp tags))
            (gts (car (globals_ok cp globals)))
            (mts (mo-map :mem cp mems))
            (tts (mo-map :table cp tables))
            (c (mo-ctx dt1 (append ($tagsxt xti) jts) (append ($globalsxt xti) gts)
                       (append ($memsxt xti) mts) (append ($tablesxt xti) tts)
                       (append ($funcsxt xti) dts) (mo-oks datas) (mo-elem-types elems) xs)))
       (module_ok/w m c cp))))
  :reason "wasm3 M7, proposer and checker (user decision 2026-11-15): the premises of Module_ok depend on each other through the contexts C' and C (notes M7-module-ok-strategy), so the rule is compiled in mode (:given \"C\" \"C'\") to MODULE_OK/W, which checks every premise, including the rule's own equations for C' and C, with them as inputs. This hand-written entry MODULE_OK (module) proposes them: the types by Types_ok, the import types by Import_ok, the five projections, x* by $funcidx_nonfuncs, the tags, globals, memories, tables by their generated relations, and dt* (C.TYPES[x]), ok* and rt* read off the syntax. A wrong proposal makes MODULE_OK/W reject; it cannot make it accept.")
)
