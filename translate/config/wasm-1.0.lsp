; il2acl2 configuration: the counted, named exceptions to the generic
; translation (plan §1 "Rules of the game"). Keep this list short; each entry
; says why the IL cannot be translated mechanically.
(
 (:def "utf8"
  :reason "Clauses 2-4 define the bytes b_1..b_4 only through an arithmetic equation on ch (the inverse direction); no matching/binding translation exists. Hand-written in rt/builtins.lisp.")

 (:split "Step" "ctxt-instrs"
  :strategy :redex
  :reason "The generic split search of val* ++ admininstr* ++ admininstr_1* is exponential when it fails. Strategy: admininstr* ends right after the first non-value; val* is searched from longest to shortest. Completeness vs. the generic search: T8 obligation.")

 (:inverse "hint(inverse)"
  :pairs (("signed_" . "inv_signed_") ("ibytes_" . "inv_ibytes_")
          ("fbytes_" . "inv_fbytes_") ("bytes_" . "inv_bytes_")
          ("utf8" . "inv_utf8"))
  :reason "SpecTec hint(inverse ...) annotations in 3-numerics.spectec; spectec --ast does not print hints. Used to solve f(a.., x) = v for x (load rules; Bname). inv_utf8 is the hand-written partner of the utf8 override.")

 (:il-patch "Bmodule"
  :old (seq (attr (case "%" (tup (num (nat 1)))) (var "Bu32")))
  :new (seq (num 0x01) (num 0x00) (num 0x00) (num 0x00))
  :reason "Bug in the SpecTec WASM 1.0 source (A-binary.spectec: `0x00 0x61 0x73 0x6D 1:Bu32`): the binary-format version is the fixed 4 bytes 0x01 0x00 0x00 0x00, not a LEB128 u32 (which encodes 1 as the single byte 0x01). Taken literally, no real .wasm file parses.")

 (:decreasing "termination order"
  :pairs (("Instr_ok" . 1) ("Instrs_ok" . 1))
  :reason "Instruction typing recurses into sub-instructions under an EXTENDED context (block/loop/if add a label), so the size of all inputs can grow. The instruction component (index 1) decreases, or stays equal with a smaller stack (frame). Recursive premise calls are ordered lexicographically by (size of component 1, size of all inputs).")

 (:memoize "search memo"
  :rels ("Instr_ok" "Instrs_ok")
  :reason "Performance only (memoization is semantically the identity). Instrs_ok/seq splits instr_1* instr_2* at every point and recurses on both halves, so REJECTING an ill-typed sequence explores exponentially many derivations (17 instructions: ~60 s). Memoizing the typing functions on hons-copied arguments makes the search polynomial (sub-sequences x stacks).")

 (:rel-override "Module_ok"
  :reason "Module_ok's context C = {TYPES ft'*, FUNCS ift* ft*, ...} contains ft*, the OUTPUT of the premises (Func_ok: C |- func : ft)*, which take C as input: a cycle no input/output mode can schedule. This override follows the rule premise by premise, calling the GENERATED relations (Type_ok, Import_ok, Global_ok, Table_ok, Mem_ok, Func_ok, Elem_ok, Data_ok, Start_ok, Export_ok, $disjoint_, $funcsxt ...). The cycle is broken with Func_ok's own output premise `C.TYPES[x] = ft`: ft is read from the type section, and every function is then CHECKED by the generated FUNC_OK against the full C."
  :defuns
  ((defun module_ok/%types (ts)                 ; (Type_ok: |- type : ft')*
     (if (atom ts) (list nil)
       (let ((r (type_ok (car ts))) (rest (module_ok/%types (cdr ts))))
         (and r rest (list (cons (car r) (car rest)))))))
   (defun module_ok/%imports (c ims)            ; (Import_ok: {TYPES ft'*} |- import : ixt)*
     (if (atom ims) (list nil)
       (let ((r (import_ok c (car ims))) (rest (module_ok/%imports c (cdr ims))))
         (and r rest (list (cons (car r) (car rest)))))))
   (defun module_ok/%globals (c gs)             ; (Global_ok: C' |- global : gt)*
     (if (atom gs) (list nil)
       (let ((r (global_ok/split c (car gs))) (rest (module_ok/%globals c (cdr gs))))
         (and r rest (list (cons (car r) (car rest)))))))
   (defun module_ok/%tables (c ts)              ; (Table_ok: C |- table : tt)*
     (if (atom ts) (list nil)
       (let ((r (table_ok c (car ts))) (rest (module_ok/%tables c (cdr ts))))
         (and r rest (list (cons (car r) (car rest)))))))
   (defun module_ok/%mems (c ms)                ; (Mem_ok: C |- mem : mt)*
     (if (atom ms) (list nil)
       (let ((r (mem_ok c (car ms))) (rest (module_ok/%mems c (cdr ms))))
         (and r rest (list (cons (car r) (car rest)))))))
   (defun module_ok/%func-types (fts1 fs)       ; ft = C.TYPES[x] (Func_ok's output premise)
     (if (atom fs) (list nil)
       (let ((x (cadr (car fs))) (rest (module_ok/%func-types fts1 (cdr fs))))
         (and (natp x) (< x (len fts1)) rest
              (list (cons (nth x fts1) (car rest)))))))
   (defun module_ok/%funcs-ok (c fs fts)        ; (Func_ok: C |- func : ft)*, checked
     (if (atom fs) t
       (and (func_ok c (car fs) (car fts))         ; the check variant (Func_ok is multi-mode)
            (module_ok/%funcs-ok c (cdr fs) (cdr fts)))))
   (defun module_ok/%elems-ok (c es)            ; (Elem_ok: C |- elem : OK)*
     (if (atom es) t (and (elem_ok c (car es)) (module_ok/%elems-ok c (cdr es)))))
   (defun module_ok/%datas-ok (c ds)            ; (Data_ok: C |- data : OK)*
     (if (atom ds) t (and (data_ok c (car ds)) (module_ok/%datas-ok c (cdr ds)))))
   (defun module_ok/%starts-ok (c ss)           ; (Start_ok: C |- start : OK)?
     (if (atom ss) t (and (start_ok c (car ss)) (module_ok/%starts-ok c (cdr ss)))))
   (defun module_ok/%exports (c es)             ; (Export_ok: C |- export : nm xt)*
     (if (atom es) (list nil)
       (let ((r (export_ok c (car es) (cadr (car es)))) (rest (module_ok/%exports c (cdr es))))
         (and r rest (list (cons (car r) (car rest)))))))
   (defun module_ok/%names (es)
     (if (atom es) nil (cons (cadr (car es)) (module_ok/%names (cdr es)))))
   (defun module_ok/%ctx (types funcs globals tables mems)
     (list :%rec (cons :types types) (cons :funcs funcs) (cons :globals globals)
           (cons :tables tables) (cons :mems mems) (cons :locals nil) (cons :labels nil) (cons :return nil)))
   ;; |- MODULE type* import* func* global* table* mem* elem* data* start? export* : ixt* -> xt*
   (defun module_ok (%a0)
     (if (not (and (consp %a0) (eq (car %a0) :module) (true-listp %a0) (equal (len %a0) 11)))
         nil
       (let* ((types (nth 1 %a0)) (imports (nth 2 %a0)) (funcs (nth 3 %a0))
              (globals (nth 4 %a0)) (tables (nth 5 %a0)) (mems (nth 6 %a0))
              (elems (nth 7 %a0)) (datas (nth 8 %a0)) (start (nth 9 %a0)) (exports (nth 10 %a0))
              (r1 (module_ok/%types types)) (fts1 (car r1))
              (r2 (and r1 (module_ok/%imports (module_ok/%ctx fts1 nil nil nil nil) imports)))
              (ixts (car r2))
              (r3 (and r2 (module_ok/%func-types fts1 funcs))) (fts (car r3))
              (cp (module_ok/%ctx fts1 (append ($funcsxt ixts) fts) ($globalsxt ixts) nil nil))
              (r4 (and r3 (module_ok/%globals cp globals))) (gts (car r4))
              (c0 (module_ok/%ctx fts1 (append ($funcsxt ixts) fts) (append ($globalsxt ixts) gts)
                                  ($tablesxt ixts) ($memsxt ixts)))
              (r5 (and r4 (module_ok/%tables c0 tables))) (tts (car r5))
              (r6 (and r5 (module_ok/%mems c0 mems))) (mts (car r6))
              (c (module_ok/%ctx fts1 (append ($funcsxt ixts) fts) (append ($globalsxt ixts) gts)
                                 (append ($tablesxt ixts) tts) (append ($memsxt ixts) mts)))
              (r7 (and r6 (module_ok/%exports c exports))) (xts (car r7)))
         (and r7
              (module_ok/%funcs-ok c funcs fts)
              (module_ok/%elems-ok c elems)
              (module_ok/%datas-ok c datas)
              (module_ok/%starts-ok c start)
              (<= (len tts) 1) (<= (len mts) 1)
              ($disjoint_ (module_ok/%names exports))
              (list (list :|%->%| ixts xts))))))))

 (:sized "||BX||"
  :pairs (("Bsection_" . "len") ("Bcode" . "len"))
  :reason "The source premise `len = ||BX||` (byte length of what BX matched) elaborates to `len = 0` in the IL, which would reject every non-empty section. In these grammars the item after `len` is parsed from exactly `len` bytes instead, and the `len = 0` premise is dropped.")
)
