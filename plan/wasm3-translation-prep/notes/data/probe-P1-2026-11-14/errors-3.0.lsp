; Every error logged by translator phase 1 (make probe).
; One per line: (function kind detail [:rule "Rel/id" :pos k] [:mode m]).
("$UTF8SINGLE" "pattern" (BIN ADD NAT (BIN MUL NAT (BIN POW NAT (NUM (NAT 2)) (NUM (NAT 6))) (CVT INT NAT (BIN SUB INT (CVT NAT INT (PROJ (UNCASE (VAR "b_1") "%") 0)) (CVT NAT INT (NUM (NAT 192)))))) (CALL "cont" (EXP (VAR "b_2")))))

("$UTF8SINGLE" "unbound variable" "b_1")

("$UTF8SINGLE" "unbound variable" "b_2")

("$UTF8SINGLE" "pattern" (BIN ADD NAT (BIN ADD NAT (BIN MUL NAT (BIN POW NAT (NUM (NAT 2)) (NUM (NAT 12))) (CVT INT NAT (BIN SUB INT (CVT NAT INT (PROJ (UNCASE (VAR "b_1") "%") 0)) (CVT NAT INT (NUM (NAT 224)))))) (BIN MUL NAT (BIN POW NAT (NUM (NAT 2)) (NUM (NAT 6))) (CALL "cont" (EXP (VAR "b_2"))))) (CALL "cont" (EXP (VAR "b_3")))))

("$UTF8SINGLE" "unbound variable" "b_1")

("$UTF8SINGLE" "unbound variable" "b_2")

("$UTF8SINGLE" "unbound variable" "b_3")

("$UTF8SINGLE" "pattern" (BIN ADD NAT (BIN ADD NAT (BIN ADD NAT (BIN MUL NAT (BIN POW NAT (NUM (NAT 2)) (NUM (NAT 18))) (CVT INT NAT (BIN SUB INT (CVT NAT INT (PROJ (UNCASE (VAR "b_1") "%") 0)) (CVT NAT INT (NUM (NAT 240)))))) (BIN MUL NAT (BIN POW NAT (NUM (NAT 2)) (NUM (NAT 12))) (CALL "cont" (EXP (VAR "b_2"))))) (BIN MUL NAT (BIN POW NAT (NUM (NAT 2)) (NUM (NAT 6))) (CALL "cont" (EXP (VAR "b_3"))))) (CALL "cont" (EXP (VAR "b_4")))))

("$UTF8SINGLE" "unbound variable" "b_1")

("$UTF8SINGLE" "unbound variable" "b_2")

("$UTF8SINGLE" "unbound variable" "b_3")

("$UTF8SINGLE" "unbound variable" "b_4")

("HEAPTYPE_OK" "unbound variable" "absheaptype" :RULE "Heaptype_ok/abs" :POS 0 :MODE :FUN)

("VALTYPE_OK" "checker relation with unbound arguments" (RULE "Numtype_ok" "%|-%:OK" (TUP (VAR "C") (VAR "numtype"))) :RULE "Valtype_ok/num" :POS 0 :MODE :FUN)

("VALTYPE_OK" "unbound variable" "numtype" :RULE "Valtype_ok/num" :POS 0 :MODE :FUN)

("VALTYPE_OK" "checker relation with unbound arguments" (RULE "Vectype_ok" "%|-%:OK" (TUP (VAR "C") (VAR "vectype"))) :RULE "Valtype_ok/vec" :POS 1 :MODE :FUN)

("VALTYPE_OK" "unbound variable" "vectype" :RULE "Valtype_ok/vec" :POS 1 :MODE :FUN)

("TYPEUSE_OK" "condition with unbound variables" (CMP LT NAT (PROJ (UNCASE (VAR "typeidx") "%") 0) (LEN (DOT (VAR "C") "TYPES"))) :RULE "Typeuse_ok/typeidx" :POS 0 :MODE :FUN)

("TYPEUSE_OK" "condition with unbound variables" (CMP EQ BOOL (IDX (DOT (VAR "C") "TYPES") (PROJ (UNCASE (VAR "typeidx") "%") 0)) (VAR "dt")) :RULE "Typeuse_ok/typeidx" :POS 0 :MODE :FUN)

("TYPEUSE_OK" "unbound variable" "typeidx" :RULE "Typeuse_ok/typeidx" :POS 0 :MODE :FUN)

("TYPEUSE_OK" "condition with unbound variables" (CMP LT NAT (VAR "i") (LEN (DOT (VAR "C") "RECS"))) :RULE "Typeuse_ok/rec" :POS 1 :MODE :FUN)

("TYPEUSE_OK" "condition with unbound variables" (CMP EQ BOOL (IDX (DOT (VAR "C") "RECS") (VAR "i")) (VAR "st")) :RULE "Typeuse_ok/rec" :POS 1 :MODE :FUN)

("TYPEUSE_OK" "unbound variable" "i" :RULE "Typeuse_ok/rec" :POS 1 :MODE :FUN)

("RESULTTYPE_OK" "iterated premise without inputs" (ITER (RULE "Valtype_ok" "%|-%:OK" (TUP (VAR "C") (VAR "t"))) LIST (DOM "t" (VAR "t*"))) :RULE "Resulttype_ok/" :POS 0 :MODE :FUN)

("RESULTTYPE_OK" "unbound variable" "t*" :RULE "Resulttype_ok/" :POS 0 :MODE :FUN)

("STORAGETYPE_OK" "checker relation with unbound arguments" (RULE "Packtype_ok" "%|-%:OK" (TUP (VAR "C") (VAR "packtype"))) :RULE "Storagetype_ok/pack" :POS 1 :MODE :FUN)

("STORAGETYPE_OK" "unbound variable" "packtype" :RULE "Storagetype_ok/pack" :POS 1 :MODE :FUN)

("COMPTYPE_OK" "iterated premise without inputs" (ITER (RULE "Fieldtype_ok" "%|-%:OK" (TUP (VAR "C") (VAR "fieldtype"))) LIST (DOM "fieldtype" (VAR "fieldtype*"))) :RULE "Comptype_ok/struct" :POS 0 :MODE :FUN)

("COMPTYPE_OK" "unbound variable" "fieldtype*" :RULE "Comptype_ok/struct" :POS 0 :MODE :FUN)

("SUBTYPE_OK2" "condition with unbound variables" (CALL "before" (EXP (VAR "typeuse")) (EXP (VAR "i"))) :RULE "Subtype_ok2/" :POS 0 :MODE :FUN)

("SUBTYPE_OK2" "unbound variable" "i" :RULE "Subtype_ok2/" :POS 0 :MODE :FUN)

("RECTYPE_OK2" "unbound variable" "i" :RULE "Rectype_ok2/empty" :POS 0 :MODE :FUN)

("DEFTYPE_OK" "relation inputs unbound" (RULE "Rectype_ok2" "%|-%:%" (TUP (COMP (STRUCT (FIELD "TYPES" (LIST)) (FIELD "TAGS" (LIST)) (FIELD "GLOBALS" (LIST)) (FIELD "MEMS" (LIST)) (FIELD "TABLES" (LIST)) (FIELD "FUNCS" (LIST)) (FIELD "DATAS" (LIST)) (FIELD "ELEMS" (LIST)) (FIELD "LOCALS" (LIST)) (FIELD "LABELS" (LIST)) (FIELD "RETURN" (OPT)) (FIELD "REFS" (LIST)) (FIELD "RECS" (ITER (VAR "subtype") (LISTN (VAR "n")) (DOM "subtype" (VAR "subtype*"))))) (VAR "C")) (VAR "rectype") (CASE "OK" (NUM (NAT 0))))) :RULE "Deftype_ok/" :POS 0 :MODE :FUN)

("DEFTYPE_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "rectype") (CASE "REC" (CASE "%" (TUP (ITER (VAR "subtype") (LISTN (VAR "n")) (DOM "subtype" (VAR "subtype*"))))))) :RULE "Deftype_ok/" :POS 0 :MODE :FUN)

("DEFTYPE_OK" "condition with unbound variables" (CMP LT NAT (VAR "i") (VAR "n")) :RULE "Deftype_ok/" :POS 0 :MODE :FUN)

("DEFTYPE_OK" "unbound variable" "rectype" :RULE "Deftype_ok/" :POS 0 :MODE :FUN)

("DEFTYPE_OK" "unbound variable" "i" :RULE "Deftype_ok/" :POS 0 :MODE :FUN)

("COMPTYPE_SUB" "relation inputs unbound" (RULE "Resulttype_sub" "%|-%<:%" (TUP (VAR "C") (CASE "%" (TUP (ITER (VAR "t_21") LIST (DOM "t_21" (VAR "t_21*"))))) (CASE "%" (TUP (ITER (VAR "t_11") LIST (DOM "t_11" (VAR "t_11*"))))))) :RULE "Comptype_sub/func" :POS 2 :MODE :FUN)

("COMPTYPE_SUB" "unbound variable" "t_21*" :RULE "Comptype_sub/func" :POS 2 :MODE :FUN)

("DEFTYPE_SUB" "pattern" (CALL "clos_deftype" (EXP (VAR "C")) (EXP (VAR "deftype_2"))) :RULE "Deftype_sub/refl" :POS 0 :MODE :FUN)

("DEFTYPE_SUB" "unbound variable" "deftype_2" :RULE "Deftype_sub/refl" :POS 0 :MODE :FUN)

("DEFTYPE_SUB" "condition with unbound variables" (CMP LT NAT (VAR "i") (LEN (ITER (VAR "typeuse") LIST (DOM "typeuse" (VAR "typeuse*"))))) :RULE "Deftype_sub/super" :POS 1 :MODE :FUN)

("DEFTYPE_SUB" "relation inputs unbound" (RULE "Heaptype_sub" "%|-%<:%" (TUP (VAR "C") (SUB (VAR "typeuse") (VAR "heaptype") (IDX (ITER (VAR "typeuse") LIST (DOM "typeuse" (VAR "typeuse*"))) (VAR "i"))) (SUB (VAR "deftype") (VAR "heaptype") (VAR "deftype_2")))) :RULE "Deftype_sub/super" :POS 1 :MODE :FUN)

("DEFTYPE_SUB" "unbound variable" "deftype_2" :RULE "Deftype_sub/super" :POS 1 :MODE :FUN)

("HEAPTYPE_SUB" "condition with unbound variables" (CMP LT NAT (PROJ (UNCASE (VAR "typeidx") "%") 0) (LEN (DOT (VAR "C") "TYPES"))) :RULE "Heaptype_sub/typeidx-r" :POS 11 :MODE :FUN)

("HEAPTYPE_SUB" "pattern" (IDX (DOT (VAR "C") "TYPES") (PROJ (UNCASE (VAR "typeidx") "%") 0)) :RULE "Heaptype_sub/typeidx-r" :POS 11 :MODE :FUN)

("HEAPTYPE_SUB" "unbound variable" "typeidx" :RULE "Heaptype_sub/typeidx-r" :POS 11 :MODE :FUN)

("HEAPTYPE_SUB" "condition with unbound variables" (CMP LT NAT (VAR "j") (LEN (ITER (VAR "typeuse") LIST (DOM "typeuse" (VAR "typeuse*"))))) :RULE "Heaptype_sub/rec-sub" :POS 15 :MODE :FUN)

("HEAPTYPE_SUB" "unbound variable" "j" :RULE "Heaptype_sub/rec-sub" :POS 15 :MODE :FUN)

("HEAPTYPE_SUB" "relation inputs unbound" (RULE "Heaptype_sub" "%|-%<:%" (TUP (VAR "C") (VAR "heaptype") (CASE "ANY" (TUP)))) :RULE "Heaptype_sub/none" :POS 16 :MODE :FUN)

("HEAPTYPE_SUB" "condition with unbound variables" (CMP NE BOOL (VAR "heaptype") (CASE "BOT" (TUP))) :RULE "Heaptype_sub/none" :POS 16 :MODE :FUN)

("HEAPTYPE_SUB" "unbound variable" "heaptype" :RULE "Heaptype_sub/none" :POS 16 :MODE :FUN)

("HEAPTYPE_SUB" "relation inputs unbound" (RULE "Heaptype_sub" "%|-%<:%" (TUP (VAR "C") (VAR "heaptype") (CASE "FUNC" (TUP)))) :RULE "Heaptype_sub/nofunc" :POS 17 :MODE :FUN)

("HEAPTYPE_SUB" "condition with unbound variables" (CMP NE BOOL (VAR "heaptype") (CASE "BOT" (TUP))) :RULE "Heaptype_sub/nofunc" :POS 17 :MODE :FUN)

("HEAPTYPE_SUB" "unbound variable" "heaptype" :RULE "Heaptype_sub/nofunc" :POS 17 :MODE :FUN)

("HEAPTYPE_SUB" "relation inputs unbound" (RULE "Heaptype_sub" "%|-%<:%" (TUP (VAR "C") (VAR "heaptype") (CASE "EXN" (TUP)))) :RULE "Heaptype_sub/noexn" :POS 18 :MODE :FUN)

("HEAPTYPE_SUB" "condition with unbound variables" (CMP NE BOOL (VAR "heaptype") (CASE "BOT" (TUP))) :RULE "Heaptype_sub/noexn" :POS 18 :MODE :FUN)

("HEAPTYPE_SUB" "unbound variable" "heaptype" :RULE "Heaptype_sub/noexn" :POS 18 :MODE :FUN)

("HEAPTYPE_SUB" "relation inputs unbound" (RULE "Heaptype_sub" "%|-%<:%" (TUP (VAR "C") (VAR "heaptype") (CASE "EXTERN" (TUP)))) :RULE "Heaptype_sub/noextern" :POS 19 :MODE :FUN)

("HEAPTYPE_SUB" "condition with unbound variables" (CMP NE BOOL (VAR "heaptype") (CASE "BOT" (TUP))) :RULE "Heaptype_sub/noextern" :POS 19 :MODE :FUN)

("HEAPTYPE_SUB" "unbound variable" "heaptype" :RULE "Heaptype_sub/noextern" :POS 19 :MODE :FUN)

("HEAPTYPE_SUB" "unbound variable" "heaptype" :RULE "Heaptype_sub/bot" :POS 20 :MODE :FUN)

("VALTYPE_SUB" "unbound variable" "valtype" :RULE "Valtype_sub/bot" :POS 3 :MODE :FUN)

("DEFTYPE_SUB" "condition with unbound variables" (CMP LT NAT (VAR "i") (LEN (ITER (VAR "typeuse") LIST (DOM "typeuse" (VAR "typeuse*"))))) :RULE "Deftype_sub/super" :POS 1 :MODE :CHECK)

("DEFTYPE_SUB" "relation inputs unbound" (RULE "Heaptype_sub" "%|-%<:%" (TUP (VAR "C") (SUB (VAR "typeuse") (VAR "heaptype") (IDX (ITER (VAR "typeuse") LIST (DOM "typeuse" (VAR "typeuse*"))) (VAR "i"))) (SUB (VAR "deftype") (VAR "heaptype") (VAR "deftype_2")))) :RULE "Deftype_sub/super" :POS 1 :MODE :CHECK)

("HEAPTYPE_SUB" "condition with unbound variables" (CMP LT NAT (VAR "j") (LEN (ITER (VAR "typeuse") LIST (DOM "typeuse" (VAR "typeuse*"))))) :RULE "Heaptype_sub/rec-sub" :POS 15 :MODE :CHECK)

("HEAPTYPE_SUB" "unbound variable" "j" :RULE "Heaptype_sub/rec-sub" :POS 15 :MODE :CHECK)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Instrtype_ok" "%|-%:OK" (TUP (VAR "C") (CASE "%->_%%" (TUP (CASE "%" (TUP (ITER (VAR "t_1") LIST (DOM "t_1" (VAR "t_1*"))))) (LIST) (CASE "%" (TUP (ITER (VAR "t_2") LIST (DOM "t_2" (VAR "t_2*"))))))))) :RULE "Instr_ok/unreachable" :POS 1 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_1*" :RULE "Instr_ok/unreachable" :POS 1 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_2*" :RULE "Instr_ok/unreachable" :POS 1 :MODE :FUN)

("INSTR_OK" "disjuncts bind different variables" (BIN OR BOOL (CMP EQ BOOL (VAR "t'") (SUB (VAR "numtype") (VAR "valtype") (VAR "numtype"))) (CMP EQ BOOL (VAR "t'") (SUB (VAR "vectype") (VAR "valtype") (VAR "vectype")))) :RULE "Instr_ok/select-impl" :POS 4 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Instrtype_ok" "%|-%:OK" (TUP (VAR "C") (CASE "%->_%%" (TUP (CASE "%" (TUP (ITER (VAR "t_1") LIST (DOM "t_1" (VAR "t_1*"))))) (LIST) (CASE "%" (TUP (ITER (VAR "t_2") LIST (DOM "t_2" (VAR "t_2*"))))))))) :RULE "Instr_ok/br" :POS 8 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_1*" :RULE "Instr_ok/br" :POS 8 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_2*" :RULE "Instr_ok/br" :POS 8 :MODE :FUN)

("INSTR_OK" "relation inputs unbound" (RULE "Resulttype_sub" "%|-%<:%" (TUP (VAR "C") (CASE "%" (TUP (ITER (VAR "t") LIST (DOM "t" (VAR "t*"))))) (IDX (DOT (VAR "C") "LABELS") (PROJ (UNCASE (VAR "l") "%") 0)))) :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "relation inputs unbound" (RULE "Resulttype_sub" "%|-%<:%" (TUP (VAR "C") (CASE "%" (TUP (ITER (VAR "t") LIST (DOM "t" (VAR "t*"))))) (IDX (DOT (VAR "C") "LABELS") (PROJ (UNCASE (VAR "l'") "%") 0)))) :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Instrtype_ok" "%|-%:OK" (TUP (VAR "C") (CASE "%->_%%" (TUP (CASE "%" (TUP (CAT (ITER (VAR "t_1") LIST (DOM "t_1" (VAR "t_1*"))) (CAT (ITER (VAR "t") LIST (DOM "t" (VAR "t*"))) (LIST (CASE "I32" (TUP))))))) (LIST) (CASE "%" (TUP (ITER (VAR "t_2") LIST (DOM "t_2" (VAR "t_2*"))))))))) :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_1*" :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "unbound variable" "t*" :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_2*" :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Instrtype_ok" "%|-%:OK" (TUP (VAR "C") (CASE "%->_%%" (TUP (CASE "%" (TUP (ITER (VAR "t_1") LIST (DOM "t_1" (VAR "t_1*"))))) (LIST) (CASE "%" (TUP (ITER (VAR "t_2") LIST (DOM "t_2" (VAR "t_2*"))))))))) :RULE "Instr_ok/return" :POS 18 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_1*" :RULE "Instr_ok/return" :POS 18 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_2*" :RULE "Instr_ok/return" :POS 18 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Instrtype_ok" "%|-%:OK" (TUP (VAR "C") (CASE "%->_%%" (TUP (CASE "%" (TUP (ITER (VAR "t_3") LIST (DOM "t_3" (VAR "t_3*"))))) (LIST) (CASE "%" (TUP (ITER (VAR "t_4") LIST (DOM "t_4" (VAR "t_4*"))))))))) :RULE "Instr_ok/return_call" :POS 19 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_3*" :RULE "Instr_ok/return_call" :POS 19 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_4*" :RULE "Instr_ok/return_call" :POS 19 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Instrtype_ok" "%|-%:OK" (TUP (VAR "C") (CASE "%->_%%" (TUP (CASE "%" (TUP (ITER (VAR "t_3") LIST (DOM "t_3" (VAR "t_3*"))))) (LIST) (CASE "%" (TUP (ITER (VAR "t_4") LIST (DOM "t_4" (VAR "t_4*"))))))))) :RULE "Instr_ok/return_call_ref" :POS 20 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_3*" :RULE "Instr_ok/return_call_ref" :POS 20 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_4*" :RULE "Instr_ok/return_call_ref" :POS 20 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Instrtype_ok" "%|-%:OK" (TUP (VAR "C") (CASE "%->_%%" (TUP (CASE "%" (TUP (ITER (VAR "t_3") LIST (DOM "t_3" (VAR "t_3*"))))) (LIST) (CASE "%" (TUP (ITER (VAR "t_4") LIST (DOM "t_4" (VAR "t_4*"))))))))) :RULE "Instr_ok/return_call_indirect" :POS 21 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_3*" :RULE "Instr_ok/return_call_indirect" :POS 21 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_4*" :RULE "Instr_ok/return_call_indirect" :POS 21 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Instrtype_ok" "%|-%:OK" (TUP (VAR "C") (CASE "%->_%%" (TUP (CASE "%" (TUP (ITER (VAR "t_1") LIST (DOM "t_1" (VAR "t_1*"))))) (LIST) (CASE "%" (TUP (ITER (VAR "t_2") LIST (DOM "t_2" (VAR "t_2*"))))))))) :RULE "Instr_ok/throw" :POS 22 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_1*" :RULE "Instr_ok/throw" :POS 22 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_2*" :RULE "Instr_ok/throw" :POS 22 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Instrtype_ok" "%|-%:OK" (TUP (VAR "C") (CASE "%->_%%" (TUP (CASE "%" (TUP (ITER (VAR "t_1") LIST (DOM "t_1" (VAR "t_1*"))))) (LIST) (CASE "%" (TUP (ITER (VAR "t_2") LIST (DOM "t_2" (VAR "t_2*"))))))))) :RULE "Instr_ok/throw_ref" :POS 23 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_1*" :RULE "Instr_ok/throw_ref" :POS 23 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_2*" :RULE "Instr_ok/throw_ref" :POS 23 :MODE :FUN)

("INSTR_OK" "disjuncts bind different variables" (BIN OR BOOL (CMP EQ BOOL (CALL "unpack" (EXP (VAR "zt"))) (SUB (VAR "numtype") (VAR "valtype") (VAR "numtype"))) (CMP EQ BOOL (CALL "unpack" (EXP (VAR "zt"))) (SUB (VAR "vectype") (VAR "valtype") (VAR "vectype")))) :RULE "Instr_ok/array.new_data" :POS 42 :MODE :FUN)

("INSTR_OK" "disjuncts bind different variables" (BIN OR BOOL (CMP EQ BOOL (CALL "unpack" (EXP (VAR "zt"))) (SUB (VAR "numtype") (VAR "valtype") (VAR "numtype"))) (CMP EQ BOOL (CALL "unpack" (EXP (VAR "zt"))) (SUB (VAR "vectype") (VAR "valtype") (VAR "vectype")))) :RULE "Instr_ok/array.init_data" :POS 49 :MODE :FUN)

("INSTR_OK" "condition with unbound variables" (CMP EQ BOOL (ITER (VAR "null_1") OPT (DOM "null_1" (VAR "null_1?"))) (ITER (VAR "null_2") OPT (DOM "null_2" (VAR "null_2?")))) :RULE "Instr_ok/extern.convert_any" :POS 50 :MODE :FUN)

("INSTR_OK" "unbound variable" "null_1?" :RULE "Instr_ok/extern.convert_any" :POS 50 :MODE :FUN)

("INSTR_OK" "unbound variable" "null_2?" :RULE "Instr_ok/extern.convert_any" :POS 50 :MODE :FUN)

("INSTR_OK" "condition with unbound variables" (CMP EQ BOOL (ITER (VAR "null_1") OPT (DOM "null_1" (VAR "null_1?"))) (ITER (VAR "null_2") OPT (DOM "null_2" (VAR "null_2?")))) :RULE "Instr_ok/any.convert_extern" :POS 51 :MODE :FUN)

("INSTR_OK" "unbound variable" "null_1?" :RULE "Instr_ok/any.convert_extern" :POS 51 :MODE :FUN)

("INSTR_OK" "unbound variable" "null_2?" :RULE "Instr_ok/any.convert_extern" :POS 51 :MODE :FUN)

("INSTRS_OK" "checker relation with unbound arguments" (RULE "Instrtype_sub" "%|-%<:%" (TUP (VAR "C") (VAR "it") (VAR "it'"))) :RULE "Instrs_ok/sub" :POS 3 :MODE :FUN)

("INSTRS_OK" "checker relation with unbound arguments" (RULE "Instrtype_ok" "%|-%:OK" (TUP (VAR "C") (VAR "it'"))) :RULE "Instrs_ok/sub" :POS 3 :MODE :FUN)

("INSTRS_OK" "unbound variable" "it'" :RULE "Instrs_ok/sub" :POS 3 :MODE :FUN)

("INSTR_OK" "disjuncts bind different variables" (BIN OR BOOL (CMP EQ BOOL (VAR "t'") (SUB (VAR "numtype") (VAR "valtype") (VAR "numtype"))) (CMP EQ BOOL (VAR "t'") (SUB (VAR "vectype") (VAR "valtype") (VAR "vectype")))) :RULE "Instr_ok/select-impl" :POS 4 :MODE :CHECK)

("INSTR_OK" "disjuncts bind different variables" (BIN OR BOOL (CMP EQ BOOL (CALL "unpack" (EXP (VAR "zt"))) (SUB (VAR "numtype") (VAR "valtype") (VAR "numtype"))) (CMP EQ BOOL (CALL "unpack" (EXP (VAR "zt"))) (SUB (VAR "vectype") (VAR "valtype") (VAR "vectype")))) :RULE "Instr_ok/array.new_data" :POS 42 :MODE :CHECK)

("INSTR_OK" "disjuncts bind different variables" (BIN OR BOOL (CMP EQ BOOL (CALL "unpack" (EXP (VAR "zt"))) (SUB (VAR "numtype") (VAR "valtype") (VAR "numtype"))) (CMP EQ BOOL (CALL "unpack" (EXP (VAR "zt"))) (SUB (VAR "vectype") (VAR "valtype") (VAR "vectype")))) :RULE "Instr_ok/array.init_data" :POS 49 :MODE :CHECK)

("MODULE_OK" "pattern" (LEN (VAR "jt*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Tag_ok" "%|-%:%" (TUP (VAR "C'") (VAR "tag") (VAR "jt"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Tag_ok" "%|-%:%" (TUP (VAR "C'") (VAR "tag") (VAR "jt"))) LIST (DOM "jt" (VAR "jt*")) (DOM "tag" (VAR "tag*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Globals_ok" "%|-%:%" (TUP (VAR "C'") (ITER (VAR "global") LIST (DOM "global" (VAR "global*"))) (ITER (VAR "gt") LIST (DOM "gt" (VAR "gt*"))))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "mt*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Mem_ok" "%|-%:%" (TUP (VAR "C'") (VAR "mem") (VAR "mt"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Mem_ok" "%|-%:%" (TUP (VAR "C'") (VAR "mem") (VAR "mt"))) LIST (DOM "mem" (VAR "mem*")) (DOM "mt" (VAR "mt*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "tt*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Table_ok" "%|-%:%" (TUP (VAR "C'") (VAR "table") (VAR "tt"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Table_ok" "%|-%:%" (TUP (VAR "C'") (VAR "table") (VAR "tt"))) LIST (DOM "table" (VAR "table*")) (DOM "tt" (VAR "tt*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "dt*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Func_ok" "%|-%:%" (TUP (VAR "C") (VAR "func") (VAR "dt"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Func_ok" "%|-%:%" (TUP (VAR "C") (VAR "func") (VAR "dt"))) LIST (DOM "dt" (VAR "dt*")) (DOM "func" (VAR "func*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "ok*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Data_ok" "%|-%:%" (TUP (VAR "C") (VAR "data") (VAR "ok"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Data_ok" "%|-%:%" (TUP (VAR "C") (VAR "data") (VAR "ok"))) LIST (DOM "data" (VAR "data*")) (DOM "ok" (VAR "ok*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "rt*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Elem_ok" "%|-%:%" (TUP (VAR "C") (VAR "elem") (VAR "rt"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Elem_ok" "%|-%:%" (TUP (VAR "C") (VAR "elem") (VAR "rt"))) LIST (DOM "elem" (VAR "elem*")) (DOM "rt" (VAR "rt*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "checker relation with unbound arguments" (RULE "Start_ok" "%|-%:OK" (TUP (VAR "C") (VAR "start"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "nm*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "xt_E*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Export_ok" "%|-%:%%" (TUP (VAR "C") (VAR "export") (VAR "nm") (VAR "xt_E"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Export_ok" "%|-%:%%" (TUP (VAR "C") (VAR "export") (VAR "nm") (VAR "xt_E"))) LIST (DOM "export" (VAR "export*")) (DOM "nm" (VAR "nm*")) (DOM "xt_E" (VAR "xt_E*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "condition with unbound variables" (CALL "disjoint_" (TYP (VAR "name")) (EXP (ITER (VAR "nm") LIST (DOM "nm" (VAR "nm*"))))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "C") (COMP (VAR "C'") (STRUCT (FIELD "TYPES" (LIST)) (FIELD "TAGS" (CAT (ITER (VAR "jt_I") LIST (DOM "jt_I" (VAR "jt_I*"))) (ITER (VAR "jt") LIST (DOM "jt" (VAR "jt*"))))) (FIELD "GLOBALS" (ITER (VAR "gt") LIST (DOM "gt" (VAR "gt*")))) (FIELD "MEMS" (CAT (ITER (VAR "mt_I") LIST (DOM "mt_I" (VAR "mt_I*"))) (ITER (VAR "mt") LIST (DOM "mt" (VAR "mt*"))))) (FIELD "TABLES" (CAT (ITER (VAR "tt_I") LIST (DOM "tt_I" (VAR "tt_I*"))) (ITER (VAR "tt") LIST (DOM "tt" (VAR "tt*"))))) (FIELD "FUNCS" (LIST)) (FIELD "DATAS" (ITER (VAR "ok") LIST (DOM "ok" (VAR "ok*")))) (FIELD "ELEMS" (ITER (VAR "rt") LIST (DOM "rt" (VAR "rt*")))) (FIELD "LOCALS" (LIST)) (FIELD "LABELS" (LIST)) (FIELD "RETURN" (OPT)) (FIELD "REFS" (LIST)) (FIELD "RECS" (LIST))))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "C'") (STRUCT (FIELD "TYPES" (ITER (VAR "dt'") LIST (DOM "dt'" (VAR "dt'*")))) (FIELD "TAGS" (LIST)) (FIELD "GLOBALS" (ITER (VAR "gt_I") LIST (DOM "gt_I" (VAR "gt_I*")))) (FIELD "MEMS" (LIST)) (FIELD "TABLES" (LIST)) (FIELD "FUNCS" (CAT (ITER (VAR "dt_I") LIST (DOM "dt_I" (VAR "dt_I*"))) (ITER (VAR "dt") LIST (DOM "dt" (VAR "dt*"))))) (FIELD "DATAS" (LIST)) (FIELD "ELEMS" (LIST)) (FIELD "LOCALS" (LIST)) (FIELD "LABELS" (LIST)) (FIELD "RETURN" (OPT)) (FIELD "REFS" (ITER (VAR "x") LIST (DOM "x" (VAR "x*")))) (FIELD "RECS" (LIST)))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "unbound variable" "C" :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "unbound variable" "xt_E*" :RULE "Module_ok/" :POS 0 :MODE :FUN)

("$FVRELOP_" "pattern" (CALL "isize" (EXP (VAR "Inn"))))

("$FVRELOP_" "unbound variable" "Inn")

("$IVBITMASKOP_" "pattern" (CALL "ibits_" (EXP (NUM (NAT 32))) (EXP (VAR "c"))))

("$IVBITMASKOP_" "unbound variable" "c")

("$VUNOP_" "higher-order argument" (DEF "fabs_"))

("$VUNOP_" "higher-order argument" (DEF "fneg_"))

("$VUNOP_" "higher-order argument" (DEF "fsqrt_"))

("$VUNOP_" "higher-order argument" (DEF "fceil_"))

("$VUNOP_" "higher-order argument" (DEF "ffloor_"))

("$VUNOP_" "higher-order argument" (DEF "ftrunc_"))

("$VUNOP_" "higher-order argument" (DEF "fnearest_"))

("$VUNOP_" "higher-order argument" (DEF "iabs_"))

("$VUNOP_" "higher-order argument" (DEF "ineg_"))

("$VUNOP_" "higher-order argument" (DEF "ipopcnt_"))

("$VBINOP_" "higher-order argument" (DEF "iadd_"))

("$VBINOP_" "higher-order argument" (DEF "isub_"))

("$VBINOP_" "higher-order argument" (DEF "imul_"))

("$VBINOP_" "higher-order argument" (DEF "iadd_sat_"))

("$VBINOP_" "higher-order argument" (DEF "isub_sat_"))

("$VBINOP_" "higher-order argument" (DEF "imin_"))

("$VBINOP_" "higher-order argument" (DEF "imax_"))

("$VBINOP_" "higher-order argument" (DEF "iavgr_"))

("$VBINOP_" "higher-order argument" (DEF "iq15mulr_sat_"))

("$VBINOP_" "higher-order argument" (DEF "irelaxed_q15mulr_"))

("$VBINOP_" "higher-order argument" (DEF "fadd_"))

("$VBINOP_" "higher-order argument" (DEF "fsub_"))

("$VBINOP_" "higher-order argument" (DEF "fmul_"))

("$VBINOP_" "higher-order argument" (DEF "fdiv_"))

("$VBINOP_" "higher-order argument" (DEF "fmin_"))

("$VBINOP_" "higher-order argument" (DEF "fmax_"))

("$VBINOP_" "higher-order argument" (DEF "fpmin_"))

("$VBINOP_" "higher-order argument" (DEF "fpmax_"))

("$VBINOP_" "higher-order argument" (DEF "frelaxed_min_"))

("$VBINOP_" "higher-order argument" (DEF "frelaxed_max_"))

("$VTERNOP_" "higher-order argument" (DEF "irelaxed_laneselect_"))

("$VTERNOP_" "higher-order argument" (DEF "frelaxed_madd_"))

("$VTERNOP_" "higher-order argument" (DEF "frelaxed_nmadd_"))

("$VRELOP_" "higher-order argument" (DEF "ieq_"))

("$VRELOP_" "higher-order argument" (DEF "ine_"))

("$VRELOP_" "higher-order argument" (DEF "ilt_"))

("$VRELOP_" "higher-order argument" (DEF "igt_"))

("$VRELOP_" "higher-order argument" (DEF "ile_"))

("$VRELOP_" "higher-order argument" (DEF "ige_"))

("$VRELOP_" "higher-order argument" (DEF "feq_"))

("$VRELOP_" "higher-order argument" (DEF "fne_"))

("$VRELOP_" "higher-order argument" (DEF "flt_"))

("$VRELOP_" "higher-order argument" (DEF "fgt_"))

("$VRELOP_" "higher-order argument" (DEF "fle_"))

("$VRELOP_" "higher-order argument" (DEF "fge_"))

("$VSHIFTOP_" "higher-order argument" (DEF "ishl_"))

("$VSHIFTOP_" "higher-order argument" (DEF "ishr_"))

("$VSWIZZLOP_" "higher-order argument" (DEF "iswizzle_lane_"))

("$VSWIZZLOP_" "higher-order argument" (DEF "irelaxed_swizzle_lane_"))

("$IVADD_PAIRWISE_" "pattern" (CALL "concat_" (TYP (VAR "N")) (EXP (ITER (LIST (VAR "j_1") (VAR "j_2")) LIST (DOM "j_1" (VAR "j_1*")) (DOM "j_2" (VAR "j_2*"))))))

("$IVADD_PAIRWISE_" "unbound variable" "j_1*")

("$IVADD_PAIRWISE_" "unbound variable" "j_2*")

("$VEXTUNOP__" "higher-order argument" (DEF "ivadd_pairwise_"))

("$IVDOT_" "pattern" (CALL "concat_" (TYP (VAR "iN" (EXP (VAR "N")))) (EXP (ITER (LIST (VAR "j_1") (VAR "j_2")) LIST (DOM "j_1" (VAR "j_1*")) (DOM "j_2" (VAR "j_2*"))))))

("$IVDOT_" "unbound variable" "j_1*")

("$IVDOT_" "unbound variable" "j_2*")

("$IVDOT_SAT_" "pattern" (CALL "concat_" (TYP (VAR "iN" (EXP (VAR "N")))) (EXP (ITER (LIST (VAR "j_1") (VAR "j_2")) LIST (DOM "j_1" (VAR "j_1*")) (DOM "j_2" (VAR "j_2*"))))))

("$IVDOT_SAT_" "unbound variable" "j_1*")

("$IVDOT_SAT_" "unbound variable" "j_2*")

("$VEXTBINOP__" "higher-order argument" (DEF "ivmul_"))

("$VEXTBINOP__" "higher-order argument" (DEF "ivdot_"))

("$VEXTBINOP__" "higher-order argument" (DEF "ivrelaxed_dot_"))

("STEP_PURE" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (VAR "Lnn") (VAR "M")))) (EXP (ITER (CALL "lpacknum_" (EXP (VAR "Lnn")) (EXP (VAR "c_1"))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0)))))) :RULE "Step_pure/vsplat" :POS 70 :MODE :FUN)

("STEP_PURE" "unbound variable" "Lnn" :RULE "Step_pure/vsplat" :POS 70 :MODE :FUN)

("STEP_PURE" "unbound variable" "c_1" :RULE "Step_pure/vsplat" :POS 70 :MODE :FUN)

("STEP_PURE" "unbound variable" "Lnn" :RULE "Step_pure/vsplat" :POS 70 :MODE :FUN)

("STEP_PURE" "unbound variable" "M" :RULE "Step_pure/vsplat" :POS 70 :MODE :FUN)

("STEP_PURE" "unbound variable" "c" :RULE "Step_pure/vsplat" :POS 70 :MODE :FUN)

("STEP_PURE" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (VAR "Lnn") (VAR "M")))) (EXP (UPD (CALL "lanes_" (EXP (CASE "%X%" (TUP (VAR "Lnn") (VAR "M")))) (EXP (VAR "c_1"))) (IDX ROOT (PROJ (UNCASE (VAR "i") "%") 0)) (CALL "lpacknum_" (EXP (VAR "Lnn")) (EXP (VAR "c_2"))))))) :RULE "Step_pure/vreplace_lane" :POS 73 :MODE :FUN)

("STEP_PURE" "unbound variable" "c_1" :RULE "Step_pure/vreplace_lane" :POS 73 :MODE :FUN)

("STEP_PURE" "unbound variable" "Lnn" :RULE "Step_pure/vreplace_lane" :POS 73 :MODE :FUN)

("STEP_PURE" "unbound variable" "c_2" :RULE "Step_pure/vreplace_lane" :POS 73 :MODE :FUN)

("STEP_PURE" "unbound variable" "Lnn" :RULE "Step_pure/vreplace_lane" :POS 73 :MODE :FUN)

("STEP_PURE" "unbound variable" "M" :RULE "Step_pure/vreplace_lane" :POS 73 :MODE :FUN)

("STEP_PURE" "unbound variable" "i" :RULE "Step_pure/vreplace_lane" :POS 73 :MODE :FUN)

("STEP_PURE" "unbound variable" "c" :RULE "Step_pure/vreplace_lane" :POS 73 :MODE :FUN)

("STEP_READ" "pattern" (CALL "nbytes_" (EXP (VAR "nt")) (EXP (VAR "c"))) :RULE "Step_read/load-num-val" :POS 39 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/load-num-val" :POS 39 :MODE :FUN)

("STEP_READ" "pattern" (CALL "vbytes_" (EXP (CASE "V128" (TUP))) (EXP (VAR "c"))) :RULE "Step_read/vload-num-val" :POS 43 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/vload-num-val" :POS 43 :MODE :FUN)

("STEP_READ" "iterated premise without inputs" (ITER (IF (CMP EQ BOOL (CALL "ibytes_" (EXP (VAR "K")) (EXP (VAR "j"))) (SLICE (DOT (CALL "mem" (EXP (VAR "z")) (EXP (VAR "x"))) "BYTES") (BIN ADD NAT (BIN ADD NAT (PROJ (UNCASE (VAR "i") "%") 0) (PROJ (UNCASE (DOT (VAR "ao") "OFFSET") "%") 0)) (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (BIN MUL NAT (VAR "k") (VAR "K"))) (CVT NAT RAT (NUM (NAT 8)))))) (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (VAR "K")) (CVT NAT RAT (NUM (NAT 8)))))))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0) "k") (DOM "j" (VAR "j*"))) :RULE "Step_read/vload-pack-val" :POS 45 :MODE :FUN)

("STEP_READ" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (ITER (CALL "extend__" (EXP (VAR "K")) (EXP (CALL "jsizenn" (EXP (VAR "Jnn")))) (EXP (VAR "sx")) (EXP (VAR "j"))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0)) (DOM "j" (VAR "j*")))))) :RULE "Step_read/vload-pack-val" :POS 45 :MODE :FUN)

("STEP_READ" "pattern" (CALL "jsizenn" (EXP (VAR "Jnn"))) :RULE "Step_read/vload-pack-val" :POS 45 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/vload-pack-val" :POS 45 :MODE :FUN)

("STEP_READ" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step_read/vload-splat-val" :POS 47 :MODE :FUN)

("STEP_READ" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (ITER (CASE "%" (TUP (PROJ (UNCASE (VAR "j") "%") 0))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0)))))) :RULE "Step_read/vload-splat-val" :POS 47 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/vload-splat-val" :POS 47 :MODE :FUN)

("STEP_READ" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step_read/vload_lane-val" :POS 51 :MODE :FUN)

("STEP_READ" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (UPD (CALL "lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (VAR "c_1"))) (IDX ROOT (PROJ (UNCASE (VAR "j") "%") 0)) (CASE "%" (TUP (PROJ (UNCASE (VAR "k") "%") 0))))))) :RULE "Step_read/vload_lane-val" :POS 51 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/vload_lane-val" :POS 51 :MODE :FUN)

("STEP_READ" "premise" (ITER (IF (CMP NE BOOL (CALL "cunpack" (EXP (VAR "zt"))) (OPT))) (LISTN (VAR "n"))) :RULE "Step_read/array.new_data-num" :POS 76 :MODE :FUN)

("STEP_READ" "pattern" (CALL "concatn_" (TYP (VAR "byte")) (EXP (ITER (CALL "zbytes_" (EXP (VAR "zt")) (EXP (VAR "c"))) (LISTN (VAR "n")) (DOM "c" (VAR "c*")))) (EXP (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (CALL "zsize" (EXP (VAR "zt")))) (CVT NAT RAT (NUM (NAT 8))))))) :RULE "Step_read/array.new_data-num" :POS 76 :MODE :FUN)

("STEP_READ" "unbound variable" "c*" :RULE "Step_read/array.new_data-num" :POS 76 :MODE :FUN)

("STEP_READ" "pattern" (CALL "zbytes_" (EXP (VAR "zt")) (EXP (VAR "c"))) :RULE "Step_read/array.init_data-num" :POS 102 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/array.init_data-num" :POS 102 :MODE :FUN)

("STEP_READ" "iterated premise without inputs" (ITER (IF (CMP EQ BOOL (CALL "ibytes_" (EXP (VAR "K")) (EXP (VAR "j"))) (SLICE (DOT (CALL "mem" (EXP (VAR "z")) (EXP (VAR "x"))) "BYTES") (BIN ADD NAT (BIN ADD NAT (PROJ (UNCASE (VAR "i") "%") 0) (PROJ (UNCASE (DOT (VAR "ao") "OFFSET") "%") 0)) (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (BIN MUL NAT (VAR "k") (VAR "K"))) (CVT NAT RAT (NUM (NAT 8)))))) (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (VAR "K")) (CVT NAT RAT (NUM (NAT 8)))))))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0) "k") (DOM "j" (VAR "j*"))) :RULE "Step_read/vload-pack-val" :POS 45 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (ITER (CALL "extend__" (EXP (VAR "K")) (EXP (CALL "jsizenn" (EXP (VAR "Jnn")))) (EXP (VAR "sx")) (EXP (VAR "j"))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0)) (DOM "j" (VAR "j*"))))) :RULE "Step_read/vload-pack-val" :POS 45 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "jsizenn" (EXP (VAR "Jnn"))) :RULE "Step_read/vload-pack-val" :POS 45 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step_read/vload-splat-val" :POS 47 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (ITER (CASE "%" (TUP (PROJ (UNCASE (VAR "j") "%") 0))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0))))) :RULE "Step_read/vload-splat-val" :POS 47 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step_read/vload_lane-val" :POS 51 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (UPD (CALL "lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (VAR "c_1"))) (IDX ROOT (PROJ (UNCASE (VAR "j") "%") 0)) (CASE "%" (TUP (PROJ (UNCASE (VAR "k") "%") 0)))))) :RULE "Step_read/vload_lane-val" :POS 51 :MODE :CHECK)

("STEP_READ" "premise" (ITER (IF (CMP NE BOOL (CALL "cunpack" (EXP (VAR "zt"))) (OPT))) (LISTN (VAR "n"))) :RULE "Step_read/array.new_data-num" :POS 76 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "concatn_" (TYP (VAR "byte")) (EXP (ITER (CALL "zbytes_" (EXP (VAR "zt")) (EXP (VAR "c"))) (LISTN (VAR "n")) (DOM "c" (VAR "c*")))) (EXP (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (CALL "zsize" (EXP (VAR "zt")))) (CVT NAT RAT (NUM (NAT 8))))))) :RULE "Step_read/array.new_data-num" :POS 76 :MODE :CHECK)

("STEP_READ" "unbound variable" "c*" :RULE "Step_read/array.new_data-num" :POS 76 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "zbytes_" (EXP (VAR "zt")) (EXP (VAR "c"))) :RULE "Step_read/array.init_data-num" :POS 102 :MODE :CHECK)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/array.init_data-num" :POS 102 :MODE :CHECK)

("STEP" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step/vstore_lane-val" :POS 25 :MODE :FUN)

("STEP" "condition with unbound variables" (CMP LT NAT (PROJ (UNCASE (VAR "j") "%") 0) (LEN (CALL "lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (VAR "c"))))) :RULE "Step/vstore_lane-val" :POS 25 :MODE :FUN)

("STEP" "condition with unbound variables" (CMP EQ BOOL (ITER (VAR "b") LIST (DOM "b" (VAR "b*"))) (CALL "ibytes_" (EXP (VAR "N")) (EXP (CASE "%" (TUP (PROJ (UNCASE (IDX (CALL "lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (VAR "c"))) (PROJ (UNCASE (VAR "j") "%") 0)) "%") 0)))))) :RULE "Step/vstore_lane-val" :POS 25 :MODE :FUN)

("STEP" "unbound variable" "b*" :RULE "Step/vstore_lane-val" :POS 25 :MODE :FUN)

("$EVALEXPRS" "relation inputs unbound" (RULE "Eval_expr" "%;%~>*%;%" (TUP (VAR "z") (VAR "expr") (VAR "z'") (LIST (SUB (VAR "ref") (VAR "val") (VAR "ref"))))))

("$EVALEXPRS" "condition with unbound variables" (CMP EQ BOOL (TUP (VAR "z''") (ITER (VAR "ref'") LIST (DOM "ref'" (VAR "ref'*")))) (CALL "evalexprs" (EXP (VAR "z'")) (EXP (ITER (VAR "expr'") LIST (DOM "expr'" (VAR "expr'*")))))))

("$EVALEXPRS" "unbound variable" "z''")

("$EVALEXPRS" "unbound variable" "ref")

("$EVALEXPRS" "unbound variable" "ref'*")

("$EVALGLOBALS" "relation inputs unbound" (RULE "Eval_expr" "%;%~>*%;%" (TUP (VAR "z") (VAR "expr") (VAR "z'") (LIST (VAR "val")))))

("$EVALGLOBALS" "condition with unbound variables" (CMP EQ BOOL (VAR "z'") (CASE "%;%" (TUP (VAR "s") (VAR "f")))))

("$EVALGLOBALS" "condition with unbound variables" (CMP EQ BOOL (TUP (VAR "s'") (VAR "a")) (CALL "allocglobal" (EXP (VAR "s")) (EXP (VAR "gt")) (EXP (VAR "val")))))

("$EVALGLOBALS" "condition with unbound variables" (CMP EQ BOOL (TUP (VAR "z''") (ITER (VAR "val'") LIST (DOM "val'" (VAR "val'*")))) (CALL "evalglobals" (EXP (CASE "%;%" (TUP (VAR "s'") (EXT (VAR "f") (DOT (DOT ROOT "MODULE") "GLOBALS") (LIST (VAR "a")))))) (EXP (ITER (VAR "gt'") LIST (DOM "gt'" (VAR "gt'*")))) (EXP (ITER (VAR "expr'") LIST (DOM "expr'" (VAR "expr'*")))))))

("$EVALGLOBALS" "unbound variable" "z''")

("$EVALGLOBALS" "unbound variable" "val")

("$EVALGLOBALS" "unbound variable" "val'*")

("CONTEXT_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "C") (STRUCT (FIELD "TYPES" (ITER (VAR "dt") (LISTN (VAR "n")) (DOM "dt" (VAR "dt*")))) (FIELD "TAGS" (ITER (VAR "jt") LIST (DOM "jt" (VAR "jt*")))) (FIELD "GLOBALS" (ITER (VAR "gt") LIST (DOM "gt" (VAR "gt*")))) (FIELD "MEMS" (ITER (VAR "mt") LIST (DOM "mt" (VAR "mt*")))) (FIELD "TABLES" (ITER (VAR "tt") LIST (DOM "tt" (VAR "tt*")))) (FIELD "FUNCS" (ITER (VAR "dt_F") LIST (DOM "dt_F" (VAR "dt_F*")))) (FIELD "DATAS" (ITER (VAR "ok") LIST (DOM "ok" (VAR "ok*")))) (FIELD "ELEMS" (ITER (VAR "et") LIST (DOM "et" (VAR "et*")))) (FIELD "LOCALS" (ITER (VAR "lct") LIST (DOM "lct" (VAR "lct*")))) (FIELD "LABELS" (ITER (CASE "%" (TUP (ITER (VAR "t") LIST (DOM "t" (VAR "t*"))))) LIST (DOM "t*" (VAR "t**")))) (FIELD "RETURN" (ITER (CASE "%" (TUP (ITER (VAR "t'") LIST (DOM "t'" (VAR "t'*"))))) OPT (DOM "t'*" (VAR "t'*?")))) (FIELD "REFS" (ITER (VAR "x") LIST (DOM "x" (VAR "x*")))) (FIELD "RECS" (ITER (VAR "st") (LISTN (VAR "m")) (DOM "st" (VAR "st*")))))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "C_0") (STRUCT (FIELD "TYPES" (ITER (VAR "dt") (LISTN (VAR "n")) (DOM "dt" (VAR "dt*")))) (FIELD "TAGS" (LIST)) (FIELD "GLOBALS" (LIST)) (FIELD "MEMS" (LIST)) (FIELD "TABLES" (LIST)) (FIELD "FUNCS" (LIST)) (FIELD "DATAS" (LIST)) (FIELD "ELEMS" (LIST)) (FIELD "LOCALS" (LIST)) (FIELD "LABELS" (LIST)) (FIELD "RETURN" (OPT)) (FIELD "REFS" (LIST)) (FIELD "RECS" (LIST)))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Deftype_ok" "%|-%:OK" (TUP (STRUCT (FIELD "TYPES" (SLICE (ITER (VAR "dt") (LISTN (VAR "n")) (DOM "dt" (VAR "dt*"))) (NUM (NAT 0)) (VAR "i"))) (FIELD "TAGS" (LIST)) (FIELD "GLOBALS" (LIST)) (FIELD "MEMS" (LIST)) (FIELD "TABLES" (LIST)) (FIELD "FUNCS" (LIST)) (FIELD "DATAS" (LIST)) (FIELD "ELEMS" (LIST)) (FIELD "LOCALS" (LIST)) (FIELD "LABELS" (LIST)) (FIELD "RETURN" (OPT)) (FIELD "REFS" (LIST)) (FIELD "RECS" (LIST))) (VAR "dt"))) (LISTN (VAR "n") "i") (DOM "dt" (VAR "dt*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Subtype_ok2" "%|-%:%" (TUP (STRUCT (FIELD "TYPES" (ITER (VAR "dt") (LISTN (VAR "n")) (DOM "dt" (VAR "dt*")))) (FIELD "TAGS" (LIST)) (FIELD "GLOBALS" (LIST)) (FIELD "MEMS" (LIST)) (FIELD "TABLES" (LIST)) (FIELD "FUNCS" (LIST)) (FIELD "DATAS" (LIST)) (FIELD "ELEMS" (LIST)) (FIELD "LOCALS" (LIST)) (FIELD "LABELS" (LIST)) (FIELD "RETURN" (OPT)) (FIELD "REFS" (LIST)) (FIELD "RECS" (ITER (VAR "st") (LISTN (VAR "m")) (DOM "st" (VAR "st*"))))) (VAR "st") (CASE "OK" (VAR "i")))) (LISTN (VAR "m") "i") (DOM "st" (VAR "st*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Tagtype_ok" "%|-%:OK" (TUP (VAR "C_0") (VAR "jt"))) LIST (DOM "jt" (VAR "jt*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Globaltype_ok" "%|-%:OK" (TUP (VAR "C_0") (VAR "gt"))) LIST (DOM "gt" (VAR "gt*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Memtype_ok" "%|-%:OK" (TUP (VAR "C_0") (VAR "mt"))) LIST (DOM "mt" (VAR "mt*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Tabletype_ok" "%|-%:OK" (TUP (VAR "C_0") (VAR "tt"))) LIST (DOM "tt" (VAR "tt*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Deftype_ok" "%|-%:OK" (TUP (VAR "C_0") (VAR "dt_F"))) LIST (DOM "dt_F" (VAR "dt_F*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "condition with unbound variables" (CMP EQ BOOL (LEN (VAR "dt_F*")) (LEN (VAR "t_1*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "condition with unbound variables" (CMP EQ BOOL (LEN (VAR "dt_F*")) (LEN (VAR "t_2*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Expand" "%~~%" (TUP (VAR "dt_F") (CASE "FUNC%->%" (TUP (CASE "%" (TUP (LIST (VAR "t_1")))) (CASE "%" (TUP (LIST (VAR "t_2")))))))) LIST (DOM "dt_F" (VAR "dt_F*")) (DOM "t_1" (VAR "t_1*")) (DOM "t_2" (VAR "t_2*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Reftype_ok" "%|-%:OK" (TUP (VAR "C_0") (VAR "et"))) LIST (DOM "et" (VAR "et*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Localtype_ok" "%|-%:OK" (TUP (VAR "C_0") (VAR "lct"))) LIST (DOM "lct" (VAR "lct*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Resulttype_ok" "%|-%:OK" (TUP (VAR "C_0") (CASE "%" (TUP (ITER (VAR "t") LIST (DOM "t" (VAR "t*"))))))) LIST (DOM "t*" (VAR "t**"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (RULE "Resulttype_ok" "%|-%:OK" (TUP (VAR "C_0") (CASE "%" (TUP (ITER (VAR "t'") LIST (DOM "t'" (VAR "t'*"))))))) OPT (DOM "t'*" (VAR "t'*?"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "iterated premise without inputs" (ITER (IF (CMP LT NAT (PROJ (UNCASE (VAR "x") "%") 0) (LEN (ITER (VAR "dt_F") LIST (DOM "dt_F" (VAR "dt_F*")))))) LIST (DOM "x" (VAR "x*"))) :RULE "Context_ok/" :POS 0 :MODE :FUN)

("CONTEXT_OK" "unbound variable" "C" :RULE "Context_ok/" :POS 0 :MODE :FUN)

("MODULEINST_OK" "condition with unbound variables" (CMP LE NAT (VAR "k") (LEN (ITER (VAR "funcaddr") LIST (DOM "funcaddr" (VAR "funcaddr*"))))) :RULE "Moduleinst_ok/" :POS 0 :MODE :FUN)

("MODULEINST_OK" "unbound variable" "k" :RULE "Moduleinst_ok/" :POS 0 :MODE :FUN)

("MODULEINST_OK" "unbound variable" "subtype*" :RULE "Moduleinst_ok/" :POS 0 :MODE :FUN)

("IMMUTREACHABLE" "condition with unbound variables" (CMP LT NAT (VAR "i") (LEN (DOT (IDX (DOT (VAR "s") "STRUCTS") (VAR "a")) "FIELDS"))) :RULE "ImmutReachable/ref.struct" :POS 1 :MODE :FUN)

("IMMUTREACHABLE" "condition with unbound variables" (CMP LT NAT (VAR "i") (LEN (ITER (VAR "ft") LIST (DOM "ft" (VAR "ft*"))))) :RULE "ImmutReachable/ref.struct" :POS 1 :MODE :FUN)

("IMMUTREACHABLE" "condition with unbound variables" (CMP EQ BOOL (IDX (ITER (VAR "ft") LIST (DOM "ft" (VAR "ft*"))) (VAR "i")) (CASE "%%" (TUP (OPT) (VAR "zt")))) :RULE "ImmutReachable/ref.struct" :POS 1 :MODE :FUN)

("IMMUTREACHABLE" "unbound variable" "i" :RULE "ImmutReachable/ref.struct" :POS 1 :MODE :FUN)

("IMMUTREACHABLE" "condition with unbound variables" (CMP LT NAT (VAR "i") (LEN (DOT (IDX (DOT (VAR "s") "ARRAYS") (VAR "a")) "FIELDS"))) :RULE "ImmutReachable/ref.array" :POS 2 :MODE :FUN)

("IMMUTREACHABLE" "unbound variable" "i" :RULE "ImmutReachable/ref.array" :POS 2 :MODE :FUN)

("IMMUTREACHABLE" "condition with unbound variables" (CMP LT NAT (VAR "i") (LEN (DOT (IDX (DOT (VAR "s") "EXNS") (VAR "a")) "FIELDS"))) :RULE "ImmutReachable/ref.exn" :POS 3 :MODE :FUN)

("IMMUTREACHABLE" "unbound variable" "i" :RULE "ImmutReachable/ref.exn" :POS 3 :MODE :FUN)

("STORE_OK" "condition with unbound variables" (CMP EQ BOOL (LEN (VAR "taginst*")) (LEN (VAR "tagtype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "iterated premise without inputs" (ITER (RULE "Taginst_ok" "%|-%:%" (TUP (VAR "s") (VAR "taginst") (VAR "tagtype"))) LIST (DOM "taginst" (VAR "taginst*")) (DOM "tagtype" (VAR "tagtype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "condition with unbound variables" (CMP EQ BOOL (LEN (VAR "globalinst*")) (LEN (VAR "globaltype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "iterated premise without inputs" (ITER (RULE "Globalinst_ok" "%|-%:%" (TUP (VAR "s") (VAR "globalinst") (VAR "globaltype"))) LIST (DOM "globalinst" (VAR "globalinst*")) (DOM "globaltype" (VAR "globaltype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "condition with unbound variables" (CMP EQ BOOL (LEN (VAR "meminst*")) (LEN (VAR "memtype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "iterated premise without inputs" (ITER (RULE "Meminst_ok" "%|-%:%" (TUP (VAR "s") (VAR "meminst") (VAR "memtype"))) LIST (DOM "meminst" (VAR "meminst*")) (DOM "memtype" (VAR "memtype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "condition with unbound variables" (CMP EQ BOOL (LEN (VAR "tableinst*")) (LEN (VAR "tabletype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "iterated premise without inputs" (ITER (RULE "Tableinst_ok" "%|-%:%" (TUP (VAR "s") (VAR "tableinst") (VAR "tabletype"))) LIST (DOM "tableinst" (VAR "tableinst*")) (DOM "tabletype" (VAR "tabletype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "condition with unbound variables" (CMP EQ BOOL (LEN (VAR "deftype*")) (LEN (VAR "funcinst*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "iterated premise without inputs" (ITER (RULE "Funcinst_ok" "%|-%:%" (TUP (VAR "s") (VAR "funcinst") (VAR "deftype"))) LIST (DOM "deftype" (VAR "deftype*")) (DOM "funcinst" (VAR "funcinst*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "condition with unbound variables" (CMP EQ BOOL (LEN (VAR "datainst*")) (LEN (VAR "datatype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "iterated premise without inputs" (ITER (RULE "Datainst_ok" "%|-%:%" (TUP (VAR "s") (VAR "datainst") (VAR "datatype"))) LIST (DOM "datainst" (VAR "datainst*")) (DOM "datatype" (VAR "datatype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "condition with unbound variables" (CMP EQ BOOL (LEN (VAR "eleminst*")) (LEN (VAR "elemtype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "iterated premise without inputs" (ITER (RULE "Eleminst_ok" "%|-%:%" (TUP (VAR "s") (VAR "eleminst") (VAR "elemtype"))) LIST (DOM "eleminst" (VAR "eleminst*")) (DOM "elemtype" (VAR "elemtype*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "iterated premise without inputs" (ITER (RULE "Structinst_ok" "%|-%:OK" (TUP (VAR "s") (VAR "structinst"))) LIST (DOM "structinst" (VAR "structinst*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "iterated premise without inputs" (ITER (RULE "Arrayinst_ok" "%|-%:OK" (TUP (VAR "s") (VAR "arrayinst"))) LIST (DOM "arrayinst" (VAR "arrayinst*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "iterated premise without inputs" (ITER (RULE "Exninst_ok" "%|-%:OK" (TUP (VAR "s") (VAR "exninst"))) LIST (DOM "exninst" (VAR "exninst*"))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "premise" (ITER (RULE "NotImmutReachable" "~%>>_%%" (TUP (CASE "REF.STRUCT_ADDR" (VAR "a")) (VAR "s") (CASE "REF.STRUCT_ADDR" (VAR "a")))) (LISTN (LEN (ITER (VAR "structinst") LIST (DOM "structinst" (VAR "structinst*")))) "a")) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "premise" (ITER (RULE "NotImmutReachable" "~%>>_%%" (TUP (CASE "REF.ARRAY_ADDR" (VAR "a")) (VAR "s") (CASE "REF.ARRAY_ADDR" (VAR "a")))) (LISTN (LEN (ITER (VAR "arrayinst") LIST (DOM "arrayinst" (VAR "arrayinst*")))) "a")) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "premise" (ITER (RULE "NotImmutReachable" "~%>>_%%" (TUP (CASE "REF.EXN_ADDR" (VAR "a")) (VAR "s") (CASE "REF.EXN_ADDR" (VAR "a")))) (LISTN (LEN (ITER (VAR "exninst") LIST (DOM "exninst" (VAR "exninst*")))) "a")) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "s") (STRUCT (FIELD "TAGS" (ITER (VAR "taginst") LIST (DOM "taginst" (VAR "taginst*")))) (FIELD "GLOBALS" (ITER (VAR "globalinst") LIST (DOM "globalinst" (VAR "globalinst*")))) (FIELD "MEMS" (ITER (VAR "meminst") LIST (DOM "meminst" (VAR "meminst*")))) (FIELD "TABLES" (ITER (VAR "tableinst") LIST (DOM "tableinst" (VAR "tableinst*")))) (FIELD "FUNCS" (ITER (VAR "funcinst") LIST (DOM "funcinst" (VAR "funcinst*")))) (FIELD "DATAS" (ITER (VAR "datainst") LIST (DOM "datainst" (VAR "datainst*")))) (FIELD "ELEMS" (ITER (VAR "eleminst") LIST (DOM "eleminst" (VAR "eleminst*")))) (FIELD "STRUCTS" (ITER (VAR "structinst") LIST (DOM "structinst" (VAR "structinst*")))) (FIELD "ARRAYS" (ITER (VAR "arrayinst") LIST (DOM "arrayinst" (VAR "arrayinst*")))) (FIELD "EXNS" (ITER (VAR "exninst") LIST (DOM "exninst" (VAR "exninst*")))))) :RULE "Store_ok/" :POS 0 :MODE :FUN)

("STORE_OK" "unbound variable" "s" :RULE "Store_ok/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s") "TAGS")))) (LISTN (LEN (DOT (VAR "s") "TAGS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s'") "TAGS")))) (LISTN (LEN (DOT (VAR "s") "TAGS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (RULE "Extend_taginst" "%<=%" (TUP (IDX (DOT (VAR "s") "TAGS") (VAR "a")) (IDX (DOT (VAR "s'") "TAGS") (VAR "a")))) (LISTN (LEN (DOT (VAR "s") "TAGS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s") "GLOBALS")))) (LISTN (LEN (DOT (VAR "s") "GLOBALS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s'") "GLOBALS")))) (LISTN (LEN (DOT (VAR "s") "GLOBALS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (RULE "Extend_globalinst" "%<=%" (TUP (IDX (DOT (VAR "s") "GLOBALS") (VAR "a")) (IDX (DOT (VAR "s'") "GLOBALS") (VAR "a")))) (LISTN (LEN (DOT (VAR "s") "GLOBALS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s") "MEMS")))) (LISTN (LEN (DOT (VAR "s") "MEMS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s'") "MEMS")))) (LISTN (LEN (DOT (VAR "s") "MEMS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (RULE "Extend_meminst" "%<=%" (TUP (IDX (DOT (VAR "s") "MEMS") (VAR "a")) (IDX (DOT (VAR "s'") "MEMS") (VAR "a")))) (LISTN (LEN (DOT (VAR "s") "MEMS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s") "TABLES")))) (LISTN (LEN (DOT (VAR "s") "TABLES")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s'") "TABLES")))) (LISTN (LEN (DOT (VAR "s") "TABLES")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (RULE "Extend_tableinst" "%<=%" (TUP (IDX (DOT (VAR "s") "TABLES") (VAR "a")) (IDX (DOT (VAR "s'") "TABLES") (VAR "a")))) (LISTN (LEN (DOT (VAR "s") "TABLES")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s") "FUNCS")))) (LISTN (LEN (DOT (VAR "s") "FUNCS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s'") "FUNCS")))) (LISTN (LEN (DOT (VAR "s") "FUNCS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (RULE "Extend_funcinst" "%<=%" (TUP (IDX (DOT (VAR "s") "FUNCS") (VAR "a")) (IDX (DOT (VAR "s'") "FUNCS") (VAR "a")))) (LISTN (LEN (DOT (VAR "s") "FUNCS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s") "DATAS")))) (LISTN (LEN (DOT (VAR "s") "DATAS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s'") "DATAS")))) (LISTN (LEN (DOT (VAR "s") "DATAS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (RULE "Extend_datainst" "%<=%" (TUP (IDX (DOT (VAR "s") "DATAS") (VAR "a")) (IDX (DOT (VAR "s'") "DATAS") (VAR "a")))) (LISTN (LEN (DOT (VAR "s") "DATAS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s") "ELEMS")))) (LISTN (LEN (DOT (VAR "s") "ELEMS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s'") "ELEMS")))) (LISTN (LEN (DOT (VAR "s") "ELEMS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (RULE "Extend_eleminst" "%<=%" (TUP (IDX (DOT (VAR "s") "ELEMS") (VAR "a")) (IDX (DOT (VAR "s'") "ELEMS") (VAR "a")))) (LISTN (LEN (DOT (VAR "s") "ELEMS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s") "STRUCTS")))) (LISTN (LEN (DOT (VAR "s") "STRUCTS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s'") "STRUCTS")))) (LISTN (LEN (DOT (VAR "s") "STRUCTS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (RULE "Extend_structinst" "%<=%" (TUP (IDX (DOT (VAR "s") "STRUCTS") (VAR "a")) (IDX (DOT (VAR "s'") "STRUCTS") (VAR "a")))) (LISTN (LEN (DOT (VAR "s") "STRUCTS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s") "ARRAYS")))) (LISTN (LEN (DOT (VAR "s") "ARRAYS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s'") "ARRAYS")))) (LISTN (LEN (DOT (VAR "s") "ARRAYS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (RULE "Extend_arrayinst" "%<=%" (TUP (IDX (DOT (VAR "s") "ARRAYS") (VAR "a")) (IDX (DOT (VAR "s'") "ARRAYS") (VAR "a")))) (LISTN (LEN (DOT (VAR "s") "ARRAYS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s") "EXNS")))) (LISTN (LEN (DOT (VAR "s") "EXNS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (IF (CMP LT NAT (VAR "a") (LEN (DOT (VAR "s'") "EXNS")))) (LISTN (LEN (DOT (VAR "s") "EXNS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "premise" (ITER (RULE "Extend_exninst" "%<=%" (TUP (IDX (DOT (VAR "s") "EXNS") (VAR "a")) (IDX (DOT (VAR "s'") "EXNS") (VAR "a")))) (LISTN (LEN (DOT (VAR "s") "EXNS")) "a")) :RULE "Extend_store/" :POS 0 :MODE :FUN)

("EXTEND_STORE" "unbound variable" "s'" :RULE "Extend_store/" :POS 0 :MODE :FUN)

("NOTATIONTYPINGPREMISEDOTS" "relation with an empty tuple (arity 0)" "NotationTypingPremisedots" :MODE :FUN)

("NOTATIONTYPINGSCHEME" "exp" NIL :RULE "NotationTypingScheme/" :POS 0 :MODE :FUN)

("NOTATIONTYPINGSCHEME" "unbound variable" "conclusion" :RULE "NotationTypingScheme/" :POS 0 :MODE :FUN)

("GRAM/THEXNUM" "grammar symbol" (TEXT "_"))

("GRAM/TSTRINGCHAR" "grammar symbol" (TEXT "\\t"))

("GRAM/TSTRINGCHAR" "grammar symbol" (TEXT "\\n"))

("GRAM/TSTRINGCHAR" "grammar symbol" (TEXT "\\r"))

("GRAM/TSTRINGCHAR" "grammar symbol" (TEXT "\\\""))

("GRAM/TSTRINGCHAR" "grammar symbol" (TEXT "\\'"))

("GRAM/TSTRINGCHAR" "grammar symbol" (TEXT "\\\\"))

("GRAM/TSTRINGCHAR" "grammar symbol" (TEXT "\\u{"))

("GRAM/TSTRINGCHAR" "grammar symbol" (TEXT "}"))

("GRAM/TSTRINGELEM" "grammar symbol" (TEXT "\\"))

("GRAM/TSTRING" "grammar symbol" (TEXT "\""))

("GRAM/TSTRING" "grammar symbol" (TEXT "\""))

("GRAM/TID" "grammar symbol" (TEXT "$"))

("GRAM/TID" "grammar symbol" (TEXT "$"))

("GRAM/TRESERVED" "grammar symbol" (TEXT ","))

("GRAM/TRESERVED" "grammar symbol" (TEXT ";"))

("GRAM/TRESERVED" "grammar symbol" (TEXT "["))

("GRAM/TRESERVED" "grammar symbol" (TEXT "]"))

("GRAM/TRESERVED" "grammar symbol" (TEXT "{"))

("GRAM/TRESERVED" "grammar symbol" (TEXT "}"))

("GRAM/TBLOCKCOMMENT" "grammar symbol" (TEXT "(;"))

("GRAM/TBLOCKCOMMENT" "grammar symbol" (TEXT ";)"))

("GRAM/TBLOCKCHAR" "grammar symbol" (TEXT ";"))

("GRAM/TBLOCKCHAR" "grammar symbol" (TEXT "("))

("GRAM/TEOF" "grammar symbol" (TEXT ""))

("GRAM/TLINECOMMENT" "grammar symbol" (TEXT ";;"))

("GRAM/TSPACE" "grammar symbol" (TEXT " "))

("GRAM/TANNOT" "grammar symbol" (TEXT "(@"))

("GRAM/TANNOT" "grammar symbol" (TEXT ")"))

("GRAM/TSIGN" "grammar symbol" (TEXT "+"))

("GRAM/TSIGN" "grammar symbol" (TEXT "-"))

("GRAM/TNUM" "grammar symbol" (TEXT "_"))

("GRAM/TUN" "grammar symbol" (TEXT "0x"))

("GRAM/TFRAC" "grammar symbol" (TEXT "_"))

("GRAM/THEXFRAC" "grammar symbol" (TEXT "_"))

("GRAM/TMANT" "grammar symbol" (TEXT "."))

("GRAM/TMANT" "grammar symbol" (TEXT "."))

("GRAM/THEXMANT" "grammar symbol" (TEXT "."))

("GRAM/THEXMANT" "grammar symbol" (TEXT "."))

("GRAM/TFLOAT" "grammar symbol" (TEXT "E"))

("GRAM/TFLOAT" "grammar symbol" (TEXT "e"))

("GRAM/THEXFLOAT" "grammar symbol" (TEXT "0x"))

("GRAM/THEXFLOAT" "grammar symbol" (TEXT "P"))

("GRAM/THEXFLOAT" "grammar symbol" (TEXT "p"))

("GRAM/TFNMAG" "grammar symbol" (TEXT "inf"))

("GRAM/TFNMAG" "grammar symbol" (TEXT "nan"))

("GRAM/TFNMAG" "grammar symbol" (TEXT "nan:0x"))

("GRAM/TIDX_" "pattern" (IDX (VAR "ids") (PROJ (UNCASE (VAR "x") "%") 0)))

("GRAM/TIDX_" "unbound variable" "x")

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT "("))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT "tag"))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT ")"))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT "("))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT "global"))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT ")"))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT "("))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT "memory"))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT ")"))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT "("))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT "table"))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT ")"))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT "("))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT "func"))

("GRAM/TEXTERNIDX_" "grammar symbol" (TEXT ")"))

("GRAM/TNUMTYPE" "grammar symbol" (TEXT "i32"))

("GRAM/TNUMTYPE" "grammar symbol" (TEXT "i64"))

("GRAM/TNUMTYPE" "grammar symbol" (TEXT "f32"))

("GRAM/TNUMTYPE" "grammar symbol" (TEXT "f64"))

("GRAM/TVECTYPE" "grammar symbol" (TEXT "v128"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "any"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "eq"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "i31"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "struct"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "array"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "none"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "func"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "nofunc"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "exn"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "noexn"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "extern"))

("GRAM/TABSHEAPTYPE" "grammar symbol" (TEXT "noextern"))

("GRAM/TNULL" "grammar symbol" (TEXT "null"))

("GRAM/TREFTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TREFTYPE_" "grammar symbol" (TEXT "ref"))

("GRAM/TREFTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TPACKTYPE" "grammar symbol" (TEXT "i8"))

("GRAM/TPACKTYPE" "grammar symbol" (TEXT "i16"))

("GRAM/TFIELDTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TFIELDTYPE_" "grammar symbol" (TEXT "mut"))

("GRAM/TFIELDTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TFIELD_" "grammar symbol" (TEXT "("))

("GRAM/TFIELD_" "grammar symbol" (TEXT "field"))

("GRAM/TFIELD_" "grammar symbol" (TEXT ")"))

("GRAM/TPARAM_" "grammar symbol" (TEXT "("))

("GRAM/TPARAM_" "grammar symbol" (TEXT "param"))

("GRAM/TPARAM_" "grammar symbol" (TEXT ")"))

("GRAM/TRESULT_" "grammar symbol" (TEXT "("))

("GRAM/TRESULT_" "grammar symbol" (TEXT "result"))

("GRAM/TRESULT_" "grammar symbol" (TEXT ")"))

("GRAM/TCOMPTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TCOMPTYPE_" "grammar symbol" (TEXT "struct"))

("GRAM/TCOMPTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TCOMPTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TCOMPTYPE_" "grammar symbol" (TEXT "array"))

("GRAM/TCOMPTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TCOMPTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TCOMPTYPE_" "grammar symbol" (TEXT "func"))

("GRAM/TCOMPTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TFINAL" "grammar symbol" (TEXT "final"))

("GRAM/TSUBTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TSUBTYPE_" "grammar symbol" (TEXT "sub"))

("GRAM/TSUBTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TTYPEDEF_" "grammar symbol" (TEXT "("))

("GRAM/TTYPEDEF_" "grammar symbol" (TEXT "type"))

("GRAM/TTYPEDEF_" "grammar symbol" (TEXT ")"))

("GRAM/TRECTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TRECTYPE_" "grammar symbol" (TEXT "rec"))

("GRAM/TRECTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TADDRTYPE" "grammar symbol" (TEXT "i32"))

("GRAM/TADDRTYPE" "grammar symbol" (TEXT "i64"))

("GRAM/TTYPEUSE_" "grammar symbol" (TEXT "("))

("GRAM/TTYPEUSE_" "grammar symbol" (TEXT "type"))

("GRAM/TTYPEUSE_" "grammar symbol" (TEXT ")"))

("GRAM/TTYPEUSE_" "grammar symbol" (TEXT "("))

("GRAM/TTYPEUSE_" "grammar symbol" (TEXT "type"))

("GRAM/TTYPEUSE_" "grammar symbol" (TEXT ")"))

("GRAM/TGLOBALTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TGLOBALTYPE_" "grammar symbol" (TEXT "mut"))

("GRAM/TGLOBALTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT "tag"))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT "global"))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT "memory"))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT "table"))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT "("))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT "func"))

("GRAM/TEXTERNTYPE_" "grammar symbol" (TEXT ")"))

("GRAM/TLABEL_" "pattern" (IDX (DOT (VAR "I") "LABELS") (PROJ (UNCASE (VAR "x") "%") 0)))

("GRAM/TLABEL_" "unbound variable" "x")

("GRAM/TCATCH_" "grammar symbol" (TEXT "("))

("GRAM/TCATCH_" "grammar symbol" (TEXT "catch"))

("GRAM/TCATCH_" "grammar symbol" (TEXT ")"))

("GRAM/TCATCH_" "grammar symbol" (TEXT "("))

("GRAM/TCATCH_" "grammar symbol" (TEXT "catch_ref"))

("GRAM/TCATCH_" "grammar symbol" (TEXT ")"))

("GRAM/TCATCH_" "grammar symbol" (TEXT "("))

("GRAM/TCATCH_" "grammar symbol" (TEXT "catch_all"))

("GRAM/TCATCH_" "grammar symbol" (TEXT ")"))

("GRAM/TCATCH_" "grammar symbol" (TEXT "("))

("GRAM/TCATCH_" "grammar symbol" (TEXT "catch_all_ref"))

("GRAM/TCATCH_" "grammar symbol" (TEXT ")"))

("GRAM/TALIGN_" "grammar symbol" (TEXT "align="))

("GRAM/TALIGN_" "pattern" (BIN POW NAT (NUM (NAT 2)) (VAR "n")))

("GRAM/TALIGN_" "unbound variable" "n")

("GRAM/TALIGN_" "pattern" (BIN POW NAT (NUM (NAT 2)) (VAR "n")))

("GRAM/TALIGN_" "unbound variable" "n")

("GRAM/TOFFSET" "grammar symbol" (TEXT "offset="))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "unreachable"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "nop"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "drop"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "select"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "br"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "br_if"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "br_table"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "br_on_null"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "br_on_non_null"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "br_on_cast"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "br_on_cast_fail"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "call"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "call_ref"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "call_indirect"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "return"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "return_call"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "return_call_ref"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "return_call_indirect"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "throw"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "throw_ref"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "local.get"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "local.set"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "local.tee"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "global.get"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "global.set"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "table.get"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "table.set"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "table.size"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "table.grow"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "table.fill"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "table.copy"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "table.init"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "elem.drop"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.load"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.load"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.load"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.load"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.load8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.load8_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.load16_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.load16_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.load8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.load8_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.load16_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.load16_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.load32_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.load32_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load8x8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load8x8_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load16x4_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load16x4_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load32x2_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load32x2_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load8_splat"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load16_splat"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load32_splat"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load64_splat"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load32_zero"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load64_zero"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load8_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load16_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load32_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.load64_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.store"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.store"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.store"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.store"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.store8"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.store16"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.store8"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.store16"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.store32"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.store"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.store8_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.store16_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.store32_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.store64_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "memory.size"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "memory.grow"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "memory.fill"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "memory.copy"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "memory.init"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "data.drop"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "ref.null"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "ref.func"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "ref.is_null"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "ref.as_non_null"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "ref.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "ref.test"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "ref.cast"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "ref.i31"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i31.get_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i31.get_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "struct.new"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "struct.new_default"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "struct.get"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "struct.get_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "struct.get_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "struct.set"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.new"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.new_default"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.new_fixed"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.new_data"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.new_elem"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.get"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.get_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.get_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.set"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.len"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.fill"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.copy"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.init_data"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "array.init_elem"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "any.convert_extern"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "extern.convert_any"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.const"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.const"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.const"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.const"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.eqz"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.eqz"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.ne"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.lt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.lt_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.gt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.gt_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.le_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.le_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.ge_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.ge_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.ne"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.lt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.lt_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.gt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.gt_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.le_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.le_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.ge_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.ge_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.ne"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.lt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.gt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.le"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.ge"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.ne"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.lt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.gt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.le"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.ge"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.clz"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.ctz"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.popcnt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.extend8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.extend16_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.clz"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.ctz"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.popcnt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.extend8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.extend16_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.extend32_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.abs"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.neg"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.sqrt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.ceil"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.floor"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.trunc"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.nearest"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.abs"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.neg"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.sqrt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.ceil"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.floor"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.trunc"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.nearest"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.add"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.sub"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.mul"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.div_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.div_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.rem_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.rem_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.and"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.or"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.xor"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.shl"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.shr_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.shr_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.rotl"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.rotr"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.add"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.sub"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.mul"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.div_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.div_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.rem_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.rem_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.and"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.or"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.xor"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.shl"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.shr_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.shr_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.rotl"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.rotr"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.add"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.sub"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.mul"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.div"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.min"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.max"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.copysign"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.add"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.sub"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.mul"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.div"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.min"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.max"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.copysign"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.wrap_i64"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.trunc_f32_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.trunc_f32_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.trunc_f64_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.trunc_f64_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.trunc_sat_f32_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.trunc_sat_f32_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.trunc_sat_f64_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.trunc_sat_f64_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.extend_i32_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.extend_i32_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.trunc_f32_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.trunc_f32_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.trunc_f64_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.trunc_f64_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.trunc_sat_f32_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.trunc_sat_f32_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.trunc_sat_f64_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.trunc_sat_f64_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.demote_f64"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.convert_i32_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.convert_i32_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.convert_i64_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.convert_i64_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.promote_f32"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.convert_i32_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.convert_i32_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.convert_i64_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.convert_i64_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32.reinterpret_f32"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64.reinterpret_f64"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32.reinterpret_i32"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64.reinterpret_i64"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.const"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.const"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.const"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.const"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.const"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.const"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.shuffle"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.swizzle"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.relaxed_swizzle"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.splat"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.splat"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.splat"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.splat"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.splat"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.splat"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.extract_lane_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.extract_lane_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extract_lane_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extract_lane_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extract_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.extract_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.extract_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.extract_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.replace_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.replace_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.replace_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.replace_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.replace_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.replace_lane"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.any_true"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.all_true"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.all_true"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.all_true"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.all_true"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.ne"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.lt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.lt_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.gt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.gt_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.le_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.le_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.ge_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.ge_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.ne"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.lt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.lt_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.gt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.gt_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.le_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.le_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.ge_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.ge_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.ne"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.lt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.lt_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.gt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.gt_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.le_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.le_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.ge_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.ge_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.ne"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.lt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.gt_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.le_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.ge_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.ne"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.lt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.gt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.le"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.ge"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.eq"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.ne"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.lt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.gt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.le"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.ge"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.not"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.abs"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.neg"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.popcnt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.abs"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.neg"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.abs"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.neg"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.abs"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.neg"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.abs"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.neg"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.sqrt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.ceil"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.floor"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.trunc"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.nearest"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.abs"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.neg"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.sqrt"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.ceil"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.floor"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.trunc"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.nearest"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.and"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.andnot"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.or"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.xor"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.add"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.add_sat_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.add_sat_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.sub"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.sub_sat_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.sub_sat_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.min_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.min_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.max_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.max_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.avgr_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.add"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.add_sat_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.add_sat_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.sub"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.sub_sat_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.sub_sat_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.mul"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.min_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.min_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.max_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.max_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.avgr_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.q15mulr_sat_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.relaxed_q15mulr_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.add"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.sub"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.mul"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.min_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.min_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.max_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.max_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.add"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.sub"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.mul"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.add"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.sub"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.mul"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.div"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.min"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.max"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.pmin"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.pmax"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.relaxed_min"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.relaxed_max"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.add"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.sub"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.mul"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.div"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.min"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.max"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.pmin"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.pmax"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.relaxed_min"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.relaxed_max"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "v128.bitselect"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.relaxed_laneselect"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.relaxed_laneselect"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.relaxed_laneselect"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.relaxed_laneselect"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.relaxed_madd"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.relaxed_nmadd"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.relaxed_madd"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.relaxed_nmadd"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.shl"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.shr_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.shr_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.shl"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.shr_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.shr_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.shl"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.shr_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.shr_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.shl"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.shr_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.shr_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.bitmask"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.bitmask"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.bitmask"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.bitmask"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.narrow_i16x8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i8x16.narrow_i16x8_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.narrow_i32x4_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.narrow_i32x4_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extend_low_i8x16_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extend_low_i8x16_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extend_high_i8x16_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extend_high_i8x16_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extend_low_i16x8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extend_low_i16x8_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extend_high_i16x8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extend_high_i16x8_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.trunc_sat_f32x4_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.trunc_sat_f32x4_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.trunc_sat_f64x2_s_zero"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.trunc_sat_f64x2_u_zero"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.relaxed_trunc_f32x4_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.relaxed_trunc_f32x4_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.relaxed_trunc_f64x2_s_zero"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.relaxed_trunc_f64x2_u_zero"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.extend_low_i32x4_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.extend_low_i32x4_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.extend_high_i32x4_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.extend_high_i32x4_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.demote_f64x2_zero"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.convert_i32x4_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f32x4.convert_i32x4_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.promote_low_f32x4"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.convert_low_i32x4_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "f64x2.convert_low_i32x4_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extadd_pairwise_i8x16_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extadd_pairwise_i8x16_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extadd_pairwise_i16x8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extadd_pairwise_i16x8_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extmul_low_i8x16_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extmul_low_i8x16_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extmul_high_i8x16_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.extmul_high_i8x16_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i16x8.relaxed_dot_i8x16_i7x16_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extmul_low_i16x8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extmul_low_i16x8_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extmul_high_i16x8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.extmul_high_i16x8_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.dot_i16x8_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.extmul_low_i32x4_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.extmul_low_i32x4_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.extmul_high_i32x4_s"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i64x2.extmul_high_i32x4_u"))

("GRAM/TPLAININSTR_" "grammar symbol" (TEXT "i32x4.relaxed_dot_i8x16_i7x16_add_s"))

("GRAM/TBLOCKINSTR_" "grammar symbol" (TEXT "block"))

("GRAM/TBLOCKINSTR_" "grammar symbol" (TEXT "end"))

("GRAM/TBLOCKINSTR_" "grammar symbol" (TEXT "loop"))

("GRAM/TBLOCKINSTR_" "grammar symbol" (TEXT "end"))

("GRAM/TBLOCKINSTR_" "grammar symbol" (TEXT "if"))

("GRAM/TBLOCKINSTR_" "grammar symbol" (TEXT "else"))

("GRAM/TBLOCKINSTR_" "grammar symbol" (TEXT "end"))

("GRAM/TBLOCKINSTR_" "grammar symbol" (TEXT "try_table"))

("GRAM/TBLOCKINSTR_" "grammar symbol" (TEXT "end"))

("GRAM/TTAG_" "grammar symbol" (TEXT "("))

("GRAM/TTAG_" "grammar symbol" (TEXT "tag"))

("GRAM/TTAG_" "grammar symbol" (TEXT ")"))

("GRAM/TGLOBAL_" "grammar symbol" (TEXT "("))

("GRAM/TGLOBAL_" "grammar symbol" (TEXT "global"))

("GRAM/TGLOBAL_" "grammar symbol" (TEXT ")"))

("GRAM/TMEM_" "grammar symbol" (TEXT "("))

("GRAM/TMEM_" "grammar symbol" (TEXT "memory"))

("GRAM/TMEM_" "grammar symbol" (TEXT ")"))

("GRAM/TTABLE_" "grammar symbol" (TEXT "("))

("GRAM/TTABLE_" "grammar symbol" (TEXT "table"))

("GRAM/TTABLE_" "grammar symbol" (TEXT ")"))

("GRAM/TLOCAL_" "grammar symbol" (TEXT "("))

("GRAM/TLOCAL_" "grammar symbol" (TEXT "local"))

("GRAM/TLOCAL_" "grammar symbol" (TEXT ")"))

("GRAM/TFUNC_" "grammar symbol" (TEXT "("))

("GRAM/TFUNC_" "grammar symbol" (TEXT "func"))

("GRAM/TFUNC_" "unbound variable" "I'")

("GRAM/TFUNC_" "grammar symbol" (TEXT ")"))

("GRAM/TMEMUSE_" "grammar symbol" (TEXT "("))

("GRAM/TMEMUSE_" "grammar symbol" (TEXT "memory"))

("GRAM/TMEMUSE_" "grammar symbol" (TEXT ")"))

("GRAM/TOFFSETEXPR_" "grammar symbol" (TEXT "("))

("GRAM/TOFFSETEXPR_" "grammar symbol" (TEXT "offset"))

("GRAM/TOFFSETEXPR_" "grammar symbol" (TEXT ")"))

("GRAM/TDATA_" "grammar symbol" (TEXT "("))

("GRAM/TDATA_" "grammar symbol" (TEXT "data"))

("GRAM/TDATA_" "grammar symbol" (TEXT ")"))

("GRAM/TDATA_" "grammar symbol" (TEXT "("))

("GRAM/TDATA_" "grammar symbol" (TEXT "data"))

("GRAM/TDATA_" "grammar symbol" (TEXT ")"))

("GRAM/TELEMEXPR_" "grammar symbol" (TEXT "("))

("GRAM/TELEMEXPR_" "grammar symbol" (TEXT "item"))

("GRAM/TELEMEXPR_" "grammar symbol" (TEXT ")"))

("GRAM/TTABLEUSE_" "grammar symbol" (TEXT "("))

("GRAM/TTABLEUSE_" "grammar symbol" (TEXT "table"))

("GRAM/TTABLEUSE_" "grammar symbol" (TEXT ")"))

("GRAM/TELEM_" "grammar symbol" (TEXT "("))

("GRAM/TELEM_" "grammar symbol" (TEXT "elem"))

("GRAM/TELEM_" "grammar symbol" (TEXT ")"))

("GRAM/TELEM_" "grammar symbol" (TEXT "("))

("GRAM/TELEM_" "grammar symbol" (TEXT "elem"))

("GRAM/TELEM_" "grammar symbol" (TEXT ")"))

("GRAM/TELEM_" "grammar symbol" (TEXT "("))

("GRAM/TELEM_" "grammar symbol" (TEXT "elem"))

("GRAM/TELEM_" "grammar symbol" (TEXT "declare"))

("GRAM/TELEM_" "grammar symbol" (TEXT ")"))

("GRAM/TSTART_" "grammar symbol" (TEXT "("))

("GRAM/TSTART_" "grammar symbol" (TEXT "start"))

("GRAM/TSTART_" "grammar symbol" (TEXT ")"))

("GRAM/TIMPORT_" "grammar symbol" (TEXT "("))

("GRAM/TIMPORT_" "grammar symbol" (TEXT "import"))

("GRAM/TIMPORT_" "grammar symbol" (TEXT ")"))

("GRAM/TEXPORT_" "grammar symbol" (TEXT "("))

("GRAM/TEXPORT_" "grammar symbol" (TEXT "export"))

("GRAM/TEXPORT_" "grammar symbol" (TEXT ")"))

("GRAM/TEXPORTDOTS" "grammar symbol" (TEXT "("))

("GRAM/TEXPORTDOTS" "grammar symbol" (TEXT "export"))

("GRAM/TEXPORTDOTS" "grammar symbol" (TEXT ")"))

("GRAM/TIMPORTDOTS" "grammar symbol" (TEXT "("))

("GRAM/TIMPORTDOTS" "grammar symbol" (TEXT "import"))

("GRAM/TIMPORTDOTS" "grammar symbol" (TEXT ")"))

("GRAM/TEXPORTMEMDOTS_" "grammar symbol" (TEXT "("))

("GRAM/TEXPORTMEMDOTS_" "grammar symbol" (TEXT "data"))

("GRAM/TEXPORTMEMDOTS_" "grammar symbol" (TEXT ")"))

("GRAM/TEXPORTTABLEDOTS_" "grammar symbol" (TEXT "("))

("GRAM/TEXPORTTABLEDOTS_" "grammar symbol" (TEXT "elem"))

("GRAM/TEXPORTTABLEDOTS_" "grammar symbol" (TEXT ")"))

("GRAM/TMODULE" "grammar symbol" (TEXT "("))

("GRAM/TMODULE" "grammar symbol" (TEXT "module"))

("GRAM/TMODULE" "unbound variable" "I'")

("GRAM/TMODULE" "grammar symbol" (TEXT ")"))

