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

("$VEXTUNOP__" "higher-order argument" (DEF "ivadd_pairwise_"))

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

("STEP_READ" "iterated premise without inputs" (ITER (IF (CMP EQ BOOL (CALL "ibytes_" (EXP (VAR "K")) (EXP (VAR "j"))) (SLICE (DOT (CALL "mem" (EXP (VAR "z")) (EXP (VAR "x"))) "BYTES") (BIN ADD NAT (BIN ADD NAT (PROJ (UNCASE (VAR "i") "%") 0) (PROJ (UNCASE (DOT (VAR "ao") "OFFSET") "%") 0)) (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (BIN MUL NAT (VAR "k") (VAR "K"))) (CVT NAT RAT (NUM (NAT 8)))))) (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (VAR "K")) (CVT NAT RAT (NUM (NAT 8)))))))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0) "k") (DOM "j" (VAR "j*"))) :RULE "Step_read/vload-pack-val" :POS 45 :MODE :FUN)

("STEP_READ" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (ITER (CALL "extend__" (EXP (VAR "K")) (EXP (CALL "jsizenn" (EXP (VAR "Jnn")))) (EXP (VAR "sx")) (EXP (VAR "j"))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0)) (DOM "j" (VAR "j*")))))) :RULE "Step_read/vload-pack-val" :POS 45 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/vload-pack-val" :POS 45 :MODE :FUN)

("STEP_READ" "premise" (ITER (IF (CMP NE BOOL (CALL "cunpack" (EXP (VAR "zt"))) (OPT))) (LISTN (VAR "n"))) :RULE "Step_read/array.new_data-num" :POS 76 :MODE :FUN)

("STEP_READ" "unbound variable" "c*" :RULE "Step_read/array.new_data-num" :POS 76 :MODE :FUN)

("STEP_READ" "unbound variable" "c*" :RULE "Step_read/array.new_data-num" :POS 76 :MODE :FUN)

("STEP_READ" "unbound variable" "c*" :RULE "Step_read/array.new_data-num" :POS 76 :MODE :FUN)

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

