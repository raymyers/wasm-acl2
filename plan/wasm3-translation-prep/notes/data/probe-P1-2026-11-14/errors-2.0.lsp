; Every error logged by translator phase 1 (make probe).
; One per line: (function kind detail [:rule "Rel/id" :pos k] [:mode m]).
("$VRELOP_" "pattern" (CALL "isize" (EXP (VAR "Inn"))))

("$VRELOP_" "condition with unbound variables" (CMP EQ BOOL (VAR "v128") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn")) (VAR "M")))) (EXP (ITER (CASE "%" (TUP (PROJ (UNCASE (VAR "lane_3") "%") 0))) LIST (DOM "lane_3" (VAR "lane_3*")))))))

("$VRELOP_" "unbound variable" "v128")

("$VRELOP_" "pattern" (CALL "isize" (EXP (VAR "Inn"))))

("$VRELOP_" "condition with unbound variables" (CMP EQ BOOL (VAR "v128") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn")) (VAR "M")))) (EXP (ITER (CASE "%" (TUP (PROJ (UNCASE (VAR "lane_3") "%") 0))) LIST (DOM "lane_3" (VAR "lane_3*")))))))

("$VRELOP_" "unbound variable" "v128")

("$VRELOP_" "pattern" (CALL "isize" (EXP (VAR "Inn"))))

("$VRELOP_" "condition with unbound variables" (CMP EQ BOOL (VAR "v128") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn")) (VAR "M")))) (EXP (ITER (CASE "%" (TUP (PROJ (UNCASE (VAR "lane_3") "%") 0))) LIST (DOM "lane_3" (VAR "lane_3*")))))))

("$VRELOP_" "unbound variable" "v128")

("$VRELOP_" "pattern" (CALL "isize" (EXP (VAR "Inn"))))

("$VRELOP_" "condition with unbound variables" (CMP EQ BOOL (VAR "v128") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn")) (VAR "M")))) (EXP (ITER (CASE "%" (TUP (PROJ (UNCASE (VAR "lane_3") "%") 0))) LIST (DOM "lane_3" (VAR "lane_3*")))))))

("$VRELOP_" "unbound variable" "v128")

("$VRELOP_" "pattern" (CALL "isize" (EXP (VAR "Inn"))))

("$VRELOP_" "condition with unbound variables" (CMP EQ BOOL (VAR "v128") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn")) (VAR "M")))) (EXP (ITER (CASE "%" (TUP (PROJ (UNCASE (VAR "lane_3") "%") 0))) LIST (DOM "lane_3" (VAR "lane_3*")))))))

("$VRELOP_" "unbound variable" "v128")

("$VRELOP_" "pattern" (CALL "isize" (EXP (VAR "Inn"))))

("$VRELOP_" "condition with unbound variables" (CMP EQ BOOL (VAR "v128") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn")) (VAR "M")))) (EXP (ITER (CASE "%" (TUP (PROJ (UNCASE (VAR "lane_3") "%") 0))) LIST (DOM "lane_3" (VAR "lane_3*")))))))

("$VRELOP_" "unbound variable" "v128")

("$VEXTUNOP__" "pattern" (CALL "concat_" (TYP (VAR "iN" (EXP (CALL "lsizenn1" (EXP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn_1"))))))) (EXP (ITER (LIST (VAR "cj_1") (VAR "cj_2")) LIST (DOM "cj_1" (VAR "cj_1*")) (DOM "cj_2" (VAR "cj_2*"))))))

("$VEXTUNOP__" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn_1")) (VAR "M_1")))) (EXP (ITER (CALL "iadd_" (EXP (CALL "lsizenn1" (EXP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn_1"))))) (EXP (VAR "cj_1")) (EXP (VAR "cj_2"))) LIST (DOM "cj_1" (VAR "cj_1*")) (DOM "cj_2" (VAR "cj_2*")))))))

("$VEXTUNOP__" "unbound variable" "c")

("$VEXTBINOP__" "pattern" (CALL "concat_" (TYP (VAR "iN" (EXP (CALL "lsizenn1" (EXP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn_1"))))))) (EXP (ITER (LIST (VAR "cj_1") (VAR "cj_2")) LIST (DOM "cj_1" (VAR "cj_1*")) (DOM "cj_2" (VAR "cj_2*"))))))

("$VEXTBINOP__" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn_1")) (VAR "M_1")))) (EXP (ITER (CALL "iadd_" (EXP (CALL "lsizenn1" (EXP (SUB (VAR "Inn") (VAR "lanetype") (VAR "Inn_1"))))) (EXP (VAR "cj_1")) (EXP (VAR "cj_2"))) LIST (DOM "cj_1" (VAR "cj_1*")) (DOM "cj_2" (VAR "cj_2*")))))))

("$VEXTBINOP__" "unbound variable" "c")

("INSTR_OK" "unbound variable" "t_1*" :RULE "Instr_ok/unreachable" :POS 1 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_2*" :RULE "Instr_ok/unreachable" :POS 1 :MODE :FUN)

("INSTR_OK" "unbound variable" "t" :RULE "Instr_ok/drop" :POS 2 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Valtype_sub" "|-%<:%" (TUP (VAR "t") (VAR "t'"))) :RULE "Instr_ok/select-impl" :POS 4 :MODE :FUN)

("INSTR_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "t'") (SUB (VAR "numtype") (VAR "valtype") (VAR "numtype"))) :RULE "Instr_ok/select-impl" :POS 4 :MODE :FUN)

("INSTR_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "t'") (SUB (VAR "vectype") (VAR "valtype") (VAR "vectype"))) :RULE "Instr_ok/select-impl" :POS 4 :MODE :FUN)

("INSTR_OK" "unbound variable" "t" :RULE "Instr_ok/select-impl" :POS 4 :MODE :FUN)

("INSTR_OK" "unbound variable" "t" :RULE "Instr_ok/select-impl" :POS 4 :MODE :FUN)

("INSTR_OK" "unbound variable" "t" :RULE "Instr_ok/select-impl" :POS 4 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_1*" :RULE "Instr_ok/br" :POS 8 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_2*" :RULE "Instr_ok/br" :POS 8 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Resulttype_sub" "|-%<:%" (TUP (CASE "%" (TUP (ITER (VAR "t") LIST (DOM "t" (VAR "t*"))))) (IDX (DOT (VAR "C") "LABELS") (PROJ (UNCASE (VAR "l") "%") 0)))) :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Resulttype_sub" "|-%<:%" (TUP (CASE "%" (TUP (ITER (VAR "t") LIST (DOM "t" (VAR "t*"))))) (IDX (DOT (VAR "C") "LABELS") (PROJ (UNCASE (VAR "l'") "%") 0)))) :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_1*" :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "unbound variable" "t*" :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_2*" :RULE "Instr_ok/br_table" :POS 10 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_1*" :RULE "Instr_ok/return" :POS 13 :MODE :FUN)

("INSTR_OK" "unbound variable" "t_2*" :RULE "Instr_ok/return" :POS 13 :MODE :FUN)

("INSTR_OK" "unbound variable" "rt" :RULE "Instr_ok/ref.is_null" :POS 23 :MODE :FUN)

("INSTRS_OK" "checker relation with unbound arguments" (RULE "Resulttype_sub" "|-%<:%" (TUP (CASE "%" (TUP (ITER (VAR "t'_1") LIST (DOM "t'_1" (VAR "t'_1*"))))) (CASE "%" (TUP (ITER (VAR "t_1") LIST (DOM "t_1" (VAR "t_1*"))))))) :RULE "Instrs_ok/sub" :POS 3 :MODE :FUN)

("INSTRS_OK" "checker relation with unbound arguments" (RULE "Resulttype_sub" "|-%<:%" (TUP (CASE "%" (TUP (ITER (VAR "t_2") LIST (DOM "t_2" (VAR "t_2*"))))) (CASE "%" (TUP (ITER (VAR "t'_2") LIST (DOM "t'_2" (VAR "t'_2*"))))))) :RULE "Instrs_ok/sub" :POS 3 :MODE :FUN)

("INSTRS_OK" "unbound variable" "t'_1*" :RULE "Instrs_ok/sub" :POS 3 :MODE :FUN)

("INSTRS_OK" "unbound variable" "t'_2*" :RULE "Instrs_ok/sub" :POS 3 :MODE :FUN)

("INSTRS_OK" "unbound variable" "t*" :RULE "Instrs_ok/frame" :POS 4 :MODE :FUN)

("INSTRS_OK" "unbound variable" "t*" :RULE "Instrs_ok/frame" :POS 4 :MODE :FUN)

("INSTR_OK" "checker relation with unbound arguments" (RULE "Valtype_sub" "|-%<:%" (TUP (VAR "t") (VAR "t'"))) :RULE "Instr_ok/select-impl" :POS 4 :MODE :CHECK)

("INSTR_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "t'") (SUB (VAR "numtype") (VAR "valtype") (VAR "numtype"))) :RULE "Instr_ok/select-impl" :POS 4 :MODE :CHECK)

("INSTR_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "t'") (SUB (VAR "vectype") (VAR "valtype") (VAR "vectype"))) :RULE "Instr_ok/select-impl" :POS 4 :MODE :CHECK)

("INSTRS_OK" "relation inputs unbound" (RULE "Instrs_ok" "%|-%:%" (TUP (VAR "C") (ITER (VAR "instr") LIST (DOM "instr" (VAR "instr*"))) (CASE "%->%" (TUP (CASE "%" (TUP (ITER (VAR "t_1") LIST (DOM "t_1" (VAR "t_1*"))))) (CASE "%" (TUP (ITER (VAR "t_2") LIST (DOM "t_2" (VAR "t_2*"))))))))) :RULE "Instrs_ok/sub" :POS 3 :MODE :CHECK)

("INSTRS_OK" "checker relation with unbound arguments" (RULE "Resulttype_sub" "|-%<:%" (TUP (CASE "%" (TUP (ITER (VAR "t'_1") LIST (DOM "t'_1" (VAR "t'_1*"))))) (CASE "%" (TUP (ITER (VAR "t_1") LIST (DOM "t_1" (VAR "t_1*"))))))) :RULE "Instrs_ok/sub" :POS 3 :MODE :CHECK)

("INSTRS_OK" "checker relation with unbound arguments" (RULE "Resulttype_sub" "|-%<:%" (TUP (CASE "%" (TUP (ITER (VAR "t_2") LIST (DOM "t_2" (VAR "t_2*"))))) (CASE "%" (TUP (ITER (VAR "t'_2") LIST (DOM "t'_2" (VAR "t'_2*"))))))) :RULE "Instrs_ok/sub" :POS 3 :MODE :CHECK)

("MODULE_OK" "pattern" (LEN (VAR "gt*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Global_ok" "%|-%:%" (TUP (VAR "C'") (VAR "global") (VAR "gt"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Global_ok" "%|-%:%" (TUP (VAR "C'") (VAR "global") (VAR "gt"))) LIST (DOM "global" (VAR "global*")) (DOM "gt" (VAR "gt*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "tt*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Table_ok" "%|-%:%" (TUP (VAR "C'") (VAR "table") (VAR "tt"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Table_ok" "%|-%:%" (TUP (VAR "C'") (VAR "table") (VAR "tt"))) LIST (DOM "table" (VAR "table*")) (DOM "tt" (VAR "tt*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "mt*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Mem_ok" "%|-%:%" (TUP (VAR "C'") (VAR "mem") (VAR "mt"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Mem_ok" "%|-%:%" (TUP (VAR "C'") (VAR "mem") (VAR "mt"))) LIST (DOM "mem" (VAR "mem*")) (DOM "mt" (VAR "mt*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "rt*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Elem_ok" "%|-%:%" (TUP (VAR "C'") (VAR "elem") (VAR "rt"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Elem_ok" "%|-%:%" (TUP (VAR "C'") (VAR "elem") (VAR "rt"))) LIST (DOM "elem" (VAR "elem*")) (DOM "rt" (VAR "rt*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "checker relation with unbound arguments" (RULE "Data_ok" "%|-%:OK" (TUP (VAR "C'") (VAR "data"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "ft*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Func_ok" "%|-%:%" (TUP (VAR "C") (VAR "func") (VAR "ft"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Func_ok" "%|-%:%" (TUP (VAR "C") (VAR "func") (VAR "ft"))) LIST (DOM "ft" (VAR "ft*")) (DOM "func" (VAR "func*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "checker relation with unbound arguments" (RULE "Start_ok" "%|-%:OK" (TUP (VAR "C") (VAR "start"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "nm*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "pattern" (LEN (VAR "xt*")) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "relation inputs unbound" (RULE "Export_ok" "%|-%:%%" (TUP (VAR "C") (VAR "export") (VAR "nm") (VAR "xt"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "iterated premise output not bound" (ITER (RULE "Export_ok" "%|-%:%%" (TUP (VAR "C") (VAR "export") (VAR "nm") (VAR "xt"))) LIST (DOM "export" (VAR "export*")) (DOM "nm" (VAR "nm*")) (DOM "xt" (VAR "xt*"))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "condition with unbound variables" (CMP LE NAT (LEN (ITER (VAR "mt") LIST (DOM "mt" (VAR "mt*")))) (NUM (NAT 1))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "condition with unbound variables" (CALL "disjoint_" (TYP (VAR "name")) (EXP (ITER (VAR "nm") LIST (DOM "nm" (VAR "nm*"))))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "C") (STRUCT (FIELD "TYPES" (ITER (VAR "ft'") LIST (DOM "ft'" (VAR "ft'*")))) (FIELD "FUNCS" (CAT (ITER (VAR "ift") LIST (DOM "ift" (VAR "ift*"))) (ITER (VAR "ft") LIST (DOM "ft" (VAR "ft*"))))) (FIELD "GLOBALS" (CAT (ITER (VAR "igt") LIST (DOM "igt" (VAR "igt*"))) (ITER (VAR "gt") LIST (DOM "gt" (VAR "gt*"))))) (FIELD "TABLES" (CAT (ITER (VAR "itt") LIST (DOM "itt" (VAR "itt*"))) (ITER (VAR "tt") LIST (DOM "tt" (VAR "tt*"))))) (FIELD "MEMS" (CAT (ITER (VAR "imt") LIST (DOM "imt" (VAR "imt*"))) (ITER (VAR "mt") LIST (DOM "mt" (VAR "mt*"))))) (FIELD "ELEMS" (ITER (VAR "rt") LIST (DOM "rt" (VAR "rt*")))) (FIELD "DATAS" (ITER (CASE "OK" (TUP)) (LISTN (VAR "n")))) (FIELD "LOCALS" (LIST)) (FIELD "LABELS" (LIST)) (FIELD "RETURN" (OPT)))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "condition with unbound variables" (CMP EQ BOOL (VAR "C'") (STRUCT (FIELD "TYPES" (ITER (VAR "ft'") LIST (DOM "ft'" (VAR "ft'*")))) (FIELD "FUNCS" (CAT (ITER (VAR "ift") LIST (DOM "ift" (VAR "ift*"))) (ITER (VAR "ft") LIST (DOM "ft" (VAR "ft*"))))) (FIELD "GLOBALS" (ITER (VAR "igt") LIST (DOM "igt" (VAR "igt*")))) (FIELD "TABLES" (CAT (ITER (VAR "itt") LIST (DOM "itt" (VAR "itt*"))) (ITER (VAR "tt") LIST (DOM "tt" (VAR "tt*"))))) (FIELD "MEMS" (CAT (ITER (VAR "imt") LIST (DOM "imt" (VAR "imt*"))) (ITER (VAR "mt") LIST (DOM "mt" (VAR "mt*"))))) (FIELD "ELEMS" (LIST)) (FIELD "DATAS" (LIST)) (FIELD "LOCALS" (LIST)) (FIELD "LABELS" (LIST)) (FIELD "RETURN" (OPT)))) :RULE "Module_ok/" :POS 0 :MODE :FUN)

("MODULE_OK" "unbound variable" "xt*" :RULE "Module_ok/" :POS 0 :MODE :FUN)

("STEP_PURE" "pattern" (CALL "ibits_" (EXP (NUM (NAT 32))) (EXP (VAR "ci"))) :RULE "Step_pure/vbitmask" :POS 42 :MODE :FUN)

("STEP_PURE" "unbound variable" "ci" :RULE "Step_pure/vbitmask" :POS 42 :MODE :FUN)

("STEP_PURE" "premise" (ITER (IF (CMP LT NAT (PROJ (UNCASE (IDX (ITER (VAR "ci") LIST (DOM "ci" (VAR "ci*"))) (VAR "k")) "%") 0) (LEN (ITER (VAR "c'") LIST (DOM "c'" (VAR "c'*")))))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0) "k")) :RULE "Step_pure/vswizzle" :POS 43 :MODE :FUN)

("STEP_PURE" "premise" (ITER (IF (CMP LT NAT (VAR "k") (LEN (ITER (VAR "ci") LIST (DOM "ci" (VAR "ci*")))))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0) "k")) :RULE "Step_pure/vswizzle" :POS 43 :MODE :FUN)

("STEP_PURE" "premise" (ITER (IF (CMP LT NAT (PROJ (UNCASE (IDX (ITER (VAR "i") LIST (DOM "i" (VAR "i*"))) (VAR "k")) "%") 0) (LEN (ITER (VAR "c'") LIST (DOM "c'" (VAR "c'*")))))) (LISTN (VAR "N") "k")) :RULE "Step_pure/vshuffle" :POS 44 :MODE :FUN)

("STEP_PURE" "premise" (ITER (IF (CMP LT NAT (VAR "k") (LEN (ITER (VAR "i") LIST (DOM "i" (VAR "i*")))))) (LISTN (VAR "N") "k")) :RULE "Step_pure/vshuffle" :POS 44 :MODE :FUN)

("STEP_PURE" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (VAR "Lnn") (CASE "%" (TUP (VAR "N")))))) (EXP (ITER (CALL "packnum_" (EXP (VAR "Lnn")) (EXP (VAR "c_1"))) (LISTN (VAR "N")))))) :RULE "Step_pure/vsplat" :POS 45 :MODE :FUN)

("STEP_PURE" "unbound variable" "Lnn" :RULE "Step_pure/vsplat" :POS 45 :MODE :FUN)

("STEP_PURE" "unbound variable" "c_1" :RULE "Step_pure/vsplat" :POS 45 :MODE :FUN)

("STEP_PURE" "unbound variable" "Lnn" :RULE "Step_pure/vsplat" :POS 45 :MODE :FUN)

("STEP_PURE" "unbound variable" "N" :RULE "Step_pure/vsplat" :POS 45 :MODE :FUN)

("STEP_PURE" "unbound variable" "c" :RULE "Step_pure/vsplat" :POS 45 :MODE :FUN)

("STEP_PURE" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (VAR "Lnn") (CASE "%" (TUP (VAR "N")))))) (EXP (UPD (CALL "lanes_" (EXP (CASE "%X%" (TUP (VAR "Lnn") (CASE "%" (TUP (VAR "N")))))) (EXP (VAR "c_1"))) (IDX ROOT (PROJ (UNCASE (VAR "i") "%") 0)) (CALL "packnum_" (EXP (VAR "Lnn")) (EXP (VAR "c_2"))))))) :RULE "Step_pure/vreplace_lane" :POS 48 :MODE :FUN)

("STEP_PURE" "unbound variable" "c_1" :RULE "Step_pure/vreplace_lane" :POS 48 :MODE :FUN)

("STEP_PURE" "unbound variable" "Lnn" :RULE "Step_pure/vreplace_lane" :POS 48 :MODE :FUN)

("STEP_PURE" "unbound variable" "c_2" :RULE "Step_pure/vreplace_lane" :POS 48 :MODE :FUN)

("STEP_PURE" "unbound variable" "Lnn" :RULE "Step_pure/vreplace_lane" :POS 48 :MODE :FUN)

("STEP_PURE" "unbound variable" "N" :RULE "Step_pure/vreplace_lane" :POS 48 :MODE :FUN)

("STEP_PURE" "unbound variable" "i" :RULE "Step_pure/vreplace_lane" :POS 48 :MODE :FUN)

("STEP_PURE" "unbound variable" "c" :RULE "Step_pure/vreplace_lane" :POS 48 :MODE :FUN)

("STEP_READ" "pattern" (CALL "nbytes_" (EXP (VAR "nt")) (EXP (VAR "c"))) :RULE "Step_read/load-num-val" :POS 23 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/load-num-val" :POS 23 :MODE :FUN)

("STEP_READ" "pattern" (CALL "vbytes_" (EXP (CASE "V128" (TUP))) (EXP (VAR "c"))) :RULE "Step_read/vload-val" :POS 27 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/vload-val" :POS 27 :MODE :FUN)

("STEP_READ" "iterated premise without inputs" (ITER (IF (CMP EQ BOOL (CALL "ibytes_" (EXP (PROJ (UNCASE (VAR "M") "%") 0)) (EXP (VAR "j"))) (SLICE (DOT (CALL "mem" (EXP (VAR "z")) (EXP (CASE "%" (TUP (NUM (NAT 0)))))) "BYTES") (BIN ADD NAT (BIN ADD NAT (PROJ (UNCASE (VAR "i") "%") 0) (PROJ (UNCASE (DOT (VAR "ao") "OFFSET") "%") 0)) (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (BIN MUL NAT (VAR "k") (PROJ (UNCASE (VAR "M") "%") 0))) (CVT NAT RAT (NUM (NAT 8)))))) (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (PROJ (UNCASE (VAR "M") "%") 0)) (CVT NAT RAT (NUM (NAT 8)))))))) (LISTN (VAR "N") "k") (DOM "j" (VAR "j*"))) :RULE "Step_read/vload-shape-val" :POS 29 :MODE :FUN)

("STEP_READ" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step_read/vload-shape-val" :POS 29 :MODE :FUN)

("STEP_READ" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (CASE "%" (TUP (VAR "N")))))) (EXP (ITER (CALL "extend__" (EXP (PROJ (UNCASE (VAR "M") "%") 0)) (EXP (CALL "jsize" (EXP (VAR "Jnn")))) (EXP (VAR "sx")) (EXP (VAR "j"))) (LISTN (VAR "N")) (DOM "j" (VAR "j*")))))) :RULE "Step_read/vload-shape-val" :POS 29 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/vload-shape-val" :POS 29 :MODE :FUN)

("STEP_READ" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step_read/vload-splat-val" :POS 31 :MODE :FUN)

("STEP_READ" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (ITER (CASE "%" (TUP (PROJ (UNCASE (VAR "j") "%") 0))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0)))))) :RULE "Step_read/vload-splat-val" :POS 31 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/vload-splat-val" :POS 31 :MODE :FUN)

("STEP_READ" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step_read/vload_lane-val" :POS 35 :MODE :FUN)

("STEP_READ" "condition with unbound variables" (CMP EQ BOOL (VAR "c") (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (UPD (CALL "lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (VAR "c_1"))) (IDX ROOT (PROJ (UNCASE (VAR "j") "%") 0)) (CASE "%" (TUP (PROJ (UNCASE (VAR "k") "%") 0))))))) :RULE "Step_read/vload_lane-val" :POS 35 :MODE :FUN)

("STEP_READ" "unbound variable" "c" :RULE "Step_read/vload_lane-val" :POS 35 :MODE :FUN)

("STEP_READ" "iterated premise without inputs" (ITER (IF (CMP EQ BOOL (CALL "ibytes_" (EXP (PROJ (UNCASE (VAR "M") "%") 0)) (EXP (VAR "j"))) (SLICE (DOT (CALL "mem" (EXP (VAR "z")) (EXP (CASE "%" (TUP (NUM (NAT 0)))))) "BYTES") (BIN ADD NAT (BIN ADD NAT (PROJ (UNCASE (VAR "i") "%") 0) (PROJ (UNCASE (DOT (VAR "ao") "OFFSET") "%") 0)) (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (BIN MUL NAT (VAR "k") (PROJ (UNCASE (VAR "M") "%") 0))) (CVT NAT RAT (NUM (NAT 8)))))) (CVT RAT NAT (BIN DIV RAT (CVT NAT RAT (PROJ (UNCASE (VAR "M") "%") 0)) (CVT NAT RAT (NUM (NAT 8)))))))) (LISTN (VAR "N") "k") (DOM "j" (VAR "j*"))) :RULE "Step_read/vload-shape-val" :POS 29 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step_read/vload-shape-val" :POS 29 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (CASE "%" (TUP (VAR "N")))))) (EXP (ITER (CALL "extend__" (EXP (PROJ (UNCASE (VAR "M") "%") 0)) (EXP (CALL "jsize" (EXP (VAR "Jnn")))) (EXP (VAR "sx")) (EXP (VAR "j"))) (LISTN (VAR "N")) (DOM "j" (VAR "j*"))))) :RULE "Step_read/vload-shape-val" :POS 29 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step_read/vload-splat-val" :POS 31 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (ITER (CASE "%" (TUP (PROJ (UNCASE (VAR "j") "%") 0))) (LISTN (PROJ (UNCASE (VAR "M") "%") 0))))) :RULE "Step_read/vload-splat-val" :POS 31 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step_read/vload_lane-val" :POS 35 :MODE :CHECK)

("STEP_READ" "pattern" (CALL "inv_lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (UPD (CALL "lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (VAR "c_1"))) (IDX ROOT (PROJ (UNCASE (VAR "j") "%") 0)) (CASE "%" (TUP (PROJ (UNCASE (VAR "k") "%") 0)))))) :RULE "Step_read/vload_lane-val" :POS 35 :MODE :CHECK)

("STEP" "pattern" (CALL "jsize" (EXP (VAR "Jnn"))) :RULE "Step/vstore_lane-val" :POS 19 :MODE :FUN)

("STEP" "condition with unbound variables" (CMP LT NAT (PROJ (UNCASE (VAR "j") "%") 0) (LEN (CALL "lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (VAR "c"))))) :RULE "Step/vstore_lane-val" :POS 19 :MODE :FUN)

("STEP" "condition with unbound variables" (CMP EQ BOOL (ITER (VAR "b") LIST (DOM "b" (VAR "b*"))) (CALL "ibytes_" (EXP (VAR "N")) (EXP (CASE "%" (TUP (PROJ (UNCASE (IDX (CALL "lanes_" (EXP (CASE "%X%" (TUP (SUB (VAR "Jnn") (VAR "lanetype") (VAR "Jnn")) (VAR "M")))) (EXP (VAR "c"))) (PROJ (UNCASE (VAR "j") "%") 0)) "%") 0)))))) :RULE "Step/vstore_lane-val" :POS 19 :MODE :FUN)

("STEP" "unbound variable" "b*" :RULE "Step/vstore_lane-val" :POS 19 :MODE :FUN)

("GRAM/BINSTR" "condition with unbound variables" (CMP EQ BOOL (CALL "ibytes_" (EXP (NUM (NAT 128))) (EXP (CASE "%" (TUP (PROJ (UNCASE (VAR "b'") "%") 0))))) (LIST (VAR "b"))))

("GRAM/BINSTR" "unbound variable" "b'")

("GRAM/BINSTR" "unbound variable" "l")

