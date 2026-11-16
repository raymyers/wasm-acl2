; E2 probe: admit, in a session on top of the certified 3.0 books, every
; :program function below STEPS, with the measures the translator would emit.
; Run from translate/tests/sem-3.0/:  acl2 < <this file>
; Applies to the books generated at 78d1584 (before the E2 translator change):
; there these functions are in program mode and verify-termination can be tried.
; Result at 78d1584: the $SUBST clique admits in 0.08 s (43,109 prover steps),
; the fuel clique in 0.38 s (114,347 steps). REF_OK is probed in probe-refok.lsp.
(ld "cert.acl2")
(in-package "ACL2")
(include-book "../../gen/wasm-3.0/wasm3")
(defun vt-args (xs)
  (if (atom xs) nil
    (cons (list (car (car xs))
                (list 'declare
                      (list 'xargs :ruler-extenders :all
                            :measure (cadr (car xs)))))
          (vt-args (cdr xs)))))
(defmacro vt (&rest xs) (cons 'verify-termination (vt-args xs)))
(defun vts (xs)
  (if (atom xs) nil
    (cons `(verify-termination ,(car xs) (declare (xargs :ruler-extenders :all)))
          (vts (cdr xs)))))
(defmacro vt* (&rest xs) (cons 'progn (vts xs)))
(set-current-package "W3T" state)
(acl2::defmacro s (v r) `(%om (acl2::acl2-count ,v) ,r))
(acl2::defmacro f0 () `(%om3 (acl2::nfix %fuel) 0 0))
(acl2::defmacro fl (r v) `(%om3 (acl2::nfix %fuel) ,r (acl2::acl2-count ,v)))
(acl2::defmacro fk (r) `(%om3 (acl2::nfix %fuel) ,r (acl2::nfix (acl2::- (acl2::1+ %hi) %k))))
(acl2::with-prover-step-limit 2000000
(acl2::vt
 ($subst_typeuse (s %a0 1))
 ($subst_heaptype (s %a0 1))
 ($subst_reftype (s %a0 0))
 ($subst_valtype (s %a0 1))
 ($subst_storagetype (s %a0 2))
 ($subst_fieldtype (s %a0 0))
 ($subst_comptype/iter1 (s %l0 0))
 ($subst_comptype/iter4 (s %l0 0))
 ($subst_comptype/iter5 (s %l0 0))
 ($subst_comptype (s %a0 0))
 ($subst_subtype/iter2 (s %l0 0))
 ($subst_subtype (s %a0 0))
 ($subst_rectype/iter4 (s %l0 0))
 ($subst_rectype (s %a0 0))
 ($subst_deftype (s %a0 0))))
(acl2::vt* $subst_all_reftype $subst_all_deftype $unrollrt/iter1 $unrollrt $unrolldt expand
           $clos_deftypes $clos_deftype $unrollht_ subtype_ok2/map4)
(acl2::with-prover-step-limit 2000000
(acl2::vt
 (HEAPTYPE_OK/%F (f0)) (REFTYPE_OK/%F (f0)) (VALTYPE_OK/%F (f0)) (TYPEUSE_OK/%F (f0))
 (RESULTTYPE_OK/ALL0 (fl 1 %l0)) (RESULTTYPE_OK/%F (f0)) (FIELDTYPE_OK/%F (f0)) (STORAGETYPE_OK/%F (f0))
 (COMPTYPE_OK/ALL1 (fl 1 %l0)) (COMPTYPE_OK/%F (f0)) (SUBTYPE_OK2/ALL6 (fl 1 %l0)) (SUBTYPE_OK2/ALL7 (fl 1 %l0))
 (SUBTYPE_OK2/%F (f0)) (RECTYPE_OK2/%F (f0)) (DEFTYPE_OK/%F (f0))
 (COMPTYPE_SUB/ALL5 (fl 1 %l0)) (COMPTYPE_SUB/SEARCH6 (fk 2)) (COMPTYPE_SUB/%F (f0))
 (DEFTYPE_SUB/SOME3 (%om3 (acl2::nfix %fuel) 1 (acl2::nfix (acl2::- (acl2::nfix %n) (acl2::nfix i)))))
 (DEFTYPE_SUB/%F (f0)) (HEAPTYPE_SUB/SEARCH3 (fk 1)) (HEAPTYPE_SUB/%F (f0)) (REFTYPE_SUB/%F (f0))
 (VALTYPE_SUB/%F (f0)) (RESULTTYPE_SUB/ALL0 (fl 1 %l0)) (RESULTTYPE_SUB/%F (f0)) (STORAGETYPE_SUB/%F (f0))
 (FIELDTYPE_SUB/%F (f0)) (HEAPTYPE_SUB/ENUM2 (f0)) (DEFTYPE_SUB/ENUM2/SEARCH7 (fk 1)) (DEFTYPE_SUB/ENUM2 (f0))
 (HEAPTYPE_OK (%om3 (acl2::1+ (%tfuel)) 0 0)) (REFTYPE_OK (%om3 (acl2::1+ (%tfuel)) 0 0)) (VALTYPE_OK (%om3 (acl2::1+ (%tfuel)) 0 0)) (TYPEUSE_OK (%om3 (acl2::1+ (%tfuel)) 0 0)) (RESULTTYPE_OK (%om3 (acl2::1+ (%tfuel)) 0 0)) (FIELDTYPE_OK (%om3 (acl2::1+ (%tfuel)) 0 0))
 (STORAGETYPE_OK (%om3 (acl2::1+ (%tfuel)) 0 0)) (COMPTYPE_OK (%om3 (acl2::1+ (%tfuel)) 0 0)) (SUBTYPE_OK2 (%om3 (acl2::1+ (%tfuel)) 0 0)) (RECTYPE_OK2 (%om3 (acl2::1+ (%tfuel)) 0 0)) (DEFTYPE_OK (%om3 (acl2::1+ (%tfuel)) 0 0)) (COMPTYPE_SUB (%om3 (acl2::1+ (%tfuel)) 0 0))
 (DEFTYPE_SUB (%om3 (acl2::1+ (%tfuel)) 0 0)) (HEAPTYPE_SUB (%om3 (acl2::1+ (%tfuel)) 0 0)) (REFTYPE_SUB (%om3 (acl2::1+ (%tfuel)) 0 0)) (VALTYPE_SUB (%om3 (acl2::1+ (%tfuel)) 0 0)) (RESULTTYPE_SUB (%om3 (acl2::1+ (%tfuel)) 0 0))
 (STORAGETYPE_SUB (%om3 (acl2::1+ (%tfuel)) 0 0)) (FIELDTYPE_SUB (%om3 (acl2::1+ (%tfuel)) 0 0))))
