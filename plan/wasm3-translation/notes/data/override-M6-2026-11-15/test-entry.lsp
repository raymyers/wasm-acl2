 (:rel-override "Instrs_ok" :mode :check
  :defuns ((defun instrs_ok (c is ty)
             (if (and (consp is) (null (cdr is))) (instr_ok c (car is) ty) nil)))
  :reason "TEST of an override inside a rec group")
)
