; E4 item 1: the rule if-true in a clean, hand-written form, proved equal
; to the generated rule function W3T::STEP_PURE/R-IF-TRUE (not to a copy
; of it). Moved from the talk snippet
; talk/figures/snippets/if-true.handwritten-proof.lisp, which proved the
; same against a pasted copy of the generated clause.
(in-package "WE")
(include-book "../../translate/gen/wasm-3.0/wasm3")

(defun if-true-clean (instrs)
  (case-match instrs
    (((:const (:i32) c) (:ifelse bt then else))
     (and (true-listp then)
          (true-listp else)
          (not (equal c 0))
          (list (list (list :block bt then)))))))

(local (defthm len-0 (equal (equal (len x) 0) (not (consp x)))))
(local (defthm len-k
         (implies (and (syntaxp (quotep k)) (acl2-numberp k))
                  (equal (equal (+ k (len x)) k) (not (consp x))))))

(defthm if-true-clean-is-the-rule
  (equal (if-true-clean instrs) (w3t::step_pure/r-if-true instrs))
  :hints (("Goal" :in-theory (enable w3t::step_pure/r-if-true)))
  :rule-classes nil)

; the two cases, run
(assert-event (equal (if-true-clean '((:const (:i32) 7) (:ifelse :bt ((:nop)) ((:unreachable)))))
                     '(((:block :bt ((:nop)))))))
(assert-event (equal (if-true-clean '((:const (:i32) 0) (:ifelse :bt ((:nop)) ((:unreachable)))))
                     nil))
