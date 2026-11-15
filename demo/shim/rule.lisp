;;;; demo/shim/rule.lisp: WRT::%RULE, the rule tag of W7. In ACL2 it is a
;;;; macro of rt/prelude.lisp that expands to its result. Here too, until the
;;;; W8 recorder: (%RULE "Rel/rule-id" result) = result.
(in-package "ACL2-SHIM")
(defmacro wrt::%rule (name result) (declare (ignore name)) result)
