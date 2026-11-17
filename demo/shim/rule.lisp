;;;; demo/shim/rule.lisp: WRT::%RULE, the rule tag of W7. In ACL2 it is a
;;;; macro of rt/prelude.lisp that expands to its result. Here it is the W8
;;;; recorder: (%RULE "Rel/rule-id" result) evaluates RESULT, and when the
;;;; recorder is on (*RULE-ON*, bound by the glue's STEP-RULES for one STEP)
;;;; pushes the name onto *RULE-TRACE*. A tag fires when its rule's
;;;; conclusion is built, after its premises; the glue recovers the chain of
;;;; one step from the end of the trace (W7 note, "For W8"). Off, the cost is
;;;; one special-variable test per rule that succeeds (measured in W8).
(in-package "ACL2-SHIM")
(defvar *rule-on* nil)
(defvar *rule-trace* nil)
(defmacro wrt::%rule (name result)
  (let ((r (gensym "R")))
    `(let ((,r ,result))
       (when *rule-on* (setq *rule-trace* (cons ,name *rule-trace*)))
       ,r)))
