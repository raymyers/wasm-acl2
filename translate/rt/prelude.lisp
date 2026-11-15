; Hand-written runtime support for the generated W1T semantics (plan §3).
; Names start with % so they can never clash with generated names.
;
; Records are encoded (:%REC (:FIELD . value) ...) with fields in declaration
; order (plan §2.2).
(in-package "WRT")

(defun %get-field (r k)
  (declare (xargs :guard t))
  (if (and (consp r) (alistp (cdr r)))
      (cdr (assoc-equal k (cdr r)))
    nil))

(defun %put-field (r k v)
  (declare (xargs :guard t))
  (if (and (consp r) (alistp (cdr r)))
      (cons (car r) (put-assoc-equal k v (cdr r)))
    r))

; SpecTec record/list composition (il/eval.ml CompE): lists append, an
; empty option yields the other side, records compose field by field.
(defun %rec-p (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :%rec) (alistp (cdr x))))

(defun %comp-fields (f1 f2)
  (declare (xargs :guard (and (alistp f1) (alistp f2))))
  (if (endp f1)
      nil
    (cons (cons (caar f1)
                (let ((a (cdar f1)) (b (cdr (assoc-equal (caar f1) f2))))
                  (if (and (true-listp a) (true-listp b)) (append a b) a)))
          (%comp-fields (cdr f1) f2))))

(defun %comp (a b)
  (declare (xargs :guard t))
  (cond ((and (%rec-p a) (%rec-p b)) (cons :%rec (%comp-fields (cdr a) (cdr b))))
        ((and (true-listp a) (true-listp b)) (append a b))
        (t a)))

; Rule tags (plan/wasm3-demo W7): the translator returns the result of each
; IL rule of a relation as (%RULE "Rel/rule-id" result), and of each grammar
; production as (%RULE "Gram/#k" result). Here the tag is only a name: the
; macro expands to RESULT, so the terms ACL2 admits, proves and runs are the
; untagged ones. The JSCL build of the demo defines %RULE as a recorder of
; the rules that fire (plan/wasm3-demo/notes/W7-rule-tags.md).
(defmacro %rule (name result)
  (declare (ignore name))
  result)

; (%try-logic EVENT): admit EVENT (a defun or mutual-recursion) in logic mode
; if ACL2 accepts it -- termination via ACL2's default measures, guards not
; verified -- and otherwise in program mode. Deterministic for a given ACL2.
(defun %program-defun (d)
  (declare (xargs :guard t))
  (if (and (true-listp d) (eq (car d) 'defun) (consp (cdr d)) (consp (cddr d)))
      (list* 'defun (cadr d) (caddr d)
             '(declare (xargs :mode :program))
             (cdddr d))
    d))

(defun %program-defuns (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil
    (cons (%program-defun (car ds)) (%program-defuns (cdr ds)))))

(defun %program-version (ev)
  (declare (xargs :guard t))
  (if (and (consp ev) (eq (car ev) 'mutual-recursion))
      (cons 'mutual-recursion (%program-defuns (cdr ev)))
    (%program-defun ev)))

; The logic attempt uses :ruler-extenders :all (generated recursive calls sit
; inside let*/and, which the default rulers do not see through) and is
; bounded by a prover step limit (deterministic, unlike a time limit), so a
; hard termination proof falls back instead of hanging.
(defun %logic-defun (d)
  (declare (xargs :guard t))
  (if (and (true-listp d) (eq (car d) 'defun) (consp (cdr d)) (consp (cddr d)))
      (list* 'defun (cadr d) (caddr d)
             '(declare (xargs :ruler-extenders :all))
             (cdddr d))
    d))

(defun %logic-defuns (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (cons (%logic-defun (car ds)) (%logic-defuns (cdr ds)))))

(defun %logic-version (ev)
  (declare (xargs :guard t))
  (if (and (consp ev) (eq (car ev) 'mutual-recursion))
      (cons 'mutual-recursion (%logic-defuns (cdr ev)))
    (%logic-defun ev)))

; Second logic alternative: prove termination in ACL2's ground-zero theory,
; so the prover does not open (large) generated callees; parser loop
; measures only need the generated progress checks about len.
(defun %gz-defun (d)
  (declare (xargs :guard t))
  (if (and (true-listp d) (eq (car d) 'defun) (consp (cdr d)) (consp (cddr d)))
      (list* 'defun (cadr d) (caddr d)
             '(declare (xargs :ruler-extenders :all
                              :hints (("Goal" :in-theory
                                       (union-theories (theory 'acl2::ground-zero)
                                                       '(%om-o< %om-o-p %om3-o< %om3-o-p (:type-prescription %size)))))))
             (cdddr d))
    d))

(defun %gz-defuns (ds)
  (declare (xargs :guard t))
  (if (atom ds) nil (cons (%gz-defun (car ds)) (%gz-defuns (cdr ds)))))

(defun %gz-version (ev)
  (declare (xargs :guard t))
  (if (and (consp ev) (eq (car ev) 'mutual-recursion))
      (cons 'mutual-recursion (%gz-defuns (cdr ev)))
    (%gz-defun ev)))

; Further alternatives for a single recursive defun: measure (acl2-count f)
; for each formal f in turn (e.g. $allocfuncs recurses on its third argument
; while its first, the store, grows).
(defun %measure-alts (d fs)
  (declare (xargs :guard t))
  (if (or (atom fs) (not (and (true-listp d) (eq (car d) 'defun) (consp (cdr d)) (consp (cddr d)))))
      nil
    (cons (list 'with-prover-step-limit 200000
                (list* 'defun (cadr d) (caddr d)
                       (list 'declare (list 'xargs :ruler-extenders :all
                                            :measure (list 'acl2-count (car fs))))
                       (cdddr d)))
          (%measure-alts d (cdr fs)))))

(defmacro %try-logic (ev)
  `(make-event '(:or (with-prover-step-limit 200000 ,(%logic-version ev))
                     (with-prover-step-limit 2000000 ,(%gz-version ev))
                     ,@(and (consp ev) (eq (car ev) 'defun) (consp (cdr ev)) (consp (cddr ev))
                            (true-listp (caddr ev))
                            (%measure-alts ev (caddr ev)))
                     ,(%program-version ev))))

; Step bound for closure relations (Steps): R(x) iterates the step relation
; at most (%FUEL) times and has no result if the bound is reached.
(defun %fuel () (declare (xargs :guard t)) 1000000)

; Depth bound for the relations of a fuel group (config :fuel; il2acl2
; fuel-wrap): R/%F has no result once %TFUEL nested relation calls are
; open. Far above the depth of a derivation for a real type, and small
; enough that a search which fails through a cyclic (invalid) context ends
; without exhausting the Lisp stack.
(defun %tfuel () (declare (xargs :guard t)) 10000)

; (%try-guards f): verify the guards of F (and its clique) if ACL2 can, within
; a prover step limit; otherwise leave them unverified. Deterministic.
(defmacro %try-guards (name)
  `(make-event '(:or (with-prover-step-limit 100000 (verify-guards ,name))
                     (value-triple :guards-not-verified))))

; Lexicographic measures for recursive relation groups (T8): (%OM m n) is
; the ordinal omega*m + n. A relation R in a rec group has measure
; (%OM (1+ size(inputs)) 0); a split search inside it has
; (%OM size(inputs) counter); every recursive premise call is preceded by a
; generated check size(callee inputs) < size(inputs).
(defun %om (m n)
  (declare (xargs :guard t))
  (if (posp m) (make-ord 1 m (nfix n)) (nfix n)))

(defthm %om-o-p
  (o-p (%om m n)))

(defthm %om-o<
  (implies (and (natp a) (natp b))
           (equal (o< (%om a x) (%om b y))
                  (or (< a b) (and (equal a b) (< (nfix x) (nfix y))))))
  :hints (("Goal" :in-theory (enable o< o-finp o-first-expt o-first-coeff o-rst))))

; Opaque size (= acl2-count): the size check and the measure mention the same
; %SIZE terms, which stay syntactically identical in the measure conjecture.
(defun %size (x) (declare (xargs :guard t)) (acl2-count x))

(in-theory (disable %om %size))

; (%OM3 a b c) = omega^2*a + omega*b + c, for lexicographic size checks
; (size of a designated decreasing component, size of all inputs).
(defun %om3 (a b c)
  (declare (xargs :guard t))
  (if (posp a) (make-ord 2 a (%om b c)) (%om b c)))

(defthm %om3-o-p
  (o-p (%om3 a b c))
  :hints (("Goal" :in-theory (enable %om))))

(defthm %om3-o<
  (implies (and (natp a) (natp b) (natp x) (natp y))
           (equal (o< (%om3 a b c) (%om3 x y z))
                  (or (< a x)
                      (and (equal a x)
                           (or (< b y) (and (equal b y) (< (nfix c) (nfix z))))))))
  :hints (("Goal" :in-theory (enable %om o< o-finp o-first-expt o-first-coeff o-rst))))

(in-theory (disable %om3))
