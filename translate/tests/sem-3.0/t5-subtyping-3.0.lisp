; 3.0 subtyping and type validity, behavioural cases (wasm3 M5): the
; generated relations of the 19-relation type group, called directly (as
; 1.0 tests/sem/t6-typing). The expected answer of each case is read from
; the rules of 2.2-validation.subtyping.spectec (pinned rev), as the comment
; says. The book prints N of M and the failing cases; it does not fail on
; a wrong answer (the cases that need Heaptype_sub/trans are recorded before
; trans is translated, plan M5).
(in-package "W3T")
(include-book "../../gen/wasm-3.0/wasm3")

(program)
(set-state-ok t)

; types: A = struct {}, B = struct {} with declared supertype A,
; F1 = func [(ref null i31)] -> [], F2 = func [(ref i31)] -> []
(defconst *a* '(:_def (:rec ((:sub nil nil (:struct nil)))) 0))
(defconst *b* (list :_def (list :rec (list (list :sub nil (list *a*) '(:struct nil)))) 0))
(defun ctx (types recs)
  (list :%rec (cons :types types) '(:tags) '(:globals) '(:mems) '(:tables) '(:funcs) '(:datas)
        '(:elems) '(:locals) '(:labels) '(:return) '(:refs) (cons :recs recs)))
(defconst *c* (ctx (list *a* *b*) nil))
; a context inside a rec group: REC 0 is struct {} with declared supertype
; (type 1) = B, whose supertype is A
(defconst *cr* (ctx (list *a* *b*) (list '(:sub nil ((:_idx 1)) (:struct nil)))))
(defconst *ri31* '(:ref nil (:i31)))
(defconst *rni31* '(:ref ((:null)) (:i31)))

(defun cases ()
  `(;; abstract hierarchies
    ("I31 <: EQ (i31-eq)" ,(heaptype_sub *c* '(:i31) '(:eq)) t)
    ("I31 <: ANY (i31-eq, eq-any: trans)" ,(heaptype_sub *c* '(:i31) '(:any)) t)
    ("STRUCT <: ANY (struct-eq, eq-any: trans)" ,(heaptype_sub *c* '(:struct) '(:any)) t)
    ("ARRAY <: ANY (trans)" ,(heaptype_sub *c* '(:array) '(:any)) t)
    ("EQ <: ANY (eq-any)" ,(heaptype_sub *c* '(:eq) '(:any)) t)
    ("deftype A <: STRUCT (struct)" ,(heaptype_sub *c* *a* '(:struct)) t)
    ("deftype A <: EQ (struct, struct-eq: trans)" ,(heaptype_sub *c* *a* '(:eq)) t)
    ("deftype A <: ANY (trans, 3 steps)" ,(heaptype_sub *c* *a* '(:any)) t)
    ("NONE <: I31 (none: I31 <: ANY)" ,(heaptype_sub *c* '(:none) '(:i31)) t)
    ("NONE <: STRUCT (none: STRUCT <: ANY)" ,(heaptype_sub *c* '(:none) '(:struct)) t)
    ("NOFUNC <: FUNC (nofunc)" ,(heaptype_sub *c* '(:nofunc) '(:func)) t)
    ("NOEXTERN <: EXTERN (noextern)" ,(heaptype_sub *c* '(:noextern) '(:extern)) t)
    ("BOT <: I31 (bot)" ,(heaptype_sub *c* '(:bot) '(:i31)) t)
    ;; one negative case per hierarchy, and across
    ("I31 <: FUNC: no" ,(heaptype_sub *c* '(:i31) '(:func)) nil)
    ("FUNC <: ANY: no (separate hierarchy)" ,(heaptype_sub *c* '(:func) '(:any)) nil)
    ("EXTERN <: ANY: no" ,(heaptype_sub *c* '(:extern) '(:any)) nil)
    ("EXN <: ANY: no" ,(heaptype_sub *c* '(:exn) '(:any)) nil)
    ("ANY <: EQ: no" ,(heaptype_sub *c* '(:any) '(:eq)) nil)
    ("NOFUNC <: I31: no" ,(heaptype_sub *c* '(:nofunc) '(:i31)) nil)
    ("NONE <: FUNC: no" ,(heaptype_sub *c* '(:none) '(:func)) nil)
    ("deftype A <: FUNC: no" ,(heaptype_sub *c* *a* '(:func)) nil)
    ;; defined types and indices on each side
    ("B <: A (declared supertype)" ,(heaptype_sub *c* *b* *a*) t)
    ("A <: B: no" ,(heaptype_sub *c* *a* *b*) nil)
    ("(type 0) <: STRUCT (typeidx-l)" ,(heaptype_sub *c* '(:_idx 0) '(:struct)) t)
    ("A <: (type 0) (typeidx-r)" ,(heaptype_sub *c* *a* '(:_idx 0)) t)
    ("(type 1) <: (type 0) (both sides)" ,(heaptype_sub *c* '(:_idx 1) '(:_idx 0)) t)
    ("(type 0) <: (type 1): no" ,(heaptype_sub *c* '(:_idx 0) '(:_idx 1)) nil)
    ("(type 1) <: EQ (typeidx-l, trans)" ,(heaptype_sub *c* '(:_idx 1) '(:eq)) t)
    ;; inside a rec group
    ("REC 0 <: (type 1) (rec-sub, declared)" ,(heaptype_sub *cr* '(:rec 0) '(:_idx 1)) t)
    ("REC 0 <: STRUCT (rec-sub then typeidx-l: trans; rec-struct needs no declared supertype)" ,(heaptype_sub *cr* '(:rec 0) '(:struct)) t)
    ("REC 0 <: (type 0) (supertype of the declared one: trans)" ,(heaptype_sub *cr* '(:rec 0) '(:_idx 0)) t)
    ("REC 0 <: FUNC: no" ,(heaptype_sub *cr* '(:rec 0) '(:func)) nil)
    ;; reference types
    ("(ref i31) <: (ref null i31)" ,(reftype_sub *c* *ri31* *rni31*) t)
    ("(ref null i31) <: (ref i31): no" ,(reftype_sub *c* *rni31* *ri31*) nil)
    ("(ref i31) <: (ref null any) (trans)" ,(reftype_sub *c* *ri31* '(:ref ((:null)) (:any))) t)
    ;; fields: mutable invariant, immutable covariant
    ("field const (ref i31) <: const (ref null i31)" ,(fieldtype_sub *c* (list nil *ri31*) (list nil *rni31*)) t)
    ("field mut (ref i31) <: mut (ref null i31): no (invariant)" ,(fieldtype_sub *c* (list '((:mut)) *ri31*) (list '((:mut)) *rni31*)) nil)
    ("field mut i32 <: mut i32" ,(fieldtype_sub *c* '(((:mut)) (:i32)) '(((:mut)) (:i32))) t)
    ("field mut i32 <: const i32: no" ,(fieldtype_sub *c* '(((:mut)) (:i32)) '(nil (:i32))) nil)
    ;; function types: contravariant parameters, covariant results
    ("func [(ref null i31)]->[] <: func [(ref i31)]->[]" ,(comptype_sub *c* (list :func%->% (list *rni31*) nil) (list :func%->% (list *ri31*) nil)) t)
    ("func [(ref i31)]->[] <: func [(ref null i31)]->[]: no" ,(comptype_sub *c* (list :func%->% (list *ri31*) nil) (list :func%->% (list *rni31*) nil)) nil)
    ("func []->[(ref i31)] <: func []->[(ref null i31)]" ,(comptype_sub *c* (list :func%->% nil (list *ri31*)) (list :func%->% nil (list *rni31*))) t)
    ;; validity
    ("valtype_ok (ref null i31)" ,(valtype_ok *c* *rni31*) t)
    ("valtype_ok (ref (type 1))" ,(valtype_ok *c* '(:ref nil (:_idx 1))) t)
    ("valtype_ok (ref (type 2)): no (no such type)" ,(valtype_ok *c* '(:ref nil (:_idx 2))) nil)
    ("deftype_ok B" ,(deftype_ok *c* *b*) t)))

(defun encodings-ok ()
  (and (deftype-p *a*) (deftype-p *b*) (context-p *c*) (context-p *cr*)
       (fieldtype-p (list '((:mut)) *ri31*)) (comptype-p (list :func%->% (list *rni31*) nil))))

(defun failing (cs) (cond ((atom cs) nil) ((equal (cadr (car cs)) (caddr (car cs))) (failing (cdr cs))) (t (cons (car cs) (failing (cdr cs))))))

(make-event
 (let* ((cs (cases)) (bad (failing cs)))
   (prog2$ (cw "~%T5 subtyping (3.0): ~x0 of ~x1 cases right (encodings ~x2).~%Wrong: ~x3~%"
               (- (acl2::len cs) (acl2::len bad)) (acl2::len cs) (encodings-ok) (strip-cars bad))
           (if (encodings-ok) (mv nil '(value-triple :t5-subtyping-3.0) state)
             (mv (msg "a case uses an encoding the generated recognizers reject") nil state)))))
