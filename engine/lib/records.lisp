; License: MIT. See the file LICENSE at the top of the repository.
;
; Records (plan/wasm-engine/plan2.md V0): the specification's %GET-FIELD and
; %PUT-FIELD are ASSOC-EQUAL and PUT-ASSOC-EQUAL on the alist of a record.
; These are the seven lemmas that fast/frame.lisp stated, moved here
; unchanged so that a later book can use them without the frame lemmas.
(in-package "WE")

(defthm assoc-of-put-assoc
  (equal (assoc-equal k (put-assoc-equal k2 v al))
         (if (equal k k2) (cons k v) (assoc-equal k al))))

(defthm put-assoc-of-put-assoc-same
  (equal (put-assoc-equal k v2 (put-assoc-equal k v1 al)) (put-assoc-equal k v2 al)))

(defthm alistp-put-assoc
  (implies (alistp al) (alistp (put-assoc-equal k v al))))

(defthm put-assoc-of-assoc-same
  (implies (and (alistp al) (assoc-equal k al))
           (equal (put-assoc-equal k (cdr (assoc-equal k al)) al) al)))

(defthm assoc-present-when-value-consp
  (implies (consp (cdr (assoc-equal k al))) (assoc-equal k al))
  :rule-classes :forward-chaining)

(defthm put-assoc-commute
  (implies (and (not (equal k1 k2)) (alistp al) (assoc-equal k1 al) (assoc-equal k2 al))
           (equal (put-assoc-equal k1 v1 (put-assoc-equal k2 v2 al))
                  (put-assoc-equal k2 v2 (put-assoc-equal k1 v1 al)))))

(defthm put-assoc-same-value-over-other-key
  (implies (and (alistp al) (assoc-equal k al) (not (equal k k2)))
           (equal (put-assoc-equal k (cdr (assoc-equal k al)) (put-assoc-equal k2 v al))
                  (put-assoc-equal k2 v al))))
