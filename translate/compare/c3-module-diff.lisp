; T9 differential test, module level: run the hand-written/agentic WASM1
; semantics (../../execution.lisp) on the same V8 invoke vectors that the
; translated W1T semantics passes 515/515 (tests/sem/t5-invoke.lisp), and
; report agreement per export. This book is a REPORT: it certifies whatever
; the numbers are, and prints them (see the .cert.out).
;
; WASM1 has no module loader (its tests build states by hand), so this book
; is the bridge: each corpus .wasm is decoded with W1T's generated
; GRAM/BMODULE, and the decoded module is converted to a WASM1 acl2::state (store of
; funcinsts, memory bytes with data segments applied, table with elem segments
; applied) with WASM1's instruction syntax ((:BINOP (:I32) (:ADD)) ->
; (:I32.ADD), blocks get their result arity, loads/stores their offset).
; WASM1 cannot express NaN, +-Inf or -0 float CONSTANTS in code (f32.const
; takes a rational; the specials exist only as stack values), so functions
; containing one are reported as unrepresentable rather than run.
(in-package "WASM")
(include-book "c1-numerics-diff")   ; WASM1 + W1T, w1-val, trap-p, nan-val-p, get-result-1

(program)
(set-state-ok t)

(defun read-bytes-loop (channel acc acl2::state)
  (mv-let (b acl2::state) (read-byte$ channel acl2::state)
    (if (null b) (mv (reverse acc) acl2::state) (read-bytes-loop channel (cons b acc) acl2::state))))

(defun read-bytes (file acl2::state)
  (mv-let (channel acl2::state) (open-input-channel file :byte acl2::state)
    (if (null channel) (mv nil acl2::state)
      (mv-let (bs acl2::state) (read-bytes-loop channel nil acl2::state)
        (let ((acl2::state (close-input-channel channel acl2::state))) (mv bs acl2::state))))))

; --- W1T instruction syntax -> WASM1 instruction syntax ------------------

(defun nstr (n) (coerce (explode-atom n 10) (quote string)))
(defun down (k) (string-downcase (symbol-name k)))
(defun kw (s) (intern$ (string-upcase s) "KEYWORD"))
(defun tname (vt) (down (car vt)))                      ; (:I32) -> "i32"
(defun opname (op)                                      ; (:DIV (:U)) -> "div_u"
  (if (consp (cdr op)) (concatenate 'string (down (car op)) "_" (down (car (cadr op)))) (down (car op))))
(defun nbits (vt) (if (member-eq (car vt) '(:i64 :f64)) 64 32))
(defun offset-of (memarg) (or (cdr (assoc-eq :offset (cdr memarg))) 0))

(defun w1-const (vt x)
  ;; W1T constant -> WASM1 instruction, or :unrepresentable
  (let ((n (nbits vt)))
    (case (car vt)
      (:i32 (list :i32.const x))
      (:i64 (list :i64.const x))
      (t (cond ((or (w1t::%nan-p x) (w1t::%inf-p x)
                    (and (w1t::%zero-p n x) (w1t::%neg-p x)))
                :unrepresentable)
               ((w1t::%zero-p n x) (list (kw (concatenate 'string (tname vt) ".const")) 0))
               (t (list (kw (concatenate 'string (tname vt) ".const")) (w1t::%val n x))))))))

(defun cvt-name (to from op)
  ;; (:CVTOP (:I32) (:F64) (:TRUNC (:U))) -> "i32.trunc_f64_u"
  (concatenate 'string (tname to) "." (down (car op)) "_" (tname from)
               (if (consp (cdr op)) (concatenate 'string "_" (down (car (cadr op)))) "")))

(mutual-recursion
 (defun conv-instrs (is)
   ;; list of WASM1 instrs, or :unrepresentable / (:unsupported instr)
   (if (atom is) nil
     (let ((a (conv-instr (car is))) (r (conv-instrs (cdr is))))
       (cond ((not (and (consp a) (keywordp (car a)) (not (eq (car a) :unsupported)))) a)
             ((not (true-listp r)) r)
             ((and (consp r) (eq (car r) :unsupported)) r)
             (t (cons a r))))))
 (defun conv-body (op bt body)
   (let ((b (conv-instrs body)))
     (if (or (eq b :unrepresentable) (and (consp b) (eq (car b) :unsupported))) b
       (list op (len bt) b))))
 (defun conv-instr (i)
   (case (car i)
     ((:nop :unreachable :drop :return) (list (car i)))
     ((:local.get :local.set :local.tee :global.get :global.set :br :br_if :call)
      (list (car i) (cadr i)))
     (:call_indirect (list :call_indirect (cadr i)))
     (:br_table (list :br_table (cadr i) (caddr i)))
     (:const (w1-const (cadr i) (caddr i)))
     ((:binop :unop :testop :relop)
      (list (kw (concatenate 'string (tname (cadr i)) "." (opname (caddr i))))))
     (:cvtop (list (kw (cvt-name (cadr i) (caddr i) (cadddr i)))))
     (:load (let ((pk (car (caddr i))))           ; nil or (:_ n (:sx))
              (list (kw (if pk (concatenate 'string (tname (cadr i)) ".load" (nstr (cadr pk))
                                            "_" (down (car (caddr pk))))
                          (concatenate 'string (tname (cadr i)) ".load")))
                    (offset-of (cadddr i)))))
     (:store (let ((pk (car (caddr i))))          ; nil or n
               (list (kw (if pk (concatenate 'string (tname (cadr i)) ".store" (nstr pk))
                           (concatenate 'string (tname (cadr i)) ".store")))
                     (offset-of (cadddr i)))))
     (:block (let ((b (conv-body :block (cadr i) (caddr i)))) b))
     (:loop (let ((b (conv-body :loop (cadr i) (caddr i)))) b))
     (:ifelse (let ((th (conv-instrs (caddr i))) (el (conv-instrs (cadddr i))))
                (cond ((not (true-listp th)) th) ((and (consp th) (eq (car th) :unsupported)) th)
                      ((not (true-listp el)) el) ((and (consp el) (eq (car el) :unsupported)) el)
                      (t (list :if (len (cadr i)) th el)))))
     (t (list :unsupported i)))))

; --- W1T module -> WASM1 acl2::state pieces --------------------------------------
; (:MODULE type* import* func* global* table* mem* elem* data* start? export*)

(defun functype-of (m f) (cadr (nth (cadr f) (nth 1 m))))   ; (:%->% params results)

(defun write-bytes (mem off bs)
  (if (atom bs) mem (write-bytes (update-nth off (car bs) mem) (1+ off) (cdr bs))))
(defun apply-datas (mem ds)       ; (:DATA ((:CONST (:I32) off)) bytes)
  (if (atom ds) mem (apply-datas (write-bytes mem (caddr (car (cadr (car ds)))) (caddr (car ds))) (cdr ds))))
(defun apply-elems (tbl es)       ; (:ELEM ((:CONST (:I32) off)) funcidx*)
  (if (atom es) tbl (apply-elems (write-bytes tbl (caddr (car (cadr (car es)))) (caddr (car es))) (cdr es))))

(defun module-memory (m)
  (let ((mems (nth 6 m)))
    (if (atom mems) nil
      (apply-datas (make-list (* 65536 (cadr (cadr (car mems)))) :initial-element 0) (nth 8 m)))))
(defun module-table (m)
  (let ((ts (nth 5 m)))
    (if (atom ts) nil (apply-elems (make-list (cadr (cadr (car ts))) :initial-element nil) (nth 7 m)))))

; --- Running a vector -------------------------------------------------------

(defun chars (s) (if (atom s) nil (cons (char-code (car s)) (chars (cdr s)))))
(defun find-export (name exs)
  (cond ((atom exs) nil)
        ((equal (cadr (car exs)) (chars (coerce name 'list))) (caddr (car exs)))
        (t (find-export name (cdr exs)))))

(defun tystr (k) (string-downcase (symbol-name k)))
(defun w1-arg (ty bits)
  ;; float +0 as the rational 0, the value WASM1 constants produce (w1-val gives :F32.+0)
  (if (and (member-equal ty (quote ("f32" "f64"))) (equal bits 0))
      (if (equal ty "f32") (make-f32-val 0) (make-f64-val 0))
    (w1-val ty bits)))
(defun w1-args (tys bits) (if (atom tys) nil (cons (w1-arg (tystr (car tys)) (car bits)) (w1-args (cdr tys) (cdr bits)))))

(defun w1-invoke (m store x args)
  ;; run export function x on WASM1; result value, :trap, or :fuel
  (let* ((ft (functype-of m (nth x (nth 3 m))))
         (r (run 2000000
                 (make-state :store store
                             :call-stack (list (make-frame :return-arity (len (caddr ft)) :locals nil
                                                           :operand-stack (reverse args)
                                                           :instrs (list (list :call x)) :label-stack nil))
                             :memory (module-memory m) :globals nil :table (module-table m)))))
    (cond ((trap-p r) :trap)
          ((and (consp r) (eq (car r) :done)) (get-result-1 r))
          (t :fuel))))

(defun agree-module-p (want got rty)
  (cond ((eq want :trap) (eq got :trap))
        ((eq want :nan) (nan-val-p got))
        ((null want) (not (member-eq got '(:trap :fuel))))
        ((and (member-equal rty '("f32" "f64")) (equal want '(0)))
         ;; +0: WASM1 yields either the :F32.+0 special or the rational 0
         (or (equal got (w1-val rty 0)) (equal got (if (equal rty "f32") (make-f32-val 0) (make-f64-val 0)))))
        (t (equal got (w1-val rty (car want))))))

(defun run-vector (v mods)
  ;; v = (file export types args want) -> :ok, :unrepresentable, (:unsupported ...), or (:bad got)
  (let* ((e (cdr (assoc-equal (first v) mods))) (m (car e)) (store (cdr e))
         (addr (and m (find-export (second v) (nth 10 m)))))
    (cond ((null m) (list :bad :no-module))
          ((not (and (consp addr) (eq (car addr) :func))) (list :bad :no-export))
          ((not (true-listp store)) store)
          ((and (consp store) (eq (car store) :unsupported)) store)
          (t (let* ((x (cadr addr)) (ft (functype-of m (nth x (nth 3 m))))
                    (rty (and (consp (caddr ft)) (tname (car (caddr ft)))))
                    (body (conv-instrs (cadddr (nth x (nth 3 m))))))
               (if (eq body :unrepresentable) :unrepresentable
                 (let ((got (w1-invoke m store x (w1-args (third v) (fourth v)))))
                   (if (agree-module-p (fifth v) got rty) :ok (list :bad got)))))))))

; store conversion per module: functions with unrepresentable constants become
; trivial bodies, so the rest of the module still runs (they are never called
; by another corpus function; run-vector reports them as unrepresentable)
(defun conv-funcs-lenient (m fs)
  (if (atom fs) nil
    (let* ((f (car fs)) (ft (functype-of m f)) (body (conv-instrs (cadddr f))))
      (cons (make-funcinst :param-count (len (cadr ft)) :local-count (len (caddr f))
                           :return-arity (len (caddr ft))
                           :body (if (eq body :unrepresentable) (list (list :unreachable)) body))
            (conv-funcs-lenient m (cdr fs))))))

(defun load-modules (files acc acl2::state)
  (if (endp files) (mv acc acl2::state)
    (mv-let (bs acl2::state) (read-bytes (concatenate 'string "../tests/sem/wasm/" (car files)) acl2::state)
      (let* ((p (w1t::gram/bmodule bs)) (m (and p (car p))))
        (load-modules (cdr files) (acons (car files) (cons m (and m (conv-funcs-lenient m (nth 3 m)))) acc)
                      acl2::state)))))

; tally per (file . export): (ok unrep bad total)
(defun mtally (vs mods acc bad)
  (if (endp vs) (mv acc bad)
    (let* ((v (car vs)) (key (cons (first v) (second v))) (r (run-vector v mods))
           (old (or (cdr (assoc-equal key acc)) (list 0 0 0 0)))
           (new (list (+ (first old) (if (eq r :ok) 1 0))
                      (+ (second old) (if (eq r :unrepresentable) 1 0))
                      (+ (third old) (if (member-eq r '(:ok :unrepresentable)) 0 1))
                      (1+ (fourth old)))))
      (mtally (cdr vs) mods (put-assoc-equal key new acc)
             (if (member-eq r '(:ok :unrepresentable)) bad (cons (list v r) bad))))))

(defun sum-nth (n acc) (if (endp acc) 0 (+ (nth n (cdar acc)) (sum-nth n (cdr acc)))))
(defun unrep-by-file (acc out)
  ;; alist file -> number of unrepresentable vectors
  (if (endp acc) out
    (unrep-by-file (cdr acc)
                   (if (< 0 (second (cdar acc)))
                       (put-assoc-equal (caar (car acc))
                                        (+ (second (cdar acc)) (or (cdr (assoc-equal (caar (car acc)) out)) 0)) out)
                     out))))
(defun with-bad (acc) (cond ((endp acc) nil)
                            ((< 0 (third (cdar acc))) (cons (car acc) (with-bad (cdr acc))))
                            (t (with-bad (cdr acc)))))

(make-event
 (mv-let (channel acl2::state) (open-input-channel "../tests/sem/invoke-vectors.lsp" :object acl2::state)
   (mv-let (eofp vs acl2::state) (read-object channel acl2::state)
     (declare (ignore eofp))
     (let ((acl2::state (close-input-channel channel acl2::state)))
       (mv-let (mods acl2::state) (load-modules (remove-duplicates-equal (strip-cars vs)) nil acl2::state)
         (mv-let (acc bad) (mtally vs mods nil nil)
           (let ((acc (reverse acc)))
             (prog2$
              (cw "~%T9 module differential (WASM1 vs V8 on the T5 invoke vectors; W1T passes all ~x0):~%  WASM1 agrees on ~x1, disagrees on ~x2; ~x3 not representable in WASM1 syntax (NaN/Inf/-0 constants), by file: ~x6.~%  Exports with disagreements, as ((file . export) ok unrepresentable bad total):~%~x4~%  First disagreements (vector, WASM1 result):~%~x5~%"
                  (len vs) (sum-nth 0 acc) (sum-nth 2 acc) (sum-nth 1 acc)
                  (with-bad acc) (take (min 30 (len bad)) (reverse bad)) (unrep-by-file acc nil))
              (mv nil (list 'value-triple
                            (list 'quote (list :wasm1-ok (sum-nth 0 acc) :bad (sum-nth 2 acc)
                                               :unrepresentable (sum-nth 1 acc) :total (len vs))))
                  acl2::state)))))))))
