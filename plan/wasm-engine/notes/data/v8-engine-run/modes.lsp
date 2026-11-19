; V8 item 6 (plan/wasm-engine/plan2.md): the modes of the spec functions a
; driver calls before and between runs of the engine, and, for one in
; program mode, the program-mode functions it reaches. From engine/:
;   acl2 < ../plan/wasm-engine/notes/data/v8-engine-run/modes.lsp | sed -n "/MODES/,\$p" > .../modes.txt
(ld "cert.acl2")
(include-book "run")
(in-package "WE")
(program)
(defun body-fns (fn wrld)
  (let ((b (acl2::getpropc fn 'acl2::unnormalized-body nil wrld)))
    (if b (acl2::all-fnnames b)
      (let ((ev (acl2::get-event fn wrld)))
        (and (consp ev) (eq (car ev) 'defun)
             (mv-let (erp tb)
               (acl2::translate-cmp (car (last ev)) t nil t 'x wrld (acl2::default-state-vars nil))
               (if erp nil (acl2::all-fnnames tb))))))))
(defun prog-reach (todo seen acc wrld n)
  (cond ((or (zp n) (atom todo)) acc)
        ((member-eq (car todo) seen) (prog-reach (cdr todo) seen acc wrld (1- n)))
        (t (let* ((fn (car todo)) (pr (eq (acl2::symbol-class fn wrld) :program)))
             (prog-reach (append (body-fns fn wrld) (cdr todo)) (cons fn seen)
                         (if pr (cons fn acc) acc) wrld (1- n))))))
(defun modes (fns wrld)
  (if (atom fns) nil
    (cons (list (car fns) (acl2::symbol-class (car fns) wrld)) (modes (cdr fns) wrld))))
(cw "MODES ~x0~%" (modes '(w3t::gram/bmodule w3t::$instantiate w3t::$invoke w3t::steps/%fuel w3t::step
                            engine-run engine-config engine-result-p engine-clocks config-shape-p)
                         (w state)))
(let ((l (prog-reach '(w3t::$instantiate) nil nil (w state) 1000000)))
  (cw "PROGRAM-MODE functions reached from $INSTANTIATE: ~x0~%~x1~%" (len l) l))
(let ((l (prog-reach '(w3t::$invoke) nil nil (w state) 1000000)))
  (cw "PROGRAM-MODE functions reached from $INVOKE: ~x0~%~x1~%" (len l) l))
