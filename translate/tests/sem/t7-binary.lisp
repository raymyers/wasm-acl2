; T7 check: the binary decoder GENERATED from A-binary.spectec (GRAM/BMODULE)
; parses every module of the shared oracle corpus (tests/oracle/*.wat built
; with wat2wasm, see ../oracle/gen-wasm-corpus.mjs), consumes all input, and
; agrees with V8 on the exports (names and kinds).
(in-package "W1T")
(include-book "../../gen/wasm1")

(program)
(set-state-ok t)

(defun read-bytes-loop (channel acc state)
  (mv-let (b state) (read-byte$ channel state)
    (if (null b) (mv (reverse acc) state)
      (read-bytes-loop channel (cons b acc) state))))

(defun read-bytes (file state)
  (mv-let (channel state) (open-input-channel file :byte state)
    (if (null channel) (mv nil state)
      (mv-let (bs state) (read-bytes-loop channel nil state)
        (let ((state (close-input-channel channel state)))
          (mv bs state))))))

(defun kind-tag (k)
  (case k (:function :func) (:memory :mem) (:table :table) (t :global)))

(defun code-chars (cs)
  (if (atom cs) nil (cons (code-char (car cs)) (code-chars (cdr cs)))))

; our exports: (:EXPORT name (:FUNC|:MEM|... idx)), name = list of chars
(defun our-exports (exs)
  (if (atom exs) nil
    (cons (list (coerce (code-chars (second (car exs))) 'string)
                (car (third (car exs))))
          (our-exports (cdr exs)))))

(defun v8-exports (es)
  (if (atom es) nil
    (cons (list (car (car es)) (kind-tag (cadr (car es)))) (v8-exports (cdr es)))))

(defun check-corpus (entries nok bad state)
  (if (endp entries) (mv nok (reverse bad) state)
    (let ((file (car (car entries))) (want (v8-exports (cdr (car entries)))))
      (mv-let (bs state) (read-bytes (concatenate 'string "wasm/" file) state)
        (let* ((r (gram/bmodule bs))
               (ok (and r (null (cadr r)) (eq (car (car r)) :module)
                        (equal (our-exports (nth 10 (car r))) want))))
          (check-corpus (cdr entries) (if ok (1+ nok) nok)
                        (if ok bad (cons (list file :parsed (and r t)
                                               :rest (and r (acl2::len (cadr r)))
                                               :exports (and r (our-exports (nth 10 (car r)))))
                                         bad))
                        state))))))

(make-event
 (mv-let (channel state) (open-input-channel "wasm-corpus.lsp" :object state)
   (mv-let (eofp entries state) (read-object channel state)
     (declare (ignore eofp))
     (let ((state (close-input-channel channel state)))
       (mv-let (nok bad state) (check-corpus entries 0 nil state)
         (prog2$ (cw "~%T7 binary: ~x0 of ~x1 corpus modules parse and match V8's exports.~%"
                     nok (acl2::len entries))
                 (if bad
                     (mv (msg "failures: ~x0" bad) nil state)
                   (mv nil '(value-triple :t7-binary-ok) state))))))))
