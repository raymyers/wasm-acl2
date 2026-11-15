; Decode the modules of one converted spec-test script with the generated
; binary parser (wasm3 M2; from the prep experiment of P5). Run from
; translate/ by run-decode.sh, which prepends (assign d3-name "NAME"),
; (assign d3-data "DIR/") and (ld "gen/wasm-<v>/portcullis.acl2") plus
; (include-book "gen/wasm-<v>/wasm<major>"). Prints one line per module:
;   D3 KIND SHOULD-PARSE PARSED FILE
; KIND is the command (:MODULE, :ASSERT_INVALID, ...); SHOULD-PARSE is nil
; only for a binary :ASSERT_MALFORMED; text-format modules are skipped.
(program)
(set-state-ok t)
(defun d3-read-loop (ch acc state)
  (mv-let (b state) (read-byte$ ch state)
    (if (null b) (mv (reverse acc) state) (d3-read-loop ch (cons b acc) state))))
(defun d3-bytes (f state)
  (mv-let (ch state) (open-input-channel f :byte state)
    (if (null ch) (mv :none state)
      (mv-let (bs state) (d3-read-loop ch nil state)
        (let ((state (close-input-channel ch state))) (mv bs state))))))
(defun d3-obj (f state)
  (mv-let (ch state) (open-input-channel f :object state)
    (mv-let (eof obj state) (read-object ch state)
      (declare (ignore eof))
      (let ((state (close-input-channel ch state))) (mv obj state)))))
(defun d3-cmds (cmds dir state)
  (if (atom cmds) state
    (let* ((c (car cmds)) (k (car c))
           (file (and (member-eq k '(:module :assert_invalid :assert_unlinkable :assert_uninstantiable :assert_malformed))
                      (stringp (cadr c)) (cadr c)))
           (text (or (and (eq k :assert_malformed) (eq (cadddr c) :text))
                     (and file (> (length file) 4) (equal (subseq file (- (length file) 4) (length file)) ".wat")))))
      (if (or (null file) text) (d3-cmds (cdr cmds) dir state)
        (mv-let (bs state) (d3-bytes (concatenate 'string dir file) state)
          (let* ((p (and (consp bs) (gram/bmodule bs)))
                 (ok (and p (null (cadr p)) t)))
            (prog2$ (cw "D3 ~x0 ~x1 ~x2 ~s3~%" k (not (eq k :assert_malformed)) ok file)
                    (d3-cmds (cdr cmds) dir state))))))))
(mv-let (cmds state) (d3-obj (concatenate 'string (@ acl2::d3-data) (@ acl2::d3-name) ".lsp") state)
  (let ((state (d3-cmds cmds (@ acl2::d3-data) state))) (mv nil :done state)))
(acl2::good-bye 0)
