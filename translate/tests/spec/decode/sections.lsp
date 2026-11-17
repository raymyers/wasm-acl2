; Debug aid (wasm3 M2): for the module in file (@ acl2::d3-file), decode the
; prefixes header + first k sections with GRAM/BMODULE and print which
; prefixes decode: the first k that does not is the section to look at.
; Each section is also given to the generated section grammar alone.
; From translate/:  { echo '(assign d3-file "F")'; echo '(ld "gen/wasm-3.0/portcullis.acl2")';
;   echo '(in-package "W3T")'; echo '(include-book "gen/wasm-3.0/wasm3")';
;   cat tests/spec/decode/sections.lsp; } | acl2
(program)
(set-state-ok t)
(defun d3-read-loop (ch acc state)
  (mv-let (b state) (read-byte$ ch state)
    (if (null b) (mv (reverse acc) state) (d3-read-loop ch (cons b acc) state))))
(defun d3-bytes (f state)
  (mv-let (ch state) (open-input-channel f :byte state)
    (if (null ch) (mv nil state)
      (mv-let (bs state) (d3-read-loop ch nil state)
        (let ((state (close-input-channel ch state))) (mv bs state))))))
(defun leb (bs acc sh)                     ; (mv value rest)
  (if (atom bs) (mv acc nil)
    (let ((b (car bs)))
      (if (< b 128) (mv (+ acc (* b (expt 2 sh))) (cdr bs))
        (leb (cdr bs) (+ acc (* (- b 128) (expt 2 sh))) (+ sh 7))))))
(defun split-sections (bs acc)             ; list of (id . whole-section-bytes)
  (if (atom bs) (reverse acc)
    (mv-let (n rest) (leb (cdr bs) 0 0)
      (let* ((hdr (- (acl2::len bs) (acl2::len rest)))
             (whole (take (+ hdr n) bs)))
        (split-sections (nthcdr (+ hdr n) bs) (cons (cons (car bs) whole) acc))))))
(defun try-prefixes (hdr secs k acc)
  (if (atom secs) nil
    (let* ((acc (append acc (cdr (car secs))))
           (p (gram/bmodule (append hdr acc))))
      (prog2$ (cw "PREFIX ~x0 section id ~x1 (~x2 bytes): ~s3~%" k (car (car secs)) (acl2::len (cdr (car secs)))
                  (if (and p (null (cadr p))) "decodes" "FAILS"))
              (try-prefixes hdr (cdr secs) (1+ k) acc)))))
(mv-let (bs state) (d3-bytes (@ acl2::d3-file) state)
  (prog2$ (try-prefixes (take 8 bs) (split-sections (nthcdr 8 bs) nil) 1 nil)
          (mv nil :done state)))
