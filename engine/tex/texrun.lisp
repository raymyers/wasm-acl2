; Raw Lisp, loaded after the engine books (run.sh). The TeX spike: run
; tex.wasm (web2js TeX, the TikZJax build) on the engine's fast machine and
; write the DVI it produces.
;
; What runs where:
;  - every WebAssembly instruction of tex.wasm: the engine (WE::FAST-RUN,
;    one call for each stretch between two calls of a host function);
;  - the 18 imported functions (files, printing, date): this file, a port of
;    TikZJax's library.js. It is trusted, not proved, and it bypasses the
;    spec's $hostcall hook (it reads and writes the engine's memory array);
;  - decoding and the instantiation configuration: the generated spec.
(in-package "ACL2")

(defparameter *dir* (sb-ext:posix-getenv "TEXHOST"))
(defparameter *dl* (sb-ext:posix-getenv "TEXDL"))
(defvar *input*) (defvar *out*) (defvar *max-steps*) (defvar *path* nil)
(defvar *job* "input.tex")               ; the name TeX knows the input file by: its basename
(defvar *quiet* nil)                     ; TEXQUIET: TeX's own terminal output and a summary, no driver detail
(defvar *wasm-bytes* 0)
(defvar *snap* nil)                      ; TEXSNAP: where to save an image at the snapshot line
(defvar *snap-file* nil)                 ; the open input.tex of a saved snapshot
(defvar *snap-at* 0)                     ; where its snapshot line starts
(defvar *check* t)                       ; check the invariant at the start of every stretch (not with TEXNOCHECK)
(defun configure ()                      ; read again when a saved image starts
  (setq *path* (let ((s (sb-ext:posix-getenv "TEXPATH")) (l nil)) ; colon-separated directories
                 (loop while (and s (plusp (length s)))
                       do (let ((c (position #\: s))) (push (subseq s 0 c) l) (setq s (and c (subseq s (1+ c))))))
                 (nreverse l))
        *snap* (sb-ext:posix-getenv "TEXSNAP")
        *quiet* (sb-ext:posix-getenv "TEXQUIET")
        *check* (not (sb-ext:posix-getenv "TEXNOCHECK"))
        *input* (or (sb-ext:posix-getenv "TEXINPUT") (concatenate 'string *dir* "/input.tex"))
        *out* (or (sb-ext:posix-getenv "TEXOUT") (concatenate 'string *dir* "/out"))
        *max-steps* (let ((s (sb-ext:posix-getenv "TEXMAXSTEPS"))) (if s (parse-integer s) 20000000000))
        *job* nil)
  ; started as "acl2-wasm-tex FILE.tex": typeset FILE.tex, write FILE.dvi here, quiet output
  (let ((arg (second sb-ext:*posix-argv*)) (cwd (sb-ext:posix-getenv "PWD")))
    (when (and arg cwd (not (sb-ext:posix-getenv "TEXINPUT"))
               (> (length arg) 4) (string= ".tex" arg :start2 (- (length arg) 4)))
      (let* ((abs (if (char= (char arg 0) #\/) arg (concatenate 'string cwd "/" arg)))
             (slash (position #\/ abs :from-end t)))
        (setq *input* abs *quiet* t
              *out* (concatenate 'string cwd "/" (subseq abs (1+ slash) (- (length abs) 4)))
              *path* (append *path* (list (subseq abs 0 slash)))))))
  (setq *job* (subseq *input* (1+ (or (position #\/ *input* :from-end t) -1)))))
(configure)
(defparameter *pages* 1100)

(defun file-vector (path)
  (with-open-file (s path :element-type '(unsigned-byte 8))
    (let ((v (make-array (file-length s) :element-type '(unsigned-byte 8))))
      (read-sequence v s) v)))
(defun file-bytes (path) (coerce (file-vector path) 'list))
(defun short (x) (let ((*print-length* 12) (*print-level* 6) (*package* (find-package "WE"))) (prin1-to-string x)))
(defun rset (rec k v)                    ; record REC with field K set to V
  (cons :%rec (mapcar (lambda (p) (if (eq (car p) k) (cons k v) p)) (cdr rec))))
(defun codes-string (codes) (map 'string #'code-char codes))
(defparameter *fm* (cdr (assoc 'we::fm *user-stobj-alist*)))
(defparameter *s0* '(:%rec (:tags) (:globals) (:mems) (:tables) (:funcs) (:datas) (:elems) (:structs) (:arrays) (:exns)))

; ---------------------------------------------------------------------------
; the decoded module, cached as a printed object (decoding takes minutes)

(defun decoded-module (wasm cache)
  (if (probe-file cache)
      (with-open-file (s cache) (let ((*package* (find-package "ACL2"))) (read s)))
    (let* ((t0 (get-internal-real-time)) (p (w3t::gram/bmodule (file-bytes wasm))))
      (format t "DECODE ~a: ~,1f s, rest ~s~%" wasm (/ (- (get-internal-real-time) t0) internal-time-units-per-second 1.0)
              (length (cadr p)))
      (unless (and (car p) (null (cadr p))) (error "decode failed"))
      (with-open-file (o cache :direction :output :if-exists :supersede)
        (let ((*package* (find-package "ACL2")) (*print-pretty* nil) (*print-length* nil) (*print-level* nil)
              (*print-readably* nil) (*print-circle* nil))
          (prin1 (car p) o)))
      (car p))))

; ---------------------------------------------------------------------------
; the host: files (a port of library.js)

(defstruct hf name stdin stdout (position 0) (position2 0) (erstat 0) eoln eof content regular)
(defparameter *files* (make-array 16 :adjustable t :fill-pointer 0))
(defun stdin-text ()                     ; what TeX reads from its terminal: the file name, then \end
  (map '(vector (unsigned-byte 8)) #'char-code (format nil " ~a ~%\\end~%" *job*)))
(defparameter *final-end* nil)
(defparameter *calls* (make-hash-table :test 'equal))
(defparameter *console* (make-string-output-stream))

(declaim (inline mem8))
(defun mem8 (a) (we::fm-memi a *fm*))
(defun mem8-set (a v) (we::update-fm-memi a v *fm*))
(defun mem32 (a) (logior (mem8 a) (ash (mem8 (+ a 1)) 8) (ash (mem8 (+ a 2)) 16) (ash (mem8 (+ a 3)) 24)))
(defun mem32-set (a v) (dotimes (k 4) (mem8-set (+ a k) (ldb (byte 8 (* 8 k)) v))))
(defun mem-string (p n) (let ((s (make-string n))) (dotimes (k n s) (setf (char s k) (code-char (mem8 (+ p k)))))))
(defun s32 (x) (if (>= x #x80000000) (- x #x100000000) x))

(defun host-file-bytes (name)            ; the bytes of a host file, or nil
  (cond ((string= name *job*)
         (concatenate '(vector (unsigned-byte 8)) (vector 10) (file-vector *input*)))
        ((or (find #\/ name) (string= name "")) nil)
        (t (loop for d in (append *path* (list (concatenate 'string *dir* "/fs"))) ; TEXPATH first
                 for p = (concatenate 'string d "/" name)
                 when (probe-file p) return (file-vector p)))))

(defun new-file (f) (vector-push-extend f *files*) (1- (length *files*)))

(defun open-file (name mode)
  (let ((content (host-file-bytes name)))
    (cond ((and (null content) (eq mode :r)
                (not (find-if (lambda (f) (and (string= (hf-name f) name) (eql (hf-erstat f) 0))) *files*)))
           (unless *quiet* (format t "HOST not found: ~a~%" name))
           (new-file (make-hf :name name :erstat 1)))
          (t (unless *quiet* (format t "HOST open ~a ~a (~a bytes)~%" mode name (length content)))
             (new-file (make-hf :name name :regular t
                                :content (if (eq mode :r)
                                             (or content (make-array 0 :element-type '(unsigned-byte 8)))
                                           (make-array 1024 :element-type '(unsigned-byte 8) :adjustable t
                                                            :fill-pointer 0))))))))

(defun trim-right (s ch) (string-right-trim (list ch) s))
(defun strip-delim (s open close)        ; drop a leading OPEN and everything from the next CLOSE
  (if (and (plusp (length s)) (char= (char s 0) open))
      (let* ((r (subseq s 1)) (e (position close r))) (if e (subseq r 0 e) r))
    s))
(defun strip-prefix (s prefix)
  (if (and (>= (length s) (length prefix)) (string= prefix s :end2 (length prefix))) (subseq s (length prefix)) s))

(defun h-reset (length pointer)
  (let* ((f (trim-right (mem-string pointer length) (code-char 0)))
         (f (strip-delim f #\{ #\}))
         (f (strip-delim f #\" #\"))
         (f (trim-right f #\Space))
         (f (strip-prefix f "*"))
         (f (strip-prefix f "TeXfonts:"))
         (f (if (string= f "TeXformats:TEX.POOL") "tex.pool" f)))
    (if (string= f "TTY:")
        (new-file (make-hf :name "stdin" :stdin t :content (stdin-text)))
      (open-file f :r))))

(defun h-rewrite (length pointer)
  (let* ((f (trim-right (mem-string pointer length) #\Space))
         (f (strip-delim f #\" #\")))
    (if (string= f "TTY:")
        (new-file (make-hf :name "stdout" :stdout t))
      (open-file f :w))))

(defun out-bytes (d bytes)               ; BYTES (a sequence of codes) to file D or the console
  (let ((f (if (< (s32 d) 0) nil (aref *files* d))))
    (if (or (null f) (hf-stdout f))
        (map nil (lambda (b) (write-char (code-char b) *console*)) bytes)
      (progn (map nil (lambda (b) (vector-push-extend b (hf-content f))) bytes)
             (incf (hf-position f) (length bytes))))))
(defun out-string (d s) (out-bytes d (map 'list #'char-code s)))

(defun h-inputln (d bypass-eoln bufferp firstp lastp max-buf-stackp buf-size)
  (declare (ignore max-buf-stackp buf-size))
  (let* ((f (aref *files* d)) (first (mem32 firstp)) (last first) (c (hf-content f)))
    ; A line "%%% snapshot" in input.tex, with TEXSNAP set: stop before this
    ; call, so that the saved image repeats it with the input file of its run.
    (when (and *snap* (string= (hf-name f) *job*))
      (let ((at (+ (hf-position2 f) (if (and (/= bypass-eoln 0) (not (hf-eof f)) (hf-eoln f)) 1 0)))
            (mark (map 'vector #'char-code "%%% snapshot")))
        (when (and (<= (+ at (length mark)) (length c)) (equalp (subseq c at (+ at (length mark))) mark))
          (setq *snap-file* f *snap-at* at)
          (throw 'snapshot :snapshot))))
    (mem32-set lastp last)
    (when (and (/= bypass-eoln 0) (not (hf-eof f)) (hf-eoln f)) (incf (hf-position2 f)))
    (let ((end (or (position 10 c :start (min (hf-position2 f) (length c))) (length c))))
      (cond ((>= (hf-position2 f) (length c))
             (when (hf-stdin f) (setq *final-end* t))
             (setf (hf-eof f) t)
             0)
            (t (loop for k from (hf-position2 f) below end for a from (+ bufferp first)
                     do (mem8-set a (aref c k)))
               (setq last (+ first (- end (hf-position2 f))))
               (loop while (eql (mem8 (+ bufferp last -1)) 32) do (decf last))
               (mem32-set lastp last)
               (setf (hf-position2 f) end (hf-eoln f) t)
               1)))))

(defun h-get (d pointer length)
  (let ((f (aref *files* d)))
    (block nil
      (cond ((hf-stdin f)
             (if (>= (hf-position f) (length (hf-content f)))
                 (progn (mem8-set pointer 13) (setf (hf-eof f) t) (setq *final-end* t))
               (mem8-set pointer (aref (hf-content f) (hf-position f)))))
            ((and (hf-regular f) (> d 0))
             (let* ((c (hf-content f)) (n (min length (- (length c) (hf-position f)))))
               (when (<= n 0)
                 (mem8-set pointer 0) (setf (hf-eof f) t (hf-eoln f) t) (return))
               (dotimes (k n) (mem8-set (+ pointer k) (aref c (+ (hf-position f) k))))))
            (t (setf (hf-eof f) t (hf-eoln f) t) (return)))
      (setf (hf-eoln f) (and (member (mem8 pointer) '(10 13)) t))
      (incf (hf-position f) length))))

(defun h-put (d pointer length)
  (out-bytes d (loop for k below length collect (mem8 (+ pointer k)))))

(defun flag (x) (if x 1 0))

; (name nargs function): the function takes the i32 arguments in order and
; returns a list of i32 results
(defparameter *host-table*
  (list (list "printInteger" 2 (lambda (d x) (out-string d (format nil "~d" (s32 x))) nil))
        (list "printChar" 2 (lambda (d x) (out-bytes d (list x)) nil))
        (list "printString" 2 (lambda (d x) (out-bytes d (loop for k from 1 to (mem8 x) collect (mem8 (+ x k)))) nil))
        (list "printNewline" 1 (lambda (d) (out-bytes d (list 10)) nil))
        (list "reset" 2 (lambda (l p) (list (h-reset l p))))
        (list "inputln" 7 (lambda (&rest a) (list (apply #'h-inputln a))))
        (list "rewrite" 2 (lambda (l p) (list (h-rewrite l p))))
        (list "get" 3 (lambda (d p l) (h-get d p l) nil))
        (list "put" 3 (lambda (d p l) (h-put d p l) nil))
        (list "eof" 1 (lambda (d) (list (flag (hf-eof (aref *files* d))))))
        (list "eoln" 1 (lambda (d) (list (flag (hf-eoln (aref *files* d))))))
        (list "erstat" 1 (lambda (d) (list (hf-erstat (aref *files* d)))))
        (list "close" 1 (lambda (d) (declare (ignore d)) nil))
        (list "getCurrentMinutes" 0 (lambda () (list 0)))
        (list "getCurrentDay" 0 (lambda () (list 1)))
        (list "getCurrentMonth" 0 (lambda () (list 1)))
        (list "getCurrentYear" 0 (lambda () (list 2026)))
        (list "tex_final_end" 0 (lambda () (setq *final-end* t) nil))))

; ---------------------------------------------------------------------------
; the run loop: the engine's FAST-RUN between two calls of a host function
;
; A run of tex.wasm is a sequence of stretches. A stretch is one call of
; WE::FAST-RUN-FUEL (FAST-RUN that also returns the fuel it did not use,
; engine/fast/stretch.lisp): the fast machine runs until it stops. It stops
; :unsupported at a call_ref of a host function (WE::HOST-REF-P, plan2.md
; P1). The driver then sets the status back to :run, makes the host step
; (HOST-STEP: the arguments off the operand stack, the Lisp function, the
; results pushed, the call_ref dropped) and starts the next stretch.
; What a theorem says: FAST-STRETCH-IS-SPEC-STEPS and FAST-RUN-IS-SPEC-STEPS
; of stretch.lisp, for a stretch that starts with the invariant WE::FM-INV.
; The driver checks the invariant at the start of every stretch
; (WE::FM-INV-CHECK, proved equal to it) and counts the stretches that have
; it. What no theorem says: the host step, and that the invariant holds
; after it (it is checked, not proved).

(defparameter *host-by-addr* nil)        ; vector: function address -> entry of *host-table*, or nil
(defparameter *steps* 0)
(defparameter *host-calls* 0)
(defparameter *fallbacks* 0)
(defparameter *shortcuts* 0)             ; data.drop applied without the fallback (see below)
(defparameter *stretches* 0)
(defparameter *stretches-inv* 0)         ; stretches that started with WE::FM-INV

(defun flush-console ()
  (let ((s (get-output-stream-string *console*)))
    (when (plusp (length s)) (write-string s) (finish-output))))

(defun host-step (entry)
  (destructuring-bind (name nargs fn) entry
    (let* ((vals (we::fm-vals *fm*))
           (args (reverse (mapcar #'caddr (subseq (cdr vals) 0 nargs))))
           (results (apply fn args)))
      (incf (gethash name *calls* 0))
      (incf *host-calls*)
      (we::update-fm-vals (append (mapcar (lambda (r) (list :const '(:i32) (ldb (byte 32 0) r))) (reverse results))
                                  (nthcdr (1+ nargs) vals))
                          *fm*)
      (we::update-fm-is (cdr (we::fm-is *fm*)) *fm*))))

; the host function the machine stopped at: the head is call_ref and the
; reference on the stack is a host function of the store (the engine's own
; test); nil when it stopped :unsupported for another reason
(defun host-entry (fm hosts)
  (let ((i (car (we::fm-is fm))) (v (car (we::fm-vals fm))))
    (and (consp i) (eq (car i) :call_ref)
         (we::host-ref-p v (we::fm-store fm))
         (or (and (integerp (cadr v)) (< -1 (cadr v) (length hosts)) (aref hosts (cadr v)))
             (error "host function ~s has no entry in the host table" v)))))

(defun run-engine (label)
  (let ((t0 (get-internal-real-time)) (n 0) (fm *fm*) (hosts *host-by-addr*)
        (period (if *quiet* 100000000 20000000)) (stretches 0) (inv 0) (shortcuts0 *shortcuts*))
    (declare (fixnum n period))
    (catch 'snapshot
     (loop
      (unless (eq (we::fm-status fm) :run) (return))
      (when (>= n *max-steps*) (format t "~a: step limit~%" label) (return))
      ; one stretch, cut at the next progress line
      (incf stretches)
      (when (and *check* (we::fm-inv-check fm)) (incf inv))
      (let ((chunk (min (- *max-steps* n) (- period (mod n period)))))
        (incf n (- chunk (we::fast-run-fuel chunk fm))))
      (when (eq (we::fm-status fm) :unsupported)
        (let ((entry (host-entry fm hosts)))
          (when entry
            (we::update-fm-status :run fm)
            (host-step entry))))
      (when (zerop (mod n period))
        (flush-console)
        (let ((s (/ (- (get-internal-real-time) t0) internal-time-units-per-second 1.0)))
          (if *quiet*
              (format t "~&[~d M WebAssembly instructions, ~d s]~%" (floor n 1000000) (round s))
            (format t "~&[~a: ~d M steps, ~,0f s, ~,2f M steps/s, ~d host calls, ~d fallbacks]~%"
                    label (floor n 1000000) s (/ n 1000000.0 (max s 0.001)) *host-calls* *fallbacks*)))
        (finish-output))))
    (flush-console)
    (incf *steps* n) (incf *stretches* stretches) (incf *stretches-inv* inv)
    (let ((s (/ (- (get-internal-real-time) t0) internal-time-units-per-second 1.0)))
      (if *quiet*
          (format t "~&~a: ~:d WebAssembly instructions in ~,1f s (~,2f M/s), ~:d host calls~%"
                  (if (eq (we::fm-status fm) :done) "tex.wasm returned" (format nil "tex.wasm stopped (~s)" (we::fm-status fm)))
                  n s (/ n 1000000.0 (max s 0.001)) *host-calls*)
        (progn
          (format t "~&~a: status ~s after ~d steps, ~,1f s (~,2f M steps/s), ~d host calls, ~d fallbacks~%"
                  label (we::fm-status fm) n s (/ n 1000000.0 (max s 0.001)) *host-calls* *fallbacks*)
          (format t "~a: ~d stretches of FAST-RUN, ~a; data.drop shortcut taken ~d times~%"
                  label stretches
                  (if *check* (format nil "~d started with FM-INV" inv) "FM-INV not checked (TEXNOCHECK)")
                  (- *shortcuts* shortcuts0))))
      (unless (member (we::fm-status fm) '(:done))
        (format t "  at ~a~%  vals ~a~%" (short (car (we::fm-is fm))) (short (we::fm-vals fm))))
      (finish-output))))

; The engine's fallback copies the whole memory out and back (72 MB here).
; data.drop takes it only because the engine has no frame lemma for that rule
; yet; the rule does not read or write memory bytes. Here the spec's rule
; function is applied to the state without the bytes, as the engine does for
; its frame-safe rules. This shortcut is assumed, not proved (plan2.md V7b):
; a stretch in which it is taken is not a run of the function in the
; theorems. It is counted per stretch (*SHORTCUTS*); tex.wasm executes
; data.drop at instantiation only. Every other fallback is counted and runs
; as the engine defines it.
(sb-int:encapsulate 'we::fast-apply-fallback 'count
  (lambda (f fn z redex fm)
    (cond ((eq fn 'w3t::step/r-data.drop)
           (incf *shortcuts*)
           (multiple-value-bind (ok z2 res) (we::apply-rule fn z redex)
             (values ok (if ok z2 z) res fm)))
          (t (incf *fallbacks*)
             (when (<= *fallbacks* 20) (format t "FALLBACK ~s on ~a~%" fn (short (car (last redex)))))
             (funcall f fn z redex fm)))))

; ---------------------------------------------------------------------------
; main

(defun find-export (name exports)
  (let ((codes (map 'list #'char-code name)))
    (wrt::%get-field (find-if (lambda (x) (equal (wrt::%get-field x :name) codes)) exports) :addr)))

(defun prepare ()                        ; everything up to the call of main
  ; 1. the helper module gives the store 18 functions of the right types and a memory
  (let* ((hm (car (w3t::gram/bmodule (file-bytes (concatenate 'string *dir* "/helper.wasm")))))
         (hs (we::machine-run 1000000 (we::ms-of-config (w3t::$instantiate *s0* hm nil))))
         (store (we::ms-store hs))
         (hexports (wrt::%get-field (wrt::%get-field (we::ms-frame hs) :module) :exports))
         (externs (mapcar (lambda (x) (wrt::%get-field x :addr)) hexports))
         (funcs (wrt::%get-field store :funcs))
         (hosts (make-array (length funcs) :initial-element nil)))
    (unless (eq (we::ms-status hs) :done) (error "helper instantiation: ~s" (we::ms-status hs)))
    ; 2. each exported function becomes a host function; memory 0 loses its bytes
    ;    (they live in the engine's array)
    (dolist (x hexports)
      (let ((addr (wrt::%get-field x :addr)) (name (codes-string (wrt::%get-field x :name))))
        (when (eq (car addr) :func)
          (let ((entry (assoc name *host-table* :test #'string=)))
            (unless entry (error "no host function ~a" name))
            (setf (aref hosts (cadr addr)) entry)
            (setq funcs (loop for f in funcs for a from 0
                              collect (if (= a (cadr addr)) (rset f :code (list :_hostfunc name)) f)))))))
    (setq store (rset store :funcs funcs))
    (setq store (rset store :mems
                      (list (rset (rset (car (wrt::%get-field store :mems)) :bytes nil)
                                  :type (list :page '(:i32) (list :|[%..%]| *pages* (list *pages*)))))))
    (setq *host-by-addr* hosts)
    (format t "HOST functions at ~s~%" (loop for a from 0 for e across hosts when e collect (cons a (car e))))
    ; 3. tex.wasm: decode (cached), instantiate against those addresses
    (setq *wasm-bytes* (length (file-vector (concatenate 'string *dl* "/tex.wasm"))))
    (let* ((m (decoded-module (concatenate 'string *dl* "/tex.wasm") (concatenate 'string *dir* "/tex.decoded")))
           (c0 (w3t::$instantiate store m externs))
           (s (we::ms-of-config c0)))
      (unless c0 (error "$instantiate returned nil"))
      ; 4. the memory: 1100 pages, the core dump (LaTeX loaded), then the instantiation
      (we::resize-fm-mem (* *pages* 65536) *fm*)
      (let ((dump (file-vector (concatenate 'string *dl* "/core.dump"))))
        (dotimes (k (length dump)) (we::update-fm-memi k (aref dump k) *fm*))
        (format t "MEMORY ~d bytes, core dump ~d bytes~%" (we::fm-mem-length *fm*) (length dump)))
      (we::fm-set (we::ms-store s) (we::ms-frame s) (we::ms-vals s) (we::ms-is s) (we::ms-ctrl s) (we::ms-status s) *fm*)
      (run-engine "instantiate")
      (unless (eq (we::fm-status *fm*) :done) (error "instantiation stopped"))
      ; 5. call main
      (let* ((inst (wrt::%get-field (we::fm-frame *fm*) :module))
             (addr (find-export "main" (wrt::%get-field inst :exports)))
             (c (w3t::$invoke (we::fm-store *fm*) (cadr addr) nil))
             (s (we::ms-of-config c)))
        (format t "MAIN at ~s~%" addr)
        (we::fm-set (we::ms-store s) (we::ms-frame s) (we::ms-vals s) (we::ms-is s) (we::ms-ctrl s) (we::ms-status s) *fm*)))))

(defun run-tex ()                        ; main, then the files TeX wrote
  (let ((t0 (get-internal-real-time)))
    (configure)
    (when *snap-file*                    ; a snapshot image: this run's input.tex from the snapshot line on
      (let ((new (host-file-bytes *job*)) (old (hf-content *snap-file*)))
        (unless (and (>= (length new) *snap-at*) (equalp (subseq new 0 *snap-at*) (subseq old 0 *snap-at*)))
          (error "the input before the snapshot line differs from the snapshot's; build the snapshot again"))
        (setf (hf-content *snap-file*) new)
        (setq *snap-file* nil *snap* nil)))
    (when *quiet*                        ; no ACL2 warnings (one guard-checking note) among TeX's output
      (acl2::f-put-global 'acl2::inhibit-output-lst '(acl2::warning acl2::observation) acl2::*the-live-state*)
      (format t "~a: WebAssembly engine WE::FAST-RUN (certified book engine/fast/fast)~%running tex.wasm (~:d bytes) on ~a~%"
              (acl2::f-get-global 'acl2::acl2-version acl2::*the-live-state*) *wasm-bytes* *job*)
      (finish-output))
    (run-engine "main")
    (when *snap-file*
      (format t "SNAPSHOT after ~d steps -> ~a~%" *steps* *snap*) (finish-output)
      (sb-ext:save-lisp-and-die *snap* :toplevel #'toplevel-run :executable t :save-runtime-options t))
    (unless *quiet* (format t "HOST calls: ~s~%" (let (l) (maphash (lambda (k v) (push (cons k v) l)) *calls*) (sort l #'> :key #'cdr))))
    (loop for f across *files*
          when (and (hf-regular f) (adjustable-array-p (hf-content f)) (plusp (length (hf-content f))))
          do (let ((path (format nil "~a.~a" *out* (subseq (hf-name f) (1+ (or (position #\. (hf-name f) :from-end t) -1))))))
               (with-open-file (o path :direction :output :if-exists :supersede :element-type '(unsigned-byte 8))
                 (write-sequence (hf-content f) o))
               (if *quiet*
                   (format t "wrote ~a (~:d bytes)~%" (file-namestring path) (length (hf-content f)))
                 (format t "WROTE ~a (~d bytes, from ~a)~%" path (length (hf-content f)) (hf-name f)))))
    (when (fboundp (quote census-report))
      (format t "CENSUS-HOST ~d host calls (call_ref of a host function, stepped by the driver)~%" *host-calls*)
      (funcall (quote census-report)))
    (unless *quiet*
      (format t "TOTAL ~d steps, final-end ~s, ~,1f s~%" *steps* *final-end*
              (/ (- (get-internal-real-time) t0) internal-time-units-per-second 1.0))
      (format t "STRETCHES ~d, ~a, data.drop shortcuts ~d~%" *stretches*
              (if *check* (format nil "~d started with FM-INV" *stretches-inv*) "FM-INV not checked")
              *shortcuts*))))

(declaim (ftype function toplevel-run))
(defmacro with-driver-errors (&body body)
  `(handler-bind ((error (lambda (e) (flush-console) (format t "~&DRIVER ERROR: ~a~%" e)
                           (sb-debug:print-backtrace :count 25) (finish-output) (sb-ext:exit :code 1 :abort t))))
     ,@body))

(defun toplevel-run ()                   ; what a saved image does when it starts
  (with-driver-errors (run-tex))
  (finish-output)
  (sb-ext:exit))

; TEXCENSUS=FILE: load FILE (plan/wasm-engine/notes/data/v0-ground/census.lisp)
; before the run; it counts the rule functions the run applies and RUN-TEX
; prints the counts.
(let ((c (sb-ext:posix-getenv "TEXCENSUS"))) (when (and c (plusp (length c))) (load c)))

; TEXMODE=build: prepare, then save an image that starts at the call of main
; (acl2-wasm-tex in the build directory, an executable: SBCL's runtime, this
; ACL2 image, and the runtime options ACL2 was started with). Otherwise
; prepare and run in this process.
(with-driver-errors (prepare))
(cond ((equal (sb-ext:posix-getenv "TEXMODE") "build")
       (finish-output)
       (sb-ext:save-lisp-and-die (concatenate 'string *dir* "/acl2-wasm-tex") :toplevel #'toplevel-run
                                 :executable t :save-runtime-options t))
      (t (with-driver-errors (run-tex)) (sb-ext:exit)))
