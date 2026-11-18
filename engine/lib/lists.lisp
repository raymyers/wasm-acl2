; License: MIT. See the file LICENSE at the top of the repository.
;
; Lists (plan/wasm-engine/plan2.md V0). Two parts.
;
; 1. The machine's list functions (machine/machine.lisp: guard T is why
;    they exist) are the built-in ones: CAR-T, CDR-T, LEN-T, APP, REV-ONTO
;    and NTH-T always, TAKE-N and DROP-N when the list is long enough. A
;    proof about the machine rewrites them to CAR, CDR, LEN, APPEND,
;    REVAPPEND, NTH, TAKE and NTHCDR with the theory MACHINE-LISTS, and then
;    needs one list library only.
; 2. That library: LEN, CAR, CDR, CONSP, TRUE-LISTP, TAKE, NTHCDR and NTH of
;    APPEND, of each other and of REVAPPEND. The facts are those of
;    std/lists, which is included locally and restated here, so that a book
;    that includes this one gets these rules and no others.
;
; Every rule of part 1 is disabled at the end of the book (a proof enables
; MACHINE-LISTS); the rules of part 2 are enabled.
(in-package "WE")
(include-book "../machine/machine")
; Only system books that the Nix ACL2 has certified (flake.nix systemBooks);
; std/lists/top and std/lists/nth are not among them.
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(set-prover-step-limit 1000000)

; ---------------------------------------------------------------------------
; 1. The machine's list functions

(defthm car-t-becomes-car
  (equal (car-t x) (car x)))

(defthm cdr-t-becomes-cdr
  (equal (cdr-t x) (cdr x)))

(defthm len-t-becomes-len
  (equal (len-t l) (len l)))

(defthm app-becomes-append
  (equal (app a b) (append a b)))

(defthm rev-onto-becomes-revappend
  (equal (rev-onto l acc) (revappend l acc)))

(defthm nth-t-becomes-nth
  (equal (nth-t n l) (nth n l)))

(defthm take-n-becomes-take
  (implies (<= (nfix n) (len l))
           (equal (take-n n l) (take n l))))

(defthm drop-n-becomes-nthcdr
  (implies (or (true-listp l) (<= (nfix n) (len l)))
           (equal (drop-n n l) (nthcdr n l))))

(deftheory machine-lists
  '(car-t-becomes-car cdr-t-becomes-cdr len-t-becomes-len app-becomes-append
    rev-onto-becomes-revappend nth-t-becomes-nth take-n-becomes-take
    drop-n-becomes-nthcdr))

; ---------------------------------------------------------------------------
; 2. The built-in list functions

; (equal (len l) 3) becomes (consp l), (consp (cdr l)), ... : the generated
; patterns of the specification test lengths against constants
(defthm equal-of-len-and-constant
  (implies (syntaxp (quotep k))
           (equal (equal (len l) k)
                  (if (posp k)
                      (and (consp l) (equal (len (cdr l)) (1- k)))
                    (and (equal k 0) (atom l))))))

(defthm len-of-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm len-when-not-consp
  (implies (not (consp l)) (equal (len l) 0)))

; a length that is a sum, against a constant: (equal (+ 1 (len v) (len r)) 1)
(defthm equal-of-constant-plus-and-constant
  (implies (and (syntaxp (quotep j)) (syntaxp (quotep k))
                (acl2-numberp j) (acl2-numberp k))
           (equal (equal (+ j x) k) (equal (fix x) (- k j)))))

(defthm equal-of-sum-of-lens-and-0
  (equal (equal (+ (len a) (len b)) 0) (and (atom a) (atom b))))

(defthm consp-of-append
  (equal (consp (append a b)) (or (consp a) (consp b))))

(defthm car-of-append
  (equal (car (append a b)) (if (consp a) (car a) (car b))))

(defthm cdr-of-append
  (equal (cdr (append a b)) (if (consp a) (append (cdr a) b) (cdr b))))

(defthm true-listp-of-append
  (equal (true-listp (append a b)) (true-listp b)))

(defthm append-of-nil
  (implies (true-listp a) (equal (append a nil) a)))

(defthm append-when-not-consp
  (implies (not (consp a)) (equal (append a b) b)))

(defthm append-of-cons
  (equal (append (cons x a) b) (cons x (append a b))))

(defthm associativity-of-append
  (equal (append (append a b) c) (append a (append b c))))

(defthm nth-of-append
  (equal (nth n (append a b))
         (if (< (nfix n) (len a)) (nth n a) (nth (- (nfix n) (len a)) b))))

(defthm nth-of-cons-and-constant
  (implies (syntaxp (quotep n))
           (equal (nth n (cons a b)) (if (zp n) a (nth (1- n) b)))))

(defthm take-of-append
  (equal (take n (append a b))
         (if (<= (nfix n) (len a))
             (take n a)
           (append a (take (- (nfix n) (len a)) b)))))

(defthm nthcdr-of-append
  (equal (nthcdr n (append a b))
         (if (<= (nfix n) (len a))
             (append (nthcdr n a) b)
           (nthcdr (- (nfix n) (len a)) b))))

(defthm len-of-take
  (equal (len (take n l)) (nfix n)))

(defthm len-of-nthcdr
  (equal (len (nthcdr n l)) (nfix (- (len l) (nfix n)))))

(defthm true-listp-of-nthcdr
  (implies (true-listp l) (true-listp (nthcdr n l))))

(defthm car-of-nthcdr
  (equal (car (nthcdr n l)) (nth n l)))

(defthm consp-of-nthcdr
  (equal (consp (nthcdr n l)) (< (nfix n) (len l))))

(defthm take-of-len
  (implies (true-listp l) (equal (take (len l) l) l)))

(defthm nthcdr-of-len
  (implies (true-listp l) (equal (nthcdr (len l) l) nil)))

(defthm append-of-take-and-nthcdr
  (implies (<= (nfix n) (len l))
           (equal (append (take n l) (nthcdr n l)) l)))

; MV-NTH is kept disabled by the proof books; a component of an explicit MV
(defthm mv-nth-of-cons-and-constant
  (implies (syntaxp (quotep n))
           (equal (mv-nth n (cons a b)) (if (zp n) a (mv-nth (1- n) b)))))

; REVAPPEND: with an accumulator that is not NIL it is an APPEND, so
; (revappend x nil) is the one form that stays.
(defthm revappend-becomes-append-of-revappend-nil
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (revappend x acc) (append (revappend x nil) acc))))

(defthm len-of-revappend
  (equal (len (revappend x acc)) (+ (len x) (len acc))))

(defthm true-listp-of-revappend
  (equal (true-listp (revappend x acc)) (true-listp acc)))

(defthm consp-of-revappend
  (equal (consp (revappend x acc)) (or (consp x) (consp acc))))

(defthm revappend-of-append
  (equal (revappend (append a b) nil)
         (append (revappend b nil) (revappend a nil))))

; the top K elements of a stack and the rest, in the order of the
; configuration: rev(l) = rev(nthcdr k l) ++ rev(take k l)
(defthm revappend-of-take-and-nthcdr
  (implies (<= (nfix k) (len l))
           (equal (append (revappend (nthcdr k l) nil) (revappend (take k l) nil))
                  (revappend l nil))))

(in-theory (disable machine-lists))
