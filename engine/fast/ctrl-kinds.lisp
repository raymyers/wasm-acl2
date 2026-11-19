; License: MIT. See the file LICENSE at the top of the repository.
;
; One CTRL-OK (plan/wasm-engine/plan2.md V0). The step theorem of the fast
; machine (refine-op.lisp, FAST-STEP-REFINES) asks that every control entry
; is a label, a handler or a frame: CTRL-KINDS-OK. The invariant of the list
; machine (../machine/ok.lisp, CTRL-OK inside MACHINE-OK) says more, so it
; gives that hypothesis. This book also is the check that the books of the
; two machines can be included together, which V6 needs.
(in-package "WE")
(include-book "../machine/ok")
(include-book "refine-op")

(defthm ctrl-kinds-ok-when-ctrl-ok
  (implies (ctrl-ok c) (ctrl-kinds-ok c))
  :hints (("Goal" :in-theory (enable ctrl-ok ctrl-kinds-ok entry-ok))))

(defthm ctrl-kinds-ok-of-ms-ctrl-when-machine-ok
  (implies (machine-ok s) (ctrl-kinds-ok (ms-ctrl s))))
