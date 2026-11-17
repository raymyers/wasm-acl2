; E0: the benchmark runs. From engine/bench inside `nix develop ../..`:
;   sh build.sh && SBCL_USER_ARGS='--control-stack-size 1000' acl2 < run.lsp > OUT
; The larger control stack is needed for 64 pages: the spec's $ALLOCMEM/ITER2
; builds the byte list by plain recursion, one frame per byte, and the default
; 64 MB stack ends near 2.09 million bytes (32 pages).
(ld "bench.lsp")
(in-package "W3T")
(b3 "count" "run" (i32 20000) state)
(b3 "memloop" "run" (i32 10000) state)
(b3 "nested" "run" (i32 5000) state)
(b3 "throw" "run" (i32 3000) state)
(b3 "fac" "run" (i64 10000) state)
(b3 "fac" "run_rec" (i64 20) state)
; the call chain only at 1 page: its cost grows with the depth, not the
; memory (depths 300 and 1000 did not finish in minutes, see the note)
(bench1 "wasm/calls-1.wasm" "run" (list (i32 10)) state)
(bench1 "wasm/calls-1.wasm" "run" (list (i32 25)) state)
(bench1 "wasm/calls-1.wasm" "run" (list (i32 50)) state)
(bench1 "wasm/calls-1.wasm" "run" (list (i32 100)) state)
(bench1 "wasm/calls-1.wasm" "run" (list (i32 150)) state)
