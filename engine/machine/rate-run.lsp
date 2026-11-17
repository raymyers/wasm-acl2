; E6: rate of the list machine on the E0 benchmarks (spec steps it stands
; for, per second), for comparison with E0. Not a goal of E6.
(ld "difftest.lsp")
(in-package "WE")
(rate1 "count 20000" "../bench/wasm/count-1.wasm" "run" (list (i32 20000)) state)
(rate1 "memloop 10000 (1 page)" "../bench/wasm/memloop-1.wasm" "run" (list (i32 10000)) state)
(rate1 "memloop 10000 (16 pages)" "../bench/wasm/memloop-16.wasm" "run" (list (i32 10000)) state)
(rate1 "nested 5000" "../bench/wasm/nested-1.wasm" "run" (list (i32 5000)) state)
(rate1 "throw 3000" "../bench/wasm/throw-1.wasm" "run" (list (i32 3000)) state)
(rate1 "calls 150" "../bench/wasm/calls-1.wasm" "run" (list (i32 150)) state)
