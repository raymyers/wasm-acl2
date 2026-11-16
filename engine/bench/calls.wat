;; E0: a recursive call chain of depth n: run(n) = n + run(n-1), run(0) = 0.
(module
  (memory PAGES)
  (func $run (export "run") (param $n i32) (result i32)
    (if (result i32) (i32.eqz (local.get $n))
      (then (i32.const 0))
      (else (i32.add (local.get $n)
                     (call $run (i32.sub (local.get $n) (i32.const 1))))))))
