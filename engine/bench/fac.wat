;; E0: the factorial of the demo (demo/web/examples.js, "factorial"),
;; exported as run (the loop) and run_rec (the recursion).
(module
  (memory PAGES)
  (func (export "run") (param $n i64) (result i64)
    (local $acc i64)
    (local.set $acc (i64.const 1))
    (block $done
      (loop $next
        (br_if $done (i64.le_u (local.get $n) (i64.const 1)))
        (local.set $acc (i64.mul (local.get $acc) (local.get $n)))
        (local.set $n (i64.sub (local.get $n) (i64.const 1)))
        (br $next)))
    (local.get $acc))
  (func $fac_rec (export "run_rec") (param $n i64) (result i64)
    (if (result i64) (i64.le_u (local.get $n) (i64.const 1))
      (then (i64.const 1))
      (else (i64.mul (local.get $n)
                     (call $fac_rec (i64.sub (local.get $n) (i64.const 1))))))))
