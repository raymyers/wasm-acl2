;; E0: the counting loop with an i32.store and an i32.load per iteration
;; (address 0), as wasm3 M3's memloop. run(n) returns the last value loaded.
(module
  (memory PAGES)
  (func (export "run") (param $n i32) (result i32)
    (local $x i32)
    (block $done
      (loop $next
        (br_if $done (i32.eqz (local.get $n)))
        (i32.store (i32.const 0) (local.get $n))
        (local.set $x (i32.load (i32.const 0)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (br $next)))
    (local.get $x)))
