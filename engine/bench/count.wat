;; E0: the counting loop of wasm3 M3 / prep P6: run(n) counts n down to 0.
(module
  (memory PAGES)
  (func (export "run") (param $n i32) (result i32)
    (block $done
      (loop $next
        (br_if $done (i32.eqz (local.get $n)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (br $next)))
    (local.get $n)))
