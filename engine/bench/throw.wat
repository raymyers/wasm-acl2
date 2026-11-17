;; E0: a try_table that catches a throw. Each iteration calls $f, which
;; throws tag $e with the counter; the handler around the call catches it.
;; run(n) returns the sum of the caught values.
(module
  (memory PAGES)
  (tag $e (param i32))
  (func $f (param $x i32) (throw $e (local.get $x)))
  (func (export "run") (param $n i32) (result i32)
    (local $acc i32)
    (block $done
      (loop $next
        (br_if $done (i32.eqz (local.get $n)))
        (block $h (result i32)
          (try_table (catch $e $h)
            (call $f (local.get $n)))
          (unreachable))
        (local.set $acc (i32.add (local.get $acc)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (br $next)))
    (local.get $acc)))
