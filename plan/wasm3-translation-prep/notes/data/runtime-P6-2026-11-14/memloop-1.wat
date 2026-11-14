;; P6 runtime baseline: the counting loop with one i32.store + i32.load per
;; iteration, memory of 1 page.
(module
  (memory 1)
  (func (export "count") (param $n i32) (result i32) (local $i i32)
    (block $done
      (loop $top
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (i32.store (i32.const 64) (local.get $i))
        (local.set $i (i32.add (i32.load (i32.const 64)) (i32.const 1)))
        (br $top)))
    (local.get $i)))
