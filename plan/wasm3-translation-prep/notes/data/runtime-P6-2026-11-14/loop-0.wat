;; P6 runtime baseline: a counting loop; memory of 0 pages (none if 0).
(module
  
  (func (export "count") (param $n i32) (result i32) (local $i i32)
    (block $done
      (loop $top
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $top)))
    (local.get $i)))
