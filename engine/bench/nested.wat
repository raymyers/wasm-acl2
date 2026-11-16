;; E0: nested blocks 8 deep. Each iteration enters 8 blocks and leaves them
;; with one br out of the innermost to the outermost. run(n) returns 0.
(module
  (memory PAGES)
  (func (export "run") (param $n i32) (result i32)
    (block $done
      (loop $next
        (br_if $done (i32.eqz (local.get $n)))
        (block $b1 (block $b2 (block $b3 (block $b4
          (block $b5 (block $b6 (block $b7 (block $b8
            (local.set $n (i32.sub (local.get $n) (i32.const 1)))
            (br $b1)))))))))
        (br $next)))
    (local.get $n)))
