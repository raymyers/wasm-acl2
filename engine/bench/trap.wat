;; E0 item 4 only (not timed): a trap and an uncaught exception.
;; div(x) = 7 / x traps for x = 0; uncaught(x) throws tag $e with x.
(module
  (memory PAGES)
  (tag $e (param i32))
  (func (export "div") (param $x i32) (result i32)
    (i32.div_u (i32.const 7) (local.get $x)))
  (func (export "uncaught") (param $x i32) (result i32)
    (throw $e (local.get $x))))
