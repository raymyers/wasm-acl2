;; W0 item 4: a module with one page of memory. Decode, instantiate (data
;; segment) and a run that stores, loads, fills and copies memory.
(module
  (memory 1)
  (data (i32.const 16) "hello, wasm")
  (func (export "f") (result i32)
    (i32.store (i32.const 8) (i32.const 42))
    (memory.fill (i32.const 1024) (i32.const 7) (i32.const 256))
    (memory.copy (i32.const 2048) (i32.const 16) (i32.const 11))
    (i32.add (i32.load (i32.const 8)) (i32.load8_u (i32.const 2048)))))
