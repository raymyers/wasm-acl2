;; The `spectest` host module that spec-test-3 scripts import from (as the
;; reference interpreter provides it), for 3.0 (wasm3 M7): the 1.0 module plus
;; "table64", an i64 table, which memory64/table64 imports. Host functions are not used;
;; the print functions are ordinary no-op functions.
(module
  (global (export "global_i32") i32 (i32.const 666))
  (global (export "global_i64") i64 (i64.const 666))
  (global (export "global_f32") f32 (f32.const 666.6))
  (global (export "global_f64") f64 (f64.const 666.6))
  (table (export "table") 10 20 funcref)
  (table (export "table64") i64 10 20 funcref)
  (memory (export "memory") 1 2)
  (func (export "print"))
  (func (export "print_i32") (param i32))
  (func (export "print_i64") (param i64))
  (func (export "print_f32") (param f32))
  (func (export "print_f64") (param f64))
  (func (export "print_i32_f32") (param i32 f32))
  (func (export "print_f64_f64") (param f64 f64)))
