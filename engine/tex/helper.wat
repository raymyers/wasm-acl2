;; Declares the types of tex.wasm's 18 imported functions and its memory.
;; The driver instantiates this module with the spec, then turns each
;; exported function into a host function (:_HOSTFUNC name) in the store.
;; Exports are in tex.wasm's import order.
(module
  (func (export "printInteger") (param i32 i32) unreachable)
  (func (export "printChar") (param i32 i32) unreachable)
  (func (export "printString") (param i32 i32) unreachable)
  (func (export "printNewline") (param i32) unreachable)
  (func (export "reset") (param i32 i32) (result i32) unreachable)
  (func (export "inputln") (param i32 i32 i32 i32 i32 i32 i32) (result i32) unreachable)
  (func (export "rewrite") (param i32 i32) (result i32) unreachable)
  (func (export "get") (param i32 i32 i32) unreachable)
  (func (export "put") (param i32 i32 i32) unreachable)
  (func (export "eof") (param i32) (result i32) unreachable)
  (func (export "eoln") (param i32) (result i32) unreachable)
  (func (export "erstat") (param i32) (result i32) unreachable)
  (func (export "close") (param i32) unreachable)
  (func (export "getCurrentMinutes") (result i32) unreachable)
  (func (export "getCurrentDay") (result i32) unreachable)
  (func (export "getCurrentMonth") (result i32) unreachable)
  (func (export "getCurrentYear") (result i32) unreachable)
  (func (export "tex_final_end") unreachable)
  (memory (export "memory") 1 1100))
