// demo/web/examples.js: the page's examples (plan/wasm3-demo W5 item 1).
// Each has a source (WAT, or hex bytes with ;; comments), the export to
// call and its arguments. The GC example is hex: wabt 1.0.39 (the bundled
// WAT converter, D8) cannot parse GC instructions (struct.new: "unexpected
// token"), so its bytes are written out below with the WAT as comments.
'use strict';
const EXAMPLES = [
  {
    id: 'factorial', title: 'Factorial (i64)', export: 'fac', args: ['20'],
    source: `(module
  ;; n! with a loop; i64 arithmetic wraps mod 2^64 above 20!
  (func (export "fac") (param $n i64) (result i64)
    (local $acc i64)
    (local.set $acc (i64.const 1))
    (block $done
      (loop $next
        (br_if $done (i64.le_u (local.get $n) (i64.const 1)))
        (local.set $acc (i64.mul (local.get $acc) (local.get $n)))
        (local.set $n (i64.sub (local.get $n) (i64.const 1)))
        (br $next)))
    (local.get $acc))
  ;; the same recursively: a branch and a call per level
  (func $fac_rec (export "fac_rec") (param $n i64) (result i64)
    (if (result i64) (i64.le_u (local.get $n) (i64.const 1))
      (then (i64.const 1))
      (else (i64.mul (local.get $n)
                     (call $fac_rec (i64.sub (local.get $n) (i64.const 1))))))))`,
  },
  {
    id: 'float', title: 'Float math (f64, f32)', export: 'hypot', args: ['1.5', '2'],
    source: `(module
  ;; sqrt(x*x + y*y), correctly rounded at each step
  (func (export "hypot") (param $x f64) (param $y f64) (result f64)
    (f64.sqrt (f64.add (f64.mul (local.get $x) (local.get $x))
                       (f64.mul (local.get $y) (local.get $y)))))
  ;; x / 3 in single precision, then the nearest integer
  (func (export "third") (param $x f32) (result f32)
    (f32.nearest (f32.div (local.get $x) (f32.const 3)))))`,
  },
  {
    id: 'memory', title: 'Memory load/store', export: 'squares', args: ['10'],
    source: `(module
  (memory 1)
  ;; store i*i at address 4i for i < n, then load them back and add them up
  (func (export "squares") (param $n i32) (result i32)
    (local $i i32) (local $s i32)
    (block $b (loop $l
      (br_if $b (i32.ge_u (local.get $i) (local.get $n)))
      (i32.store (i32.shl (local.get $i) (i32.const 2))
                 (i32.mul (local.get $i) (local.get $i)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (local.set $i (i32.const 0))
    (block $b (loop $l
      (br_if $b (i32.ge_u (local.get $i) (local.get $n)))
      (local.set $s (i32.add (local.get $s)
                             (i32.load (i32.shl (local.get $i) (i32.const 2)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (local.get $s)))`,
  },
  {
    id: 'gc', title: 'GC struct', export: 'f', args: ['3', '4'],
    source: `;; hex bytes: wabt 1.0.39 does not parse GC instructions.
;; (module
;;   (type $p (struct (field i32) (field (mut i32))))
;;   (func (export "f") (param $a i32) (param $b i32) (result i32)
;;     (local $r (ref $p))
;;     (local.set $r (struct.new $p (local.get $a) (local.get $b)))
;;     (struct.set $p 1 (local.get $r)
;;                 (i32.mul (local.get $a) (local.get $b)))
;;     (i32.add (struct.get $p 0 (local.get $r))
;;              (struct.get $p 1 (local.get $r)))))
00 61 73 6d 01 00 00 00         ;; magic, version 1
01 0d 02                        ;; types (2)
   5f 02 7f 00 7f 01            ;;  0: struct i32, mut i32
   60 02 7f 7f 01 7f            ;;  1: func [i32 i32] -> [i32]
03 02 01 01                     ;; funcs: 0 has type 1
07 05 01 01 66 00 00            ;; exports: "f" = func 0
0a 28 01 26                     ;; code: 1 body, 38 bytes
   01 01 64 00                  ;;  local r: (ref 0)
   20 00 20 01 fb 00 00 21 02   ;;  r = struct.new 0 a b
   20 02 20 00 20 01 6c         ;;  r, a * b
   fb 05 00 01                  ;;  struct.set 0 1
   20 02 fb 02 00 00            ;;  struct.get 0 0 r
   20 02 fb 02 00 01 6a 0b      ;;  struct.get 0 1 r; add; end`,
  },
  {
    id: 'exception', title: 'Exception (try_table, throw)', export: 'safe', args: ['-7'],
    source: `(module
  (tag $negative (param i32))
  ;; 2x, but a negative x is thrown as the payload of $negative
  (func $double (param $x i32) (result i32)
    (if (i32.lt_s (local.get $x) (i32.const 0))
      (then (throw $negative (local.get $x))))
    (i32.mul (local.get $x) (i32.const 2)))
  ;; catches $negative and returns payload + 1000
  (func (export "safe") (param $x i32) (result i32)
    (block $handler (result i32)
      (try_table (result i32) (catch $negative $handler)
        (call $double (local.get $x)))
      (return))
    (i32.add (i32.const 1000)))
  ;; the same call without a handler: the exception escapes
  (func (export "unsafe") (param $x i32) (result i32)
    (call $double (local.get $x))))`,
  },
  {
    id: 'print', title: 'Print (host import)', export: 'squares', args: ['4'],
    source: `(module
  ;; host functions: the page provides env.print_* to both engines
  (import "env" "print_i32" (func $print_i32 (param i32)))
  (import "env" "print_f64" (func $print_f64 (param f64)))
  ;; prints i*i for i < n, then n / 4
  (func (export "squares") (param $n i32)
    (local $i i32)
    (block $done
      (loop $next
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (call $print_i32 (i32.mul (local.get $i) (local.get $i)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $next)))
    (call $print_f64 (f64.div (f64.convert_i32_u (local.get $n)) (f64.const 4)))))`,
  },
  {
    id: 'simd', title: 'SIMD lane op (i32x4)', export: 'dot', args: ['5', '6', '7', '8'],
    source: `(module
  ;; [a b c d] * [1 2 3 4] lane by lane, then the four lanes added up
  (func (export "dot") (param $a i32) (param $b i32) (param $c i32) (param $d i32) (result i32)
    (local $v v128)
    (local.set $v
      (i32x4.mul
        (i32x4.replace_lane 3
          (i32x4.replace_lane 2
            (i32x4.replace_lane 1 (i32x4.splat (local.get $a)) (local.get $b))
            (local.get $c))
          (local.get $d))
        (v128.const i32x4 1 2 3 4)))
    (i32.add
      (i32.add (i32x4.extract_lane 0 (local.get $v)) (i32x4.extract_lane 1 (local.get $v)))
      (i32.add (i32x4.extract_lane 2 (local.get $v)) (i32x4.extract_lane 3 (local.get $v))))))`,
  },
];
if (typeof module !== 'undefined') module.exports = EXAMPLES;
