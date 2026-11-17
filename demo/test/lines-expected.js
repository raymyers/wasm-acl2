// W6 exit: the expected printed line of every configuration of a
// step-through, written by hand from wabt's printed text (the line numbers
// below are those of `Lines.print`, shown in the comments) and the
// reduction rules of the Wasm 3.0 semantics. They are NOT recorded from the
// mapper (demo/web/semantics.js).
//
// Entry k is the line for the configuration after k steps (entry 0: before
// the first step). `null`: no line, for
//   - the configuration before the first step and the final one: the
//     invocation ($invoke's REF.FUNC_ADDR / CALL_REF) and its result are
//     outside the module's code;
// and these conventions, the same for every example:
//   - a constant (i32.const, v128.const, ...) is a value in the
//     configuration, never a redex: its line is never highlighted;
//   - a call takes two steps on the call's line: CALL x becomes
//     (REF.FUNC_ADDR a) (CALL_REF t), which then becomes FRAME_(LABEL_(body));
//   - block/loop: one step on their line turns them into a LABEL_; `br l`
//     with l > 0 first leaves the innermost LABEL_ (BR l-1 is then the
//     redex at the level of the block or loop being left: that line);
//     a taken br_if first becomes BR (still the br_if's line);
//   - if: one step on its line turns it into a BLOCK of the branch taken
//     (still the if's line), then a LABEL_;
//   - a level with only values left (the next step exits it): the line of
//     its end: a block's or if's `end` line, a function's last line (the
//     one with the closing parenthesis), for the body's LABEL_ and for
//     the FRAME_ alike;
//   - an exception on its way out (THROW_REF): the end line of the level
//     it is leaving, as above (try_table: its `end`, also while the handler
//     catches it);
//   - the catch clause's branch (BR) is at the try_table's position: its line.
'use strict';
module.exports = [
  {
    // factorial, func 0 (lines 3–24):
    //  5 i64.const 1   6 local.set 1   7 block   8 loop   9 local.get 0
    // 10 i64.const 1  11 i64.le_u     12 br_if 1 13 local.get 1  14 local.get 0
    // 15 i64.mul      16 local.set 1  17 local.get 0  18 i64.const 1  19 i64.sub
    // 20 local.set 0  21 br 0  22 end (loop)  23 end (block)  24 local.get 1)
    example: 'factorial', export: 'fac', args: ['3'],
    lines: [null,
      6, 7, 8, 9,                                   // local.set 1, block, loop, into the loop
      11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 8, 9, // n = 3: br_if not taken ... br 0, loop again
      11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 8, 9, // n = 2
      11, 12, 12,                                   // n = 1: br_if taken (becomes BR 1)
      8,                                            // BR 0 leaving the loop's LABEL_
      24,                                           // the block's LABEL_ left: local.get 1
      24, 24,                                       // only values: body LABEL_, then FRAME_
      null],
    // every instruction line that is not a constant (5, 10, 18 are values)
    covers: [6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 24],
  },
  {
    // factorial, func 1 (lines 25–38): 26 local.get 0  27 i64.const 1
    // 28 i64.le_u  29 if (result i64)  30 i64.const 1  31 else  32 local.get 0
    // 33 local.get 0  34 i64.const 1  35 i64.sub  36 call 1  37 i64.mul  38 end)
    example: 'factorial', export: 'fac_rec', args: ['2'],
    lines: [null,
      26, 28, 29, 29,                               // n = 2: le_u false, if -> else BLOCK
      32, 33, 35, 36, 36,                           // else: ..., call 1 (CALL, then CALL_REF)
      26, 28, 29, 29,                               // n = 1 (new frame): if -> then BLOCK
      38,                                           // then-LABEL_ holds only i64.const 1: if's end
      38, 38,                                       // body LABEL_ and FRAME_ of the inner call: values only
      37,                                           // back in the caller's else: i64.mul
      38, 38, 38,                                   // else-LABEL_, body LABEL_, FRAME_: values only
      null],
    covers: [26, 28, 29, 32, 33, 35, 36, 37, 38],
  },
  {
    // float, func 0 (lines 4–12): 5 local.get 0  6 local.get 0  7 f64.mul
    // 8 local.get 1  9 local.get 1  10 f64.mul  11 f64.add  12 f64.sqrt)
    example: 'float', export: 'hypot', args: ['1.5', '2'],
    lines: [null, 5, 6, 7, 8, 9, 10, 11, 12, 12, 12, null],
  },
  {
    // float, func 1 (lines 13–17): 14 local.get 0  15 f32.const 3  16 f32.div  17 f32.nearest)
    example: 'float', export: 'third', args: ['10'],
    lines: [null, 14, 16, 17, 17, 17, null],
  },
  {
    // memory, func 0 (lines 3–47): first loop 5 block, 6 loop, 7 local.get 1,
    // 8 local.get 0, 9 i32.ge_u, 10 br_if 1, 11 local.get 1, 12 i32.const 2,
    // 13 i32.shl, 14 local.get 1, 15 local.get 1, 16 i32.mul, 17 i32.store,
    // 18 local.get 1, 19 i32.const 1, 20 i32.add, 21 local.set 1, 22 br 0;
    // 25 i32.const 0, 26 local.set 1; second loop 27 block, 28 loop,
    // 29 local.get 1, 30 local.get 0, 31 i32.ge_u, 32 br_if 1, 33 local.get 2,
    // 34 local.get 1, 35 i32.const 2, 36 i32.shl, 37 i32.load, 38 i32.add,
    // 39 local.set 2, 40 local.get 1, 41 i32.const 1, 42 i32.add,
    // 43 local.set 1, 44 br 0; 47 local.get 2)
    example: 'memory', export: 'squares', args: ['1'],
    lines: [null,
      5, 6,                                         // block, loop
      7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 6, // i = 0: store 0 at 0, br 0
      7, 8, 9, 10, 10, 6,                           // i = 1: br_if taken (BR 1), leaves the loop
      26, 27, 28,                                   // block left; local.set 1, block, loop
      29, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 42, 43, 44, 28, // i = 0: load, add
      29, 30, 31, 32, 32, 28,                       // i = 1: leave the loop
      47, 47, 47,                                   // local.get 2; body LABEL_, FRAME_ values only
      null],
  },
  {
    // gc (fallback printer, lines 2–17): 4 local.get 0  5 local.get 1
    // 6 struct.new 0  7 local.set 2  8 local.get 2  9 local.get 0  10 local.get 1
    // 11 i32.mul  12 struct.set 0 1  13 local.get 2  14 struct.get 0 0
    // 15 local.get 2  16 struct.get 0 1  17 i32.add))
    example: 'gc', export: 'f', args: ['3', '4'],
    lines: [null, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 17, 17, null],
  },
  {
    // exception, func 0 (lines 4–14): 5 local.get 0  6 i32.const 0  7 i32.lt_s
    // 8 if  9 local.get 0  10 throw 0  11 end  12 local.get 0  13 i32.const 2  14 i32.mul)
    // func 1 (lines 15–25): 16 block  17 try_table (catch 0 0)  19 local.get 0
    // 20 call 0  21 end  22 return  23 end  24 i32.const 1000  25 i32.add)
    example: 'exception', export: 'safe', args: ['-7'],
    lines: [null,
      16, 17, 19, 20, 20,                           // block, try_table, local.get 0, call 0 (2 steps)
      5, 7, 8, 8, 9, 10,                            // func 0: x < 0, if -> then, throw 0
      11,                                           // exception leaving the if's LABEL_: its end
      14, 14, 14,                                   // leaving func 0's body (drops the rest, then exits), FRAME_
      21, 21,                                       // leaving the try_table's LABEL_, caught by HANDLER_: try_table's end
      17,                                           // the catch's BR 0, at the try_table's position
      25, 25, 25,                                   // block left: i32.add; then values only
      null],
  },
  {
    // the same with x >= 0: no exception, `return` out of the block
    example: 'exception', export: 'safe', args: ['5'],
    lines: [null,
      16, 17, 19, 20, 20,
      5, 7, 8, 8,                                   // if, false, no else: an empty BLOCK
      11,                                           // its LABEL_ holds nothing: the if's end
      12, 14, 14, 14,                               // local.get 0, i32.mul; values only (body, FRAME_)
      21, 21,                                       // try_table's LABEL_, then HANDLER_, values only
      22,                                           // return
      16,                                           // RETURN leaving the block's LABEL_ (block's position)
      25,                                           // RETURN at the FRAME_ (func 1's last line)
      null],
  },
  {
    // exception, func 2 (lines 26–28): 27 local.get 0  28 call 0)
    example: 'exception', export: 'unsafe', args: ['-7'],
    lines: [null,
      27, 28, 28,                                   // local.get 0, call 0 (2 steps)
      5, 7, 8, 8, 9, 10, 11, 14, 14, 14,            // as in safe(-7)
      28, 28,                                       // leaving func 2's body, its FRAME_
      null],                                        // uncaught: the normal form (REF.EXN_ADDR a) THROW_REF
  },
  {
    // simd, func 0 (lines 3–26): 5 local.get 0  6 i32x4.splat  7 local.get 1
    // 8 replace_lane 1  9 local.get 2  10 replace_lane 2  11 local.get 3
    // 12 replace_lane 3  13 v128.const  14 i32x4.mul  15 local.set 4
    // 16 local.get 4  17 extract_lane 0  18 local.get 4  19 extract_lane 1
    // 20 i32.add  21 local.get 4  22 extract_lane 2  23 local.get 4
    // 24 extract_lane 3  25 i32.add  26 i32.add)
    example: 'simd', export: 'dot', args: ['5', '6', '7', '8'],
    lines: [null, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 26, 26, null],
  },
];
