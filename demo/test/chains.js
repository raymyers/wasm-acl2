// W8 item 3: the rule chain of every step of six small programs, against
// chains written by hand from the 3.0 spec's reduction rules (Step,
// Step_pure, Step_read in specification/wasm-3.0/4.3-execution.instructions
// at WebAssembly/spec@943c5df). Each step's chain is read by the glue's
// STEP-RULES (shim/rule.lisp recorder) and must be exactly the expected one.
// How the expected chains follow from the rules:
// - an invocation starts as (ref.func_addr a) (call_ref t) after the
//   arguments: Step/call_ref-func makes FRAME_ n {f} (LABEL_ m {} body);
// - a redex inside a frame or label is reached by Step/ctxt-frame or
//   Step/ctxt-label; Step/ctxt-instrs only when values precede the redex or
//   instructions follow it (the rule's side condition); a handler by
//   Step/ctxt-handler;
// - then Step/pure or Step/read and the rule itself, or a Step rule
//   (call_ref-func, throw) directly;
// - LABEL_/FRAME_ around values: Step_pure/label-vals, frame-vals.
// Usage: node chains.js BUILD_DIR     (WABT_JS: wabt's JS build)
'use strict';
const path = require('path');
const build = path.resolve(process.argv[2]);
const jscl = require(path.join(build, 'jscl.js'));
require(path.join(build, 'wasm3.js'));
const L = require('../driver/lisp.js')(jscl);

const F = 'Step/ctxt-frame', LB = 'Step/ctxt-label', I = 'Step/ctxt-instrs', H = 'Step/ctxt-handler';
const P = 'Step/pure', R = 'Step/read', CALL = 'Step/call_ref-func';
const pure = r => [P, 'Step_pure/' + r], read = r => [R, 'Step_read/' + r];
const PROGRAMS = [
  { name: 'nop', wat: '(module (func (export "f") nop))', args: [], result: 'NIL',
    chains: [[CALL], [F, LB, ...pure('nop')], [F, ...pure('label-vals')], [...pure('frame-vals')]] },
  { name: 'i32.add', wat: '(module (func (export "f") (result i32) (i32.add (i32.const 1) (i32.const 2))))', args: [],
    result: '((:CONST (:I32) 3))',
    chains: [[CALL], [F, LB, ...pure('binop-val')], [F, ...pure('label-vals')], [...pure('frame-vals')]] },
  { name: 'block/br', wat: '(module (func (export "f") (result i32) (block (result i32) (i32.const 7) (br 0) (i32.const 8))))', args: [],
    result: '((:CONST (:I32) 7))',
    chains: [[CALL], [F, LB, ...read('block')], [F, LB, ...pure('br-label-zero')], [F, ...pure('label-vals')], [...pure('frame-vals')]] },
  { name: 'call/return', wat: '(module (func $g (result i32) (i32.const 5) (return)) (func (export "f") (result i32) (call $g)))', args: [],
    result: '((:CONST (:I32) 5))',
    chains: [[CALL], [F, LB, ...read('call')], [F, LB, CALL], [F, LB, F, ...pure('return-label')],
             [F, LB, ...pure('return-frame')], [F, ...pure('label-vals')], [...pure('frame-vals')]] },
  { name: 'trap', wat: '(module (func (export "f") unreachable))', args: [], result: ':TRAP',
    chains: [[CALL], [F, LB, ...pure('unreachable')], [F, ...pure('trap-label')], [...pure('trap-frame')]] },
  { name: 'throw/catch',
    wat: `(module (tag $e (param i32))
      (func (export "f") (result i32)
        (block $h (result i32)
          (try_table (catch $e $h) (i32.const 3) (throw $e))
          (i32.const 0))))`,
    args: [], result: '((:CONST (:I32) 3))',
    chains: [[CALL], [F, LB, ...read('block')], [F, LB, LB, I, ...read('try_table')],
             [F, LB, LB, I, H, LB, 'Step/throw'], [F, LB, LB, I, H, ...read('throw_ref-label')],
             [F, LB, LB, I, ...read('throw_ref-handler-catch')], [F, LB, ...pure('br-label-zero')],
             [F, ...pure('label-vals')], [...pure('frame-vals')]] },
];

async function main() {
  const wabt = await require(process.env.WABT_JS)();
  let ok = true, total = 0;
  for (const p of PROGRAMS) {
    const bin = wabt.parseWat(p.name + '.wat', p.wat, { exceptions: true }).toBinary({}).buffer;
    const [st, env] = L.toArray(L.fn('DEMO', 'LOAD-MODULE')(L.list([...bin]), L.fn('DEMO', 'EMPTY-ENV')()));
    let [s, c] = L.toArray(L.fn('DEMO', 'START-INVOKE')(env, L.list([...Buffer.from('f')]), L.list(p.args)));
    const got = [];
    while (got.length < 50) {
      const [c2, ch] = L.toArray(L.fn('DEMO', 'STEP-RULES')(c));
      if (c2 === L.NIL) break;
      got.push(L.toArray(ch).map(x => L.show(x).replace(/^"|"$/g, ""))); c = c2;
    }
    const [res] = L.toArray(L.fn('DEMO', 'FINISH-CONFIG')(c, env));
    const bad = [];
    for (let k = 0; k < Math.max(got.length, p.chains.length); k++) {
      const g = (got[k] || []).join(' → '), w = (p.chains[k] || []).join(' → ');
      if (g !== w) bad.push(`step ${k}: got ${g || '(none)'}; want ${w || '(none)'}`);
    }
    const resOk = L.show(res) === p.result;
    const pass = L.show(st) === ':OK' && L.show(s) === ':OK' && !bad.length && resOk && got.every(x => x.length);
    ok = ok && pass; total += got.length;
    console.log(`W8-CHAINS ${pass ? 'PASS' : 'FAIL'} ${p.name}: ${got.length} steps, result ${L.show(res)}${resOk ? '' : ' (want ' + p.result + ')'}`);
    for (const b of bad) console.log('  ' + b);
  }
  console.log(`W8-CHAINS ${ok ? 'all' : 'NOT all'} ${PROGRAMS.length} programs match the hand-written chains (${total} steps)`);
  process.exit(ok ? 0 : 1);
}
main().catch(e => { console.log('W8-CHAINS FAIL threw: ' + (e && e.stack || e)); process.exit(1); });
