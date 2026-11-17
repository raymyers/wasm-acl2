// W4 item 2: host imports through %HOSTCALL-HOOK (driver/glue.lisp). A host
// module "env" with one function, inc (i32) -> i32, implemented in JS
// (returns its argument + 1, and records the call); a guest module that
// imports env.inc and calls it from its export "f" (x) = inc(x) * 2. Checks
// the result, that the host saw the call with the right argument, and the
// default host (no result: no rule applies, the run stops at the call). The
// spectest module of the conformance runs is an ordinary module (its prints
// are no-op wasm functions), not host functions.
// Usage: node host.js BUILD_DIR      (WABT_JS: wabt's JS build, for the WAT)
'use strict';
const path = require('path');
const build = path.resolve(process.argv[2]);
const jscl = require(path.join(build, 'jscl.js'));
require(path.join(build, 'wasm3.js'));
const L = require('../driver/lisp.js')(jscl);

const kw = L.kw, NONE_DEFAULT = globalThis.DEMOHOST;
const bytesOf = s => L.list([...Buffer.from(s)]);
const lispBytes = u8 => L.list([...u8]);

async function main() {
  const wabt = await require(process.env.WABT_JS)();
  const wasm = wat => lispBytes(wabt.parseWat('m.wat', wat).toBinary({}).buffer);
  // the host's signature module: its exported functions become host functions
  const hostSig = wasm('(module (func (export "inc") (param i32) (result i32) unreachable))');
  const guest = wasm(`(module (import "env" "inc" (func $inc (param i32) (result i32)))
    (func (export "f") (param i32) (result i32) (i32.mul (call $inc (local.get 0)) (i32.const 2))))`);

  const calls = [];
  const name = hf => L.toArray(hf).map(x => String.fromCharCode(...L.toArray(x))).join('.');
  globalThis.DEMOHOST = {
    call(hf, vals, none) {
      const args = L.toArray(vals).map(v => L.toArray(v)[2]);
      // called several times per step, also with other splits of the arguments
      // (glue.lisp HOST-CALL): answer as a function, record distinct calls
      if (name(hf) !== "env.inc" || args.length !== 1) return none;
      const c = `${name(hf)}(${args.join(", ")})`;
      if (!calls.includes(c)) calls.push(c);
      return L.list([L.list([kw('CONST'), L.list([kw('I32')]), (args[0] + 1) >>> 0])]);
    },
  };
  let ok = true;
  const check = (what, c) => { console.log(`W4-HOST ${c ? 'PASS' : 'FAIL'} ${what}`); ok = ok && c; };

  let [st, env] = L.toArray(L.fn('DEMO', 'REGISTER-HOST')(L.fn('DEMO', 'EMPTY-ENV')(), bytesOf('env'), hostSig));
  check(`host module env registered: ${L.show(st)}`, L.show(st) === ':OK');
  [st, env] = L.toArray(L.fn('DEMO', 'LOAD-MODULE')(guest, env));
  check(`guest instantiated with env.inc imported: ${L.show(st)}`, L.show(st) === ':OK');
  const t = Date.now();
  let [r] = L.toArray(L.fn('DEMO', 'INVOKE')(env, bytesOf('f'), L.list([L.list([kw('I32'), 20])]), L.NIL));
  check(`f(20) = ${L.show(r)} (want (2 * (20 + 1)) = 42), ${Date.now() - t} ms`, L.show(r) === '((:CONST (:I32) 42))');
  check(`host saw (distinct calls) ${calls.join(" ")}`, calls.length === 1 && calls[0] === 'env.inc(20)');

  // the default host has no result: no rule applies to the host call, so the
  // run stops there (t7: the final instructions are not values)
  globalThis.DEMOHOST = NONE_DEFAULT;
  [r] = L.toArray(L.fn("DEMO", "INVOKE")(env, bytesOf("f"), L.list([L.list([kw("I32"), 20])]), 100));
  const stuck = L.show(r);
  check(`default host: f(20) stops at the host call (${stuck.slice(0, 40)}...)`, stuck.startsWith("((:FRAME_"));
  process.exit(ok ? 0 : 1);
}
main().catch(e => { console.log("W4-HOST FAIL threw: " + (e && e.stack ? e.stack.split("\n").slice(0, 6).join(" | ") : String(e))); process.exit(1); });
