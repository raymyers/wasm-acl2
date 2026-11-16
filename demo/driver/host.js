// demo/driver/host.js: the default JS host of the glue's HOST-CALL (W4 item
// 2; driver/glue.lisp). call(hf, vals, none): hf is the host function's
// (modname field) as Lisp lists of character codes, vals the arguments as
// Lisp values ((:CONST (:I32) n) ...). It returns a Lisp list of result
// values, or NONE when the host has no result (the call does not step, as
// with the books' %HOSTCALL-NONE). A page or test replaces
// globalThis.DEMOHOST before invoking.
(function () {
  'use strict';
  if (!globalThis.DEMOHOST) globalThis.DEMOHOST = { call: (hf, vals, none) => none };
})();
