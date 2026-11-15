We have execute plan/wasm3-translation/plan.md and have ACL2 semantics for WASM3. This seems to work for executing WASM3 programs but only in an ACL2 environment. Let's make it run in browser in jscl (https://github.com/jscl-project/jscl). This should be done without interfering with the ACL2 version, we should extract with a build process and add shims, or something reasonable but not duplicate the exiting code that will remain source of truth. Make a new plan and step file in plan/wasm3-demo/

---

Good. Is it possible to have a semantics rule stepper view? Line-by-line execution of the wasm?

---

Is this now ready to headless implement?
