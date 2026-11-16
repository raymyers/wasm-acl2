Is it possible to run the slide deck on my ACl2 WASM3 somehow? Like to run WASM PDF viewer in it or something?

---

What if we didn't do it in the browser version?

---

Could we make a faster engine and prove it consistent with semantics?

---

gitignore the talk figure stuff for now and make a new plan in plan folder for a verified wasm engine like you say.

---

Cool. So is there a 1.0 finish that will give me an actual displaying PDF I can present from?

---

This is a pdf renderer for wasm. https://www.npmjs.com/package/mupdf Can we run it?

---

1. you can fork the code (gh to make a fork in my org) and make the exceptions 3.0 compatible. 2. Then make a 3.0 ready engine. 3. Can you fix this?

---

Will we be able to run the code out of browser? Like ACL2 having connection to sbcl that displays?

---

Let's make this the litmus test for plan/wasm-engine working so you can update the plan to make that the demo milestones or however you want to clarify it. End of day, if I can view a PDF with the engine and it certifies vs the semantics, I'm happy

---

Are we now ready to headless execute, set up for success?

---

How close are we to being able to view pdf, even if there are incomplete proofs?

---

OK what if we pivoted to another way to demo presentation slides with it? Is there something that's less of a stretch to run than a pdf viewer?

---

Yes. Think maybe something like this? https://tools.suckless.org/sent/

---

Kill the shell if it's part of the old pdf stuff. Then let's think about how to get that size better

---

3 I think. We need to optimize the memory and arithmetic time, that was the point of making this engine, so that we'd have a fast version that matched the semantics

---

## Course corrections (2026-11-16)

What the prompts above changed in the plan:

1. **MuPDF is too big for now; an earlier demo comes first (D10, L0, E12).**
   Viewing a PDF needed a fast machine, a loader for a 10 MB module and
   host functions, and the number of instructions per page was unknown. The
   new first demo is the talk's slides, written in the plain-text format of
   suckless `sent`, rendered by a small renderer of our own compiled to wasm
   (no imports, one page of memory, integer instructions only) and run on
   the engine, with pixels identical to V8. MuPDF stays the litmus test.
   L0 was met the same day: 7 of 7 slides identical to V8.
2. **The MuPDF decode was stopped.** The full module's run through the
   generated decoder was stopped after 434 CPU minutes; the small build's
   result (decoder and `Module_ok` pass) stands for E1 item 5.
3. **Speed is the point of the engine: E7 now.** The slides are small
   (320 x 180, one bit per pixel) because memory is a list in the E6
   machine. Rather than enlarging them on the slow machine, the next work
   is the fast machine: memory in an array, then the cost of arithmetic and
   dispatch, with a refinement theorem against the list machine, so that
   the fast version matches the semantics.
