# Instruction typing behavioural cases, against V8 (before the sequencer)

- Milestone: M6 (item "Behavioural cases")
- Date: 2026-11-15
- Repo commit: 5c78b6d plus this note's commit
- Status: final for the book; the wrong cases wait for the sequencer (M6 item 3)
- Feeds wasm3 plan: §5 M6 (exit: behavioural cases N of M)

## Summary

`tests/sem-3.0/t6-instr-typing-3.0.lisp` (in `make check-3.0`) runs the
generated `EXPR_OK` (check variant) on 24 function bodies. The expected
answer of each is V8's `WebAssembly.validate` on the same body in a
module (`typing-oracle-3.0.lsp`, made by `tests/oracle/gen-typing-oracle.mjs`).
**16 of 24 agree with V8.** All 8 wrong ones are valid bodies that
the generated typing rejects; no invalid body is accepted:

| Case | V8 | generated | Why (M6 strategy note) |
|---|---|---|---|
| subsumption at block end | valid | rejected | `Instrs_ok/sub` is dropped; `Instr_ok/block` compares `t_2*` for equality |
| subsumption at function end | valid | rejected | no subsumption |
| subsumption at a call | valid | rejected | no subsumption |
| initialized non-defaultable local | valid | rejected | `x*` through the output variant |
| dead code after `unreachable` | valid | rejected | the output variant drops the stack-polymorphic rules |
| dead code after `br` | valid | rejected | same |
| dead code after `throw` | valid | rejected | same |
| `br` with a value | valid | rejected | same (`br` in a block with a result) |

The 16 right ones include every rejected case: an operand missing, an
empty body with a result, two results left, no downward subsumption, a
call with a wrong operand, an uninitialized non-defaultable local, dead
code with a wrong type, `return` with a wrong type.

## How the cases are made

Each case is a body in WAT and the same body in the generated encoding.
The WAT is wrapped in a module with two callees (`$f : [(ref null i31)]
-> []`, `$g : [i64] -> []`) and a tag (`$e`). The reference interpreter
turns it into binary unchecked (`wasm -u -d`), because wabt's text parser
lacks the GC heap types; then V8 decides. The ACL2 context mirrors the
module: functions, tag, labels and return equal to the result type, and
locals for the parameters (set) and the declared locals (set if
defaultable). The book also checks every encoding with the generated
recognizers (`context-p`, `instr-p`). That check caught my first local
type encoding.

## Data

The book and `typing-oracle-3.0.lsp` (V8's verdicts); the book's output
in `t6-instr-typing-3.0.cert.out` after `make check-3.0`.
