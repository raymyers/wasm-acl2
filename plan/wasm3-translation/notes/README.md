# WASM 3.0 translation notes

Findings and designs from the milestones of [../plan.md](../plan.md).
Conventions (header, layout, when to write a note, session protocol) are
those of the prep notes:
[../../wasm3-translation-prep/notes/README.md](../../wasm3-translation-prep/notes/README.md).
Raw data goes under `data/<name>/` with the script that made it.

## Index

| Note | Milestone | Status | What it holds |
|---|---|---|---|
| [M5-mode-table](M5-mode-table.md) | M5 item 1 | final (design and core); hand-over list open | Mode table design; what is implemented; measured results; `Heaptype_sub/trans` is not admissible |
| [M6-instruction-typing-strategy](M6-instruction-typing-strategy.md) | M6 item 1 | final; the user chose option C (2026-11-14) | First run of generated 3.0 typing (13 of 23 cases right, 18 after the fix); why subsumption has no mechanical reading; proposer and checker recommended |
