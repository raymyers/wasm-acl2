# Engine notes

Findings from the milestones of [../plan.md](../plan.md). Conventions
(layout, note header, session protocol) are those of
[the prep notes](../../wasm3-translation-prep/notes/README.md), with
milestone names `E<k>` and the header field "Feeds engine plan".

**Rule**: if a finding is not in a note here (or in `../plan.md`), it does
not exist.

## Index

| Note | Milestone | Status | One line |
|---|---|---|---|
| [E1-mupdf-target](E1-mupdf-target.md) | E1 | draft | The published MuPDF module uses legacy exceptions; fork `raymyers/mupdf`, branch `wasm3-exceptions`, switches the build to the 3.0 encoding; rebuilt module renders the same pixels in V8 |
