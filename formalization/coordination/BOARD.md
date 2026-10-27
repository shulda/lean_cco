# Project allocation — generated from BOARD.json

Revision 1; phase **READY**; public repository: **shulda/lean_cco**.

| Package | Owner | State | Prerequisites | Mathematical scope |
|---|---|---|---|---|
| [B001: Shared API and SAP geometry](../../formalization/coordination/packages/B001_SHARED_API.md) | 1 | ASSIGNED | — | Representations; RAW elementary calculus; actual quotient pullbacks; strong SAP geometry and a consumer |
| [B002: RAW exact geometry and lifting](../../formalization/coordination/packages/PLANNED.md) | — | PLANNED | B001 | RAW C06–C28, all remaining current RAW claims |
| [B003: STRONG exact calculus and PC](../../formalization/coordination/packages/PLANNED.md) | — | PLANNED | B001 | STRONG C06–C13 plus independent AP+CCO triangle fullness |
| [B004: Gates, NR2 and selectors](../../formalization/coordination/packages/PLANNED.md) | — | PLANNED | B003 | STRONG C14–C27; exact calculus prerequisite, no PC fixed-point theorem dependency |
| [B005: Positive SIR and direct relative example](../../formalization/coordination/packages/PLANNED.md) | — | PLANNED | B003, B004 | SIR C01–C14 and C20–C25; constructor/instance and direct model kept separate |
| [B006: Parity/Hasse and finite-global obstruction](../../formalization/coordination/packages/PLANNED.md) | — | PLANNED | B001 | SIR C15–C19 plus unexpanded parity/Hasse; not yet a complete contract |

Only B001 has a complete launch contract. Later rows are planning envelopes.
Package edges schedule work; consult the module claim DAG for actual theorem dependencies.
No Lean export is certified by this allocation table.
