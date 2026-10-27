# Shared decisions

This ledger records decisions that another project must be able to discover.
Routine local implementation details belong in the numbered project report.

| ID | Decision | State |
|---|---|---|
| D001 | One public repository, one Lean/Lake project, numbered equal-status receiving projects; this preparation project owns mathematical allocation. | Agreed with author, 27 October 2026. |
| D002 | Start only Project 1 with B001; test proofs, a consumer and the reporting/integration round trip before adding Project 2. | Agreed with author. |
| D003 | Packages cover substantial connected mathematics; module `T` tasks and individual lemmas are internal milestones. | Agreed with author. |
| D004 | Workers notify the author on completion/blocker/scope change; the author brings the matter back to the preparation project. | Agreed with author. |
| D005 | RAW represented composition and STRONG three-distinct-vertex composition have separate types/operations and explicit conversion lemmas. | Mathematical requirement of the pinned source. |
| D006 | Public destination is `shulda/lean_cco`. Initial Lean/mathlib release is 4.34.1, mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, with a locked transitive manifest. | Coordinator supplies the initial public scaffold; live CI status is in Actions. |
| D007 | One CI job per main push/PR update; complete matching Mathlib cache, toolchain cache, no whole-workspace cache; transitive axiom audit on CCO. | Adapted from the existing working Lean repositories; see public `BOOTSTRAP.md`. |

At B001 submission add the actual carrier/palette/diagram/action choices,
Lean/mathlib commits, public file layout and conversion API, with links to
the implementing commit. Future shared changes receive a new decision row;
preserve the prior decision and identify its replacement.
