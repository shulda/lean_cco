# CCO formalization

Read `formalization/coordination/PROTOCOL.md` and the current policy on `main`
before writing. Live package claims and acceptance are only in
`coordination:formalization/coordination/STATE.json`. Keep the pinned source,
actual hypotheses and accepted APIs; a conditional provider is unfinished
until its source instance is proved. Preserve the exact-head build and the
transitive axiom audit.

## Imports and build time

- Import the specific Mathlib modules required by the file. Do not add
  `import Mathlib` or `import Mathlib.Tactic` to production Lean modules.
  Import an individual tactic module when needed; core Lean tactics may use
  their Lean module. An unavoidable broader import requires a concrete
  reason recorded in the PR and source map.
- Put a missing import in the file that uses it. Do not enlarge a shared
  foundation module merely to supply unrelated downstream definitions or
  tactics. Do not import `CCO` from an internal `CCO/` module.
- Verify import changes by compiling their complete project consumers and
  any affected active batch branches. Green CI before an import change does
  not validate the changed head.
- When usable, keep a local incremental Lean/Lake build with the repository's
  exact toolchain and manifest. Publish coherent checkpoints; continue other
  independent work while CI runs. One publisher owns each PR branch, and
  concurrent writers use separate worktrees/build directories or disjoint
  files with one build owner.
- Targeted Mathlib cache downloads must include the actual external import
  roots and their transitive dependencies. In the pinned cache implementation,
  `cache get CCO.lean` does not discover arbitrary internal CCO import edges.
  Narrow imports before narrowing cache downloads. Keep the axiom audit.

Existing WIP branches may contain older broad imports. Remove them as part
of their tested integration; this file does not certify those branches.
