# Lean/CI bootstrap and local runbook

The coordinator prepared this infrastructure before assigning mathematical
implementation to Project 1. The only Lean theorem is a group-action smoke
check. No RAW/STRONG claim or other source-paper result is formalized yet.

## Pins and build

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib release: `v4.34.1`, commit
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- The committed Lake manifest locks all transitive package revisions.
- Library and initial namespace: `CCO`; root import file: `CCO.lean`.

After installing elan, from a clean checkout:

```bash
lake exe cache get
lake build
python3 -m unittest discover -s tools -p 'test_*.py' -q
python3 tools/check_formalization_coordination.py --check --require-launch
```

CI additionally validates all three mathematical modules and their finite
controls, and runs lean-action's transitive axiom audit on namespace `CCO`.
Its only allowed axioms are `propext`, `Classical.choice`, `Quot.sound`.
Add every intended public Lean module to the import closure of `CCO.lean`;
the default build and audit must reach it. B001 must check the actual export
map and complete module coverage before reporting completion.

## Workflow policy

One Linux job runs on default-branch pushes, PR updates and explicit dispatch.
Feature-branch pushes alone do not duplicate the PR job. Concurrency is per
PR or branch ref; newer work cancels obsolete runs for the same ref only.
Toolchains are cached. lean-action downloads the full matching Mathlib cache;
whole-workspace `.lake` caching is disabled.

This follows the working `lean_eppa_semigeneric`/`lean_all_those_eppa_classes`
policy. In the adjacent projects partial cache downloads had left large
amounts of Mathlib to compile, while multi-gigabyte `.lake` archives were
expensive to restore/save. Other repositories were read for reference only.

When investigating a slow or failed run, inspect the exact job/step logs.
Determine whether it is downloading a cache, rebuilding missing dependencies,
building the project or auditing axioms before changing cache policy. Do not
blindly rerun long jobs or upgrade the shared toolchain.

The full `HANDOFF_MANIFEST.json` describes the launch snapshot, not a ban on
legitimate later report/board/README changes. Ongoing CI validates pinned
mathematical sources and allocation metadata without requiring those mutable
files to retain their initial hashes.
