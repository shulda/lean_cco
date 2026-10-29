# Local runtime restoration — 2026-10-29

The prior scratch environment was absent. It was restored without changing tracked repository files, policy, contracts, source pins, manifest or toolchain. The primary checkout remains clean at main `8b165711491be83a7043dd4d40f818aa17ebcc05`, tree `2499d8a15ad64af2187918c63db9a9e6ba4a6d5f`.

The official Lean 4.34.1 Linux archive downloaded successfully over HTTPS (580432872 bytes). Lean reports release commit `5045d0056413266e57c625dcd7c365b10e377c52`; Lake reports `5.0.0-src+5045d00`. The local proc-self readlink adapter was reconstructed exactly from the durable runtime-imports-20261028 report. It changes only the process executable-path query; the official compiler and checker binaries are unchanged. CI continues to use the official unadapted runtime.

All nine packages were fetched at the exact committed manifest revisions, including Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The actual source closure yielded 131 targeted external Mathlib roots; the pinned cache tool successfully downloaded/decompressed 2219 files. No broad import or full-Mathlib cache request was introduced. Mathlib.Order.Irreducible and Mathlib.Data.Fintype.Card requested by the new B012 work were already included transitively. Package hydration was serialized; packages are shared read-only after hydration.

The recent main CI exposes zero downloadable workflow artifacts. To restore useful project incrementality, one local main baseline build populated the project outputs: 2839 jobs PASS. The complete passive source/byte/import-header guard then passed for all 604 actual olean parts AND all 604 current source modules. A small CCO.TypedRelation build and its warm repeat each passed the 349-job graph. No baseline whole axiom audit was repeated; final package owners retain their mandatory final build, audit and complete guards.

The official axiom-audit tool at v0.1.2, exact `46024e005996495c65ef609368e11ab39c4222e3`, was fetched and built successfully (six jobs). Its binary is available for final owner audits, with only propext, Classical.choice and Quot.sound allowed.

Local paths (reproducible conveniences, not durable binary requirements):

- Environment: `source /workspace/scratch/6b2f11185e14/runtime/env.sh`.
- Compiler: `runtime/lean-4.34.1-linux/bin`.
- Readlink adapter: `runtime/proc_self_compat.so` (C source adjacent).
- Exact shared packages: `runtime/packages`.
- Frozen, validated project output snapshot: `runtime/baseline-build`.
- Snapshot evidence: `runtime/baseline-verified.json`.
- Empty isolated worktree seeding: `python3 runtime/prepare-worktree.py ABSOLUTE_WORKTREE`; the helper refuses existing outputs.
- Existing isolated build directory: when its build is idle, copy `runtime/baseline-build/.` into its own `.lake/build/`, preserving newly created modules. Compile changed sources and use the existing consistency guard; a copied snapshot does not certify a later source state.
- Auditor: `runtime/axiom-audit/.lake/build/bin/axiom-audit`; invoke through the target worktree's `lake env`.

The baseline snapshot is separate from the mutable primary checkout so later integration cannot race with author cache seeding. B012, B014 and their helpers were informed of readiness and separate build ownership. No mathematical batch was claimed or implemented by the runtime restorer.
