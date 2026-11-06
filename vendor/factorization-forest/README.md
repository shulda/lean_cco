# Finite factorization forest provider — isolated CCO compatibility preparation

This directory contains Re'em Melamed-Katz's finite factorization-forest
formalization from `ReemMelamed/algebraic-automata` at exact commit
`0acb244aaa913c32eeeff48e939cb5df469a3f70`, ported to the receiving
Lean 4.34.1 / Mathlib v4.34.1 environment. It is advance dependency
preparation: it is not a claimed or completed B058 batch, an accepted CCO
dependency, or the concrete source adapter for the typed semigroup.
The parent project's configuration and toolchain are unchanged.

The narrow import is `AlgebraicAutomata.FactorizationForest.Tree`.
`factorization_forest_classical_bound` preserves the exact input word and
returns a Ramsey tree of height at most `3 * Fintype.card S - 1` for an
arbitrary nonempty finite semigroup. Multiplicativity is required only for
concatenations of nonempty words; no monoid or identity element is assumed.

See `PORT_REPORT.md` for the precise checks and remaining receiving duties,
`PROVENANCE.json` for original and ported source fingerprints,
`INVENTORY.md` for the independently inspected source/license/import
inventory, and `compatibility.patch` for all source modifications (apply with
`git apply --unidiff-zero`).
Original upstream configuration and the complete transitive manifest are
retained under `upstream/`; the receiving manifest is at this package root.

The original formalization belongs to Re'em Melamed-Katz. Every imported
source keeps its copyright, Apache-2.0 notice and author header. The full
license is `LICENSE`. Each changed source also identifies the CCO
compatibility port. No upstream NOTICE exists at the exact chosen pin.
Any separately redistributed provider build/cache must include this license
and applicable attribution/modification notices with its provenance.

Ordinary standalone dependency resolution/build uses this package's
`lakefile.toml`, `lake-manifest.json` and `lean-toolchain`. A read-only
shared-dependency replay is available without changing any existing build:

```sh
python3 tools/build_readonly.py \
  --dependency-root /absolute/path/to/exact/receiving/.lake/packages \
  --lean /absolute/path/to/lean-4.34.1/bin/lean \
  --audit /absolute/path/to/receiving/axiom-audit
```

The helper checks all nine receiving dependency Git pins and all fourteen
ported source hashes, compiles the complete finite closure and the small
consumer using the exact options in this package's `lakefile.toml`, and
optionally runs the protocol's transitive axiom audit. It writes only this
package's private `.lake` outputs. No upstream Lean 4.35 `.olean` is reused.
The consumer is `Tests/Consumer.lean`; it contains no CCO-specific adapter.
