# B037 C46 — actual unbounded minimal obstruction family

This stream discharges claim C46 in `formalization/unary_hn/module.json`
against N07 of its proof notes. It does not supply the obstruction bound
assumed by the main Ramsey transfer; it proves that the bound is a separate
substantive assumption.

## Concrete class and strong amalgamation

`CCO.UnaryHN.Native.ObstructionBoundaries.language` has two binary relation
symbols and no functions. `network E` has R exactly on distinct equivalent
pairs and B exactly on inequivalent pairs. `completed` consists of all
finite such networks, with no bound on the number or sizes of classes.

`completed_hereditary` in `Basic.lean` pulls the equivalence relation back along the
actual given full embedding. `network_irreducible` uses positive coverage
of each distinct pair to rule out a proper free split, and yields
`completed_irreducible` for every completed member.

`completed_finiteHereditarySAP` in `StrongAmalgam.lean` is an actual construction,
not a supplied amalgamation callback. For any full common-root span, the
carrier consists of the original root, the left points outside that root,
and the right points outside that root. Thus no distinct nonroot points
are identified. A side equivalence class meeting the root is labelled by
its root quotient class; a class missing the root retains its own side
quotient class and side tag. Equality of labels reflects and preserves
the old equivalence on each complete side. The target equivalence is the
kernel of the common vertex-label map.

`leftEmbedding` and `rightEmbedding` preserve and reflect both actual
colors. `leftPoint_root`/`rightPoint_root` prove commutativity on every
root point, and `point_overlap` proves that every overlap comes from that
root. This includes an empty root and all original side points. The final
theorem is in `CCO.UnaryHN.Native.ObstructionBoundaries` (a duplicated
namespace in the inherited uncommitted draft was corrected).

## Every size, every proper subset, every integer bound

For every natural n at least four, `path n` specifies an R-path through
all n points and a B-edge between its endpoints. `path_no_homomorphism`
uses the R-chain to force equivalent endpoint images, contradicting B.
It needs neither global injectivity nor a protected-piece premise, and
implies `path_no_completion` even for ordinary homomorphism-embedding
completions.

`irreducible_image_linked` in `FreeSplit.lean` applies to every actual irreducible
subobject and every full embedding into the partial source. Combined
with the absence of triangles in the n-cycle of specified pairs, it
proves `path_irreducibles_completed`: all protected pieces are actual
completed class members, not merely completable pieces.

`every_proper_subset_completes` quantifies over every proper subset of
the actual n-point carrier. A missing vertex cuts the R-chain; the
Boolean position label on either side of that cut supplies a completed
equivalence network on the subset's own carrier. The identity map is a
globally injective positive map. Actual completed membership of every
protected piece upgrades its restriction to a full embedding. Therefore
the result is a `HasStrongCompletion`, with no change of source carrier
and no assumption that the whole source map is globally induced.

`path_singleton_hull_completed` explicitly records admissibility of the
actual one-generated closed structures. Finally
`no_uniform_obstruction_bound (N : ℤ)` uses n = N.toNat + 4 and the strong
completion of every proper induced subset to refute
`RestrictedObstruction completed N`. Its integer quantifier includes
negative bounds. No fixed small example replaces the unbounded family.

## Authorship and validation

The base concrete class/path proofs were written by the earlier
`/root/b036_counterexample` actor. The earlier `/root/ramsey16` takeover
implemented the protected-piece, proper-subset and integer-bound proofs
and the uncommitted point-pushout/amalgam draft. `/root/b037_sap` retained
that draft, corrected its final namespace, compiled the complete stream,
and committed the genuine strong amalgamation proof as
`e68ff7418c7108f8e4d96d724c608a23d1feb5ee`.

The exact pinned Lean 4.34.1 narrow build passed:

```sh
lake build CCO.UnaryHN.ObstructionBoundaries.StrongAmalgam \
  CCO.UnaryHN.ObstructionBoundaries.Unbounded
```

It completed successfully with 1020 jobs. This is stream-level compilation;
whole-batch import closure, exact-head CI, transitive axiom audit and the
actual independent non-author review remain the B037 owner's integration
gates. No whole-project pipeline or audit was duplicated by this stream.
