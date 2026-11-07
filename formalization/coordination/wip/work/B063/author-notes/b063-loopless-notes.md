# B063 C01–C08 implementation helper checkpoint

Actual implementation helper `/root/b053_resume/b063_loopless`.
Owned source: `CCO/AutomaticEPCore/TerminalLoopless.lean` only, in work-b063.
Final source SHA256: `92c347c49ddd2741780d039116d11e7fb35084bcedac9cfcd4beead714febe68`.
Pinned Lean4.34.1 direct compilation to private temporary output passes,
with no diagnostics; no root imports, report, commit, push, or coordination
record was written by this helper.

## Exact interface

All names are under `CCO.AutomaticEPCore`, with the actual original
`CCO.ParityHasse.Original.AtomicSource S`, fixed sort `i`, actual
`HomogeneousSource S G` and its given action. No AP, SAP, CCO, source
infinitude, full-phase provider or presumed hidden result is an input.

- `FullCoverTerminal S i` quantifies over EVERY FULL ColourEq cover E⋖F
  and EVERY actual containing-class anchor x, requiring the actual
  `RelativeClass E.val F.val x` to be Infinite (Top covers included).
- `terminal_full_interval_infinite S terminal E F hEF x` proves every
  strict FULL interval has infinite actual relative class, by an actual
  cover and its injective class-inclusion map.
- `invariant_graph_serial`: nonempty actual colour-invariant graph on
  the same sort is serial by actual old transitivity.
- `invariantGraphEvenEq` / `invariantGraphConnectivityEq`: actual FULL
  colour-invariant even-walk / all-walk setoids, with the zero walk.
- `invariant_graph_positive_parity_stabilization`: one positive finite
  actual-palette threshold represents both parity relations; no exactness
  assumption, named atomicity or countability assumption is used.
- `invariant_bipartite_parity_index_two`: a nonempty invariant bipartite
  graph gives precisely TWO even classes in each connected class.
- `invariant_bipartite_parity_cover`: these are a strict FULL cover.
- `terminal_invariant_bipartite_graph_empty S H terminal graph invariant
  bipartite : ∀ x y, ¬graph.Adj x y` is the principal result.
- `terminal_bipartite_restriction_empty S H terminal oldGraph realPoint
  invariant bipartite` applies it to the literal pullback of an original
  bipartite graph along `realPoint : X i → A`. This handles a restriction
  that could be a union of current atomic names, without assuming one.
- `terminal_atom_not_bipartite S H terminal c` specializes to every
  actual occurring same-sort atom, using its actual occurrence witness.
- `equality_support_iff label realized s t`: support of real equality
  is literal type equality, for realized labels.
- `diversity_support_diagonal_iff graph label t`: a diversity support loop
  has two DISTINCT same-type real witnesses, never a real equality edge.

## C01–C08 source map and outstanding receiving seam

C01 is the actual FULL strict-interval injection argument. C02 is seriality
of the genuine current invariant graph. C03 is its two actual invariant
setoids and finite-palette stabilization. C04 is the explicit quotient with
exactly two actual parity classes and the full-cover theorem. C05/C06 are
the terminal contradiction and the literal original-graph restriction
wrapper. C07 keeps real equality support / diversity loops distinct.
C08's source-facing terminal-type theorem still needs the parent to apply
the restriction wrapper to the ACTUAL final homogeneous source, its proven
FULL terminality and the literal original-atom edge restriction invariance.
No assumed final source/tower provider was added here. These helper proofs
are not by themselves a discharge of that actual B062 source instance.

## Dependency firewall

Imports are exactly original `ParitySeed`, specific Mathlib bipartite and
Coloring.Constructions modules. The existing parity infrastructure is used
only for finite-colour actual relation powers, the explicit even/connectivity
setoids and actual full relative-index maps. The proofs never invoke the
later source Hasse theorem, source HOM-CCO theorem, a quotient/full-marking
provider, original/hidden SAP, I01–I06 or I08. Logical graph bipartiteness
is the premise of the no-odd-walk proof; it is not inferred from CCO.
The parent still owns whole-root imports, source application, compilation
of consumers and the transitive axiom audit before any completion claim.
