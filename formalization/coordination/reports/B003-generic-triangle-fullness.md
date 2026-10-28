# B003 generic triangle-fullness source export

Implementation: `835e21f5a564a8f6eaf32ba387237ca6dd88192e`, branch
`work/B003-triangle`, preserving the earlier actual-age proof and original
B003 history. This follow-up report changes no proof. The independent
non-author reviewer received this exact implementation SHA. No remote CI or
review approval is asserted by this report, and B003 is not SUBMITTED.

Pinned source: `490c3f36d85db5a0b3ced0598e6c431825254ec5`,
`sections/triangle_fullness.tex`, `lem:cco-triangle-fullness`.
This generic export closes the scope limitation of the earlier actual-age
specialization, which remains separately available and accurately reported
in `B003-triangle-fullness.md`.

## Exact generic interfaces and source quantifiers

`CCO/StrongExact/FiniteAtomicClass.lean` defines:

- `Model S`: any finite **complete** typed atomic structure on canonical
  vertices `Fin n`, over the original `S.Atom` palette and converse. Its
  diagram is purely symbolic: it is not required to be realizable in S.
  A K-model may have triangles absent from S's actual colouring.
- `Model.colour`: the full ordered tagged atom fingerprint, with `none`
  precisely on the formal logical diagonal and the displayed diversity
  atom elsewhere. `colour_eq_fullColour` verifies agreement with the
  complete-diagram full-colour API.
- `Embedding A B`: an injective finite vertex map preserving sorts and
  **every** full ordered pair colour, including the diagonal. This is
  the ordinary induced embedding of complete named-atom structures.
- `Hom D B`: a map from a finite **partial** diagram, preserving all
  vertex sorts and exactly its specified diversity edges. It may identify
  non-adjacent vertices; it imposes no condition on unspecified pairs.
- `Hereditary K`: membership descends along these induced embeddings.
  `AP K`: for K-members C,A,B and two complete-base embeddings, a K-target
  T and factor embeddings making the ordinary square commute. It asserts
  no exact overlap or cross-factor freshness.
- `CycleHomInto C B`: preserves precisely the cyclic edges and all vertex
  sorts. Chords/non-adjacent pairs need not be preserved.
- `SemanticCCO K`: if each specified simple cycle of a finite partial
  diagram has a homomorphism into **some K-member** (different targets
  allowed for different cycles), the whole diagram has a homomorphism
  into some K-member. Targets are not original-source points and no
  original-source CCO instance is substituted.
- `SmallSubmodels K A`: for every finite induced enumeration
  `e : Fin n ↪ Fin A.size` with `n ≤ 3`, `K (A.pullback e)`.
  It includes zero, one and two vertices. `colour_pullback` preserves the
  exact entire original colouring. Explicit reindex embeddings in both
  directions and `Hereditary.pullback_reindex_iff` prove invariance under
  finite enumeration changes. Isomorphism invariance follows from heredity;
  it is not a new class assumption or a representation/limit provider.

All finite complete models are represented by their finite canonical vertex
sets, as customary up to finite enumeration. K is arbitrary on these models;
there is no relation assumed between K and the actual age of S. The accepted
`AtomicSource` is reused only for its standing typed palette/involution.
No source/carrier realization of K, homogeneous limit or Fraisse provider
appears in the generic theorem.

## Proof and exact export

`CCO/StrongExact/GenericTriangleFullness.lean` follows the source proof:

1. `pairIndex`/`tripleIndex` retain literal input vertices and all their
   actual input colours. `pairEmbeddingFromColour` verifies the complete
   two-point base, including reversal and logical diagonal.
2. `fanRealized` realizes each finite root-chord/cycle-edge prefix in an
   **actual member of K**. Base and successive triangles are the input's
   literal induced Fin2/Fin3 K-members supplied by `SmallSubmodels`.
   Ordinary class AP glues them over the complete edge. Prefix vertices
   may move and the next vertex may coincide with an earlier non-neighbour.
   No SAP or fixed-root original-source homogeneity is used.
3. `cycleHomInto_of_AP` reads the whole finite cycle, including its closing
   edge and typed converses, into that K-target. It gives the actual
   class-valued cycle predicate, not an abstract unproved provider.
4. `triangleFullness` applies class-semantic CCO to the complete input.
   `Hom.toEmbedding` proves injectivity from each distinct input pair's
   diversity colour, then proves full induced colour preservation.
   Heredity of K yields **K A**.

Printed core signature:

```lean
triangleFullness
  (K : Model S → Prop)
  (hereditary : Hereditary K)
  (ap : AP K)
  (cco : SemanticCCO.{u,v,w,0} K)
  (A : Model S)
  (small : SmallSubmodels K A) : K A
```

The semantic-CCO universe is the canonical finite-vertex universe; the sort
and palette universes remain arbitrary. The core has no original-age,
original-source realization, H, SAP, NR2, triangle-completion or limit
hypothesis. It is not a partial triangle-consistency completion theorem.
The earlier actual-age theorem is a distinct useful source wrapper, not the
generic theorem's assumed provider.

## Validation and remaining limits

Exact pinned Lean/Lake 4.34.1 and Mathlib manifest revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`, unchanged.
Both generic modules were compiled, then the updated public `CCO.lean` root
was compiled. The root transitive standard allowlist audit succeeded for
**1,659 CCO declarations**, zero violations, only `propext`,
`Classical.choice`, `Quot.sound`. Direct `#print` confirms the displayed
signature and `#print axioms` for the generic theorem and reindex-invariance
consumer reports exactly those three axioms.

As in the earlier actual-age checkpoint, these checks rebuilt the new modules
and root in an isolated worktree against copied B003+PR5-compatible dependency
artifacts. They do not claim a fresh full Lake rebuild of the old-import f140
source tree or validate the later combined PR4 head. The coordinator must
run the full build, exact-head CI and root audit on that integration and
obtain substantive independent review for the current precise head.

Other B003 C07/provider and PC/completion obligations remain outside this
export. No source pin, mathematical contract, accepted shared signature,
toolchain or axiom allowlist was changed.
