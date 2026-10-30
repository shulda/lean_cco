# B039 C49 — the missing named forced factor

Actual contributor: `/root/b039_fresh/examples`. Source remains
`490c3f36d85db5a0b3ced0598e6c431825254ec5`, in particular the first model
of `formalization/unary_fresh_frames/PROOF_NOTES.md`, N09/C49. This report
concerns the first of the two independently implemented infinite models.
The two-cover model is owned by `/root/b039_fresh/sap`.

## Actual model and original language

`CCO.UnaryFreshFrames.Examples.Matching.originalModel` has the countable
carrier `(ℕ × ℕ) ⊕ (ℕ ⊕ ℕ)`. Its three named sorts are the real sort
`M=ℕ×ℕ`, quotient sort `Q=ℕ`, and matching sort `S=ℕ`. Its ONLY named
functions are `p(q,n)=q` into Q and `τ(q,n)=s_q` into S. Its ONLY named
relation is the typed Q–S matching. Both functions are total on M and
canonically extended by the identity off M for the primitive presentation.
The signature is genuinely finite; no function from Q to S or S to Q is
present. There are no constants.

The intermediate `model` adds typed root-equality relations to simplify
the extension proof. This does not buy a stronger homogeneity assumption:

- `root_iff_basic` gives an explicit quantifier-free formula using ONLY
  named p/τ, equality and the one original matching relation.
- `originalEmbedding_root_iff` and `expandedEmbedding` prove that EVERY
  induced embedding of an ORIGINAL finite closed piece preserves and
  reflects those auxiliary relations. This uses actual closure, function
  preservation and injectivity, including orphan Q/S vertices.
- `original_homogeneous` therefore extends ALL original closed partial
  isomorphisms by actual full named automorphisms.
- `automorphisms_eq` proves literal equality of the original and expanded
  full automorphism subgroups. `original_closure_eq` proves equality of
  their actual unary closures.

## Constructed properties and scope

All names below have prefix `CCO.UnaryFreshFrames.Examples.Matching`.

| Obligation | Actual declaration and proof |
|---|---|
| Countable, finite actual named language | `original_countable`, `original_finite_language` |
| Full finite-closed homogeneity | `original_homogeneous`; explicit root permutations and independent infinite-fibre permutations, constructed by `extend_equal_kernels` |
| Finite closure | `original_locallyFinite`; each real singleton has exactly its real point, p-value and τ-value, while Q/S singleton closures are singletons |
| Actual real transitivity | `original_real_transitive`, explicit root and fibre swaps |
| Full-Aut real-base orbit infinitude | `original_real_base_orbits`, for EVERY finite real D and EVERY point outside its actual closure; explicit fresh root/coordinate swaps exclude any finite candidate orbit. `real_base_acl_eq` and `real_base_dcl_eq` prove the corresponding actual real-base closure equalities |
| Actual named quotient and term | `projectionTerm`, `matchingTerm`, their literal value lemmas, `projection_onto_noninjective`, and `all_hidden_named_representations` (both hidden sorts, each with infinite real fibres) |
| Forced value but no named factor | `forced_on_actual_projection_fibres`, `original_no_named_factor` |
| Set/definable factor really exists | `unique_matching_partner`, using the original one matching relation |
| Full-Aut definability outside closure | `original_definable_off_closure`; the matching partner is fixed by EVERY full automorphism over its quotient point, but is absent from the actual singleton term closure |
| ALL unforced actual term indices infinite | `all_unforced_indices_infinite` and `all_unforced_matching_indices_infinite`, for both existing named quotient maps; actual term normal forms are proved, not supplied as a finite-term oracle |
| Actual hereditary SAP failure | `original_not_ageSAP`, contradicting the internally proved SAP-to-full-Aut-orbit criterion over an orphan hidden singleton |

Thus the first model isolates the NAMED-factor failure: full real-base
orbit infinitude and the infinite-index clause for all unforced existing
terms are retained. A merely set-theoretic/definable factor does not
provide an actual unary named term. These are unbounded infinite-model
proofs, not finite-reservoir diagnostics.

## Validation and handoff

The seven new Lean modules contain 763 lines. The final targeted build
of `CCO.UnaryFreshFrames.Examples.MatchingIndex` passed **1340 jobs**,
with no new-file warnings after the final cleanup. No whole-project build,
test suite or axiom audit was duplicated by this helper. Root/owner retain
the one final receiving pipeline and the actual nonauthor review.

Final mathematical source checkpoint: `64c919ddc0f0f570be41cbdd2441f62f400f3fd7`.
Initial coherent source checkpoints, in order: `9129e7f6f63d2fbd5501a1013f6503772a2f3ee0`,
`89fa5ea68819b05e3384af448fc82367213d84de`,
`98134b2102bad86dc0ecd607142274e56ca5e311`, and
`1f7179333c5c3d786ce91a70b46b996a3e67bbe4`.
Earlier primitive cherry-picks are prerequisites already present in the
owner and must not be replayed as new implementation. No accepted source,
API, toolchain, manifest, contract, BOARD or STATE was changed.
