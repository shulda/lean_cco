# B006 C01–C05: actual finite sparse labelled graphs

Source-complete proof checkpoint: `a10e48180ec6ddbaf686cdc0bd33ca80e8a39251`,
on accepted main `647b1b76cc075dce477974b74293eb9370ff9b5d`.
Source pin remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`;
`sections/sparse_labelled_graphs.tex` has the contracted blob
`c7db0b7169dd8ff4dcd5642469ac8fa42c2ef530`.

| Claim | Source proof and actual exported result |
|---|---|
| C01 | `monochromaticPairs` is the actual finite set of unordered DISTINCT monochromatic vertex pairs; `monochromatic_pair_count_identity` proves `2N+n=Σ n_d²`, including empty classes. `actual_monochromatic_pair_lower_bound` plus `mean_lower_bound` gives the source `N≥n²/(4q)` and `μ≥cn/(4rq)`. |
| C02 | `FiniteLaw` is an explicit finite real-weight distribution. `productLaw` normalizes a genuine finite independent product. `product_expect` evaluates its Laplace transform by a finite product of sums; `bernoulli_laplace`, `FiniteLaw.markov`, `FiniteLaw.exponential_lower_tail`, `bernoulli_lower_tail` and `requested_lower_tail` prove the source estimate directly. No Chernoff/concentration or graph-existence theorem is imported. |
| C03 | `labelWeight` and `labelLaw` give no edge with probability `1−c/n`, each requested positive label with probability `c/(nr)`. `cycle_probability` is exactly `(c/n)^ℓ`. `cycleCode_card_le` and `expect_cycleMass_le` give the precise `B=Σ c^ℓ/(2ℓ)` expectation bound, with zero codes when ℓ exceeds the vertex count. `exists_source_sparse_size` gives all explicit Archimedean bounds for `c=128rq log(q+1)`; `exists_good_outcome` uses the two finite union bounds and elementary Markov, without independence of the two global events. Its honest intermediate expectation hypothesis is DISCHARGED in the source theorem by `expect_cycleMass_le`. |
| C04 | `CycleCode V ℓ = ZMod ℓ ↪ V`. Exact edge-cardinality and injectivity of the dihedral family prove that deleting one witnessed short-cycle edge destroys at least `2ℓ` oriented codes. The normalized cycle potential therefore decreases by at least one. `delete_short_cycles` is a proved finite greedy induction with actual erased-edge budget. `bounded_deletion_retains` and `labelledGraph_of_retained_requests` retain the full q-colour/r-label conclusion, with actual labels on a finite simple graph. |
| C05 | `sparse_labelled_graph_exists hq hr g` proves `Nonempty (SparseLabelledGraph q r g)` for every positive q,r and every natural g. `high_girth_chromatic_exists hq g` is the actual r=1 consumer. `connected_high_girth_chromatic_exists hq g` gives the finite connected graph consumed by original orbital parity. The supplied `ConnectedExtraction` proof only claims preservation for r=1, not the full labelled property. |

All declarations live in `CCO.ParityHasse.Sparse`. The concrete witness
`SparseLabelledGraph q r g` has a finite ordinal vertex set, an actual
`SimpleGraph`, an unordered-pair label function with values in `Fin r`,
no injective cyclic sequence of any length from 3 through g, and:
for EVERY q-colouring there is ONE colour having a monochromatic edge of
EVERY positive label. `NoShortCycles` uses the accepted literal
`CCO.cyclicNext` on `Fin ℓ`. The independent ZMod coding is connected to
that literal predicate by a proved finite-index equivalence.

The g=0,1,2 cases are obtained from max(g,3). The q=r=1 cases require no
exception. All theorems are finite combinatorics and ordinary real analysis;
no SAP, CCO, homogeneity, countability or pre-assumed sparse-graph provider
appears in their source-facing premises. Atomic equality of the original
model plays no part in these finite graph results.

Implementation authors: `/root/b006_parity/sparse_graphs` (finite probability,
label law, exact cycle expectation and full source assembly),
`/root/b006_parity/sparse_graphs/numeric_bounds` (finite counting, numerical
bounds, cyclic-code/deletion and good-outcome proofs), and `/root/b006_sir`
(actual connected-component extraction).

Validation: changed modules and the complete `Sparse.Existence` dependency
target compile on the pinned Lean/Lake and manifest (`2006` replay/build jobs).
No full-root build, independent batch approval or official whole-batch audit
is asserted by this report; those are the B006 owner's final integration
checks. No production `sorry`, new axiom, Erdos/Chernoff black-box axiom or
source contract change was introduced. All 15 new public Sparse modules must
be included in the final additive `CCO.lean` import union by the batch owner.
