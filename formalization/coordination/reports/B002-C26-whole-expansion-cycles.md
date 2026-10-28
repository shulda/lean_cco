# B002 C26 — literal whole-path classification of actual quotient expansion cycles

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
The checked original `sections/exact_foundations/03_joint_exact_sort_lifting.tex`
has Git blob `394e0db063a476c5c069384b3d3fa2ffd3c7471d`, matching the
pinned source. This implements `raw_exact.C26`, proof note N10, alongside
already proved actual menus, zero-word exclusion and direct-edge merging.
No mathematical contract or source file is changed.

The prior `cycle_marked_cases` theorem proved that every actual raw simple
cycle either has one common underlying marked edge or yields a genuine
`MarkedProjection`. One common label alone did not state the complete
literal two-whole-path alternative required by the contract. The new
proof now gives that exact missing conclusion.

## Exact source-to-Lean map

- `QuotientExpansionThetaBranches.lean` defines `OccurrenceEdge` using
  literal original word occurrences and adjacent reduced positions. Its
  `occurrence_label_on_cycle` connects any witnessed traversed path edge
  to the actual chosen initial cycle label, including merged direct words
  and both orientations. `cycle_mark_neighbours` proves that the two
  actual neighbours exhaust all cycle edges at a mark. Under the actual
  single-label alternative `single_label_left_edge_first_step` identifies
  each such edge as the first step of an original occurrence on that
  precise underlying marked edge. `whole_path_on_cycle_of_first_edge`
  handles direct length one and longer words separately and retains every
  vertex and every edge actually traversed by the cycle.
- `QuotientExpansionThetaChoices.lean` constructs `TwoMarkChoices` from
  those two actual, distinct cycle neighbours. Their original occurrences
  are distinct; repeated direct words cannot count as two cycle neighbours.
  `TwoMarkChoices.interior_occurrence` proves that EVERY private interior
  on the cycle belongs to one of these two same occurrences. It uses whole
  path closure and the exhaustiveness of actual marked cycle incidence,
  rather than any assumed graph decomposition or source provider.
- `QuotientExpansionWholeCycleClassification.lean` proves
  `cycle_two_whole_paths_of_single_label`: there are two DISTINCT original
  occurrences on the same marked edge, both with positive reduced length;
  for EVERY formal vertex its membership in the actual cycle is equivalent
  to membership in the union of ALL positions on the TWO WHOLE paths; for
  EVERY pair of vertices its being an actual traversed unoriented cycle
  edge is equivalent to belonging to the union of ALL edges of the TWO
  WHOLE paths. `TwoMarkChoices.cycle_edge_covered` gives the difficult
  exhaustion direction, and the whole-path proof gives the converse.
  `cycle_two_whole_paths_or_marked_projection` combines this exact literal
  alternative with the existing genuine simple cyclic embedding of distinct
  marks, preserving every originally used edge label. The existing
  `projected_typed_cycle` constructor supplies its specified typed cycle.

All these results are general over the original typed source and arbitrary
finite marked sort assignment. Their only data beyond the constructed
actual diagram are the finite menus and the nonemptiness needed to define
its actual reference source-atom labels. In the actual quotient application
these data are already constructed by `CanonicalQuotientExpansion`, not
new assumed providers. No positivity of the entire word family, CCO, Helly,
SAP, pre-existing quotient homogeneity, path injectivity of a real walk or
cycle-classification premise is used. The proof itself establishes positive
length for its two chosen original occurrences. Empty/singleton menus,
identity-letter suppression and merged duplicate direct edges are retained
by the underlying actual expansion, rather than excluded by new premises.

## Validation

All three new public modules are explicitly imported by root `CCO.lean`.
Targeted build succeeds (848 jobs). Full combined root build succeeds
(1,019 jobs). Official transitive module-origin audit succeeds for all
2,190 CCO declarations with only `propext`, `Classical.choice`, `Quot.sound`.
The explicit public-root API and axiom check succeeds. Generated artifact
parts were also checked against their actual Lake trace hashes.

This is an additive implementation on a history-preserving merge of the
reviewed literal C06 leaf `3e868f530891c6e24d6a77d0784a8f09bbc951ea` and
actual expansion leaf `55d8742`. Original branch and WIP history are retained.
The current combined batch source map is maintained separately by the C28
assembly task. Exact remote-head/main CI, fresh whole-batch non-author
review and coordination acceptance remain necessary; this leaf does not
claim the batch is already integrated or accepted.
