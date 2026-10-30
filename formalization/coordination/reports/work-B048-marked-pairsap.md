# B048 actual marked pair strong spans

Author: `/root/b047_pair_safe_split/infinite_type_fibres`.
Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`; B048 claim STATE388.

`CCO/FullPhaseLift/Marked/PairSAP.lean` defines the exact actual chart property
`PairStrongAmalgamation`: every span of complete legal marked pair charts has
one finite legal chart target, induced embeddings commuting over the base,
and no cross-leg intersection outside that base.

`actual_pairStrongAmalgamation P cco sap` proves the property for `P.masks`.
It constructs the accepted B047 `actualIdentification P cco` internally, uses
B047 `unary_source_sap P cco I sap`, and applies the independently authored
unchanged generic `BinarySource.strict_pair_span`. Actual chart names embed
into that same unary source via `Age.chart_names` and `newEquiv`. The returned
finite union is recoded to a finite ordinal; `oldEquiv` and its literal actual
marks give a realized legal old chart. Reflected full child colours fix both
marked leg structures, and the generic strong intersection is retained.

Only original pair SAP is supplied. No full old SAP, arbitrary homogeneous
seed, marked-pair SAP callback, A03/full completion oracle or new axiom occurs.
This is the actual pair-chart SAP input used by the separate full marked SAP
construction; it does not itself assert a full-language theorem.

Canonical work remains frozen on preserved branch `work/B048-canonical-frozen`
at `b3c13aed929d87f3b6c1b3ac6c635502a88758ef`. This follow-up is isolated in
`work/B048-marked-pairsap`; root remains sole publisher and final build/audit
owner. Narrow validation target: `CCO.FullPhaseLift.Marked.PairSAP`.

The final narrow target succeeded with 2496 jobs on pinned Lean 4.34.1 and
unchanged manifest. Imported native SourceSpan extraction `8a7bb2c` reuses the
strongworker's exact `strict_pair_span` proof (original native `59b87e9`). Its
mechanical extraction removes every canonical/full/marked dependency. The
adapter adds only Marked/PairSAP.lean and this report; no shared owner files,
root CCO imports, broad audit or remote writes were changed.
