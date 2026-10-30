# B048 actual marked-model full SAP and full-isomorphism transport

Author actor `/root/b047_strong_phase`, Work project3 effective claim388;
fixed source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5` and accepted
base/main `787dd3b59e0405223a9b5870d562d2861c9f33d4`. This follow-on task
owns only `BinarySource/MarkedLimitSAP.lean` and this receipt. Previously
frozen detours, C06 old full SAP, SourceSpan and OneColour source proofs
are preserved. Native terminal Model/Inheritance checkpoint e97f618 was
merged preserving history; its stale empty FullSAP stub conflicted with
our completed C06 and was resolved to the complete d47ce20 implementation.

`MarkedLimitSAP.ageSAP U S pack mask classSap` proves genuine FULL relational
AgeSAP of `FullReduct.expandedTable U S pack mask classSap`, the ACTUAL
constructed marked Fraisse model. The class SAP proof is the SAME proof
used to construct that model; final assembly instantiates it by the proved
`Marked.strongAmalgamation` and its actual B047 pair-SAP input. No model SAP,
homogeneity or finite-age callback is introduced.

The proof accepts arbitrary finite full relational age spans, normalizes
all relation truths into the ONE shared BoolTable representation, and
uses the actual native `data.finite_age` theorem to obtain full chart
isomorphisms. It transports the exact two given span embeddings into the
proved finite marked class SAP. The resulting complete marked chart then
embeds into the SAME native model through `Marked.classEmbedding`.
The source embeddings retain every original positive/negative tuple,
including nullaries and repeated arguments, and the class SAP's exact
common-base/intersection equations are transported to the original span.
Empty bases and finite structures are included.

`ageSAP_on_isomorphic_table` transfers this full SAP to ANY full table T
in an arbitrary receiving carrier universe via a TRUE all-tuple
`Canonical.Iso T expandedTable`. It does not treat the native Type0
finite-age theorem as universe-polymorphic: each finite source is explicitly
reindexed through `Fintype.equivFin` before native chart classification.
The finite amalgam chart is explicitly `ULift`ed into the receiving
universe, preserving its whole full table, all span maps and exact base
intersection. This applies directly to the terminal actor's actual full
pullback on the SAME original full carrier M, using its proved expanded
full isomorphism; a merely binary or old-pair isomorphism is insufficient.

This is a source transfer theorem, not an additional completion interface.
The owner must instantiate both the actual finite class SAP and the actual
full isomorphism in the final source/tower consumer; none of the proved
conclusions is a new source hypothesis.

Validation: exact pinned Lean4.34.1/Lake5, repository manifest and private
runtime/cache. Narrow `lake build CCO.FullPhaseLift.BinarySource.MarkedLimitSAP`
passed2538 jobs for the original actual-model proof (native5a46b6c) and
again2538 for the final receiving-universe full-Iso transfer. Log is outside
Git at runtime/b048-marked-model-sap.log. Existing style warnings are
nonfatal. No full root build, duplicate tests/audit, remote writes,
`axiom`/`sorry`, new helper agents, source/contract changes or review-actor
input. Root retains the one assembled exact-head root build/CI/axiom audit.
