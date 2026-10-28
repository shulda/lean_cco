# B003 C12 support: genuine finite simple-path profile realization

Proof checkpoint `b7f97a0812e0388f6c7fce82d3cfe45868e65ed2` on local
`work/b003-finpath`, extending the reviewed C07–C09 and PCExactness route
plus actual cycle helpers. Source pin, contracts, toolchain and manifest
remain unchanged. Implementation actor: `strong_bridge`.

`FinLinePath` defines the actual traversal vertex list of a
`SpecifiedPath`, and `SimpleSpecifiedPath` is the subtype whose ENTIRE
vertex list is nodup. This distinguishes true simple formal paths from
the older wider class of endpoint-separated walks.

Given an injective enumeration `Fin(n+2) ↪ V` with one literal specified old
atom on EVERY adjacent pair, `specifiedLinePath` constructs the actual
positive path. `specifiedLinePath_vertexList` proves its vertex list is
EXACTLY `List.ofFn vertices`; `specifiedLinePath_nodup` uses the provided
formal embedding, so `simpleSpecifiedLine` is genuinely simple.

`specifiedLinePath_represented_readout` reads any represented word witness
onto those EXACT original line vertices, respecting every given old atom
and retaining the two literal real endpoints. The final source theorem
`specifiedLine_realizable_of_profile` uses original homogeneous SAP word
semantics to realize any GIVEN profile atom along that literal old line,
with that SAME endpoint diversity atom. There is no stable-network,
path-formula, CCO, or conditional completion-provider premise.

This supplies the old-simple-line cut bridge for the separate C12
augmented-edge proof. It does not claim the complete simple-path formula
or replace it by the all-endpoint-separated-walk bound. C13 converse
canonical packaging is also separate. B003 remains **IN_PROGRESS**.

Validation: new module kernel-checks without warnings; all public modules
are imported from `CCO.lean`. Freshly materialized full root builds in
**1025 jobs**. Explicit `import CCO` checks expose the new path theorem and
the earlier cycle/C09/PCExactness APIs in the SAME audit environment.
Transitive audit: **1781 CCO declarations**, including private names, only
`propext`, `Classical.choice`, `Quot.sound`; explicit path-theorem axiom
print confirms the same allowlist. Remote exact-head CI and independent
exact-SHA review remain required before submission/integration.
