# B037 — actual E02 and ordered-transfer providers

Author: `/root/frontier16`. This report covers its own new EPPABridge and
Ordered modules and OrderedAmbient. It does not assert whole-batch acceptance.
Mathematical source remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`.

## Source-to-Lean map

| Source obligation | Actual implementation |
|---|---|
| E01 functional HN2.19 | `OrderedAmbient.allOrderedModels_ramsey` applies the real upstream `allThoseRamseyClasses_theorem_2_19_partialFunctions` on the compatible native provider. The witness is singleton-valued and globally ordered. |
| E02 unary injectivization | `EPPABridge/Completion.unary_completionIffStrong` constructs an actual finite hereditary SAP class and applies accepted `AllThoseEPPA.MainTheorems.completionIffStrong`. `Native.unary_injective_completion` retains the source's singleton/irreducible-class hypotheses. |
| Nullary/empty boundary | `Homomorphism.HE_profile` tests the ACTUAL empty closed irreducible, deriving the given completion's full nullary profile. `Encoding` keeps that profile on every decoded carrier, including the empty carrier. Positive symbols/functions stay on the same carrier. |
| Actual class and map bridges | `Encoding`, `Irreducible`, `Homomorphism` prove exact profile-restricted encode/decode identities, both full-embedding/closed-substructure transports, both irreducibility directions and both HE transports. `profileClass` has actual decoded K membership, finite members, hereditary embeddings and exact strong intersection. No representation/class/HE callback occurs. |
| C13–14 ordered ambient | `OrderedAmbient` defines arbitrary global ordered expansions and proves their actual irreducibility. Adding a displayed order to an OLD irreducible is used separately in `Ordered/Forget`; the converse is never asserted. |
| C15 heredity and ordered SAP | `Ordered/Amalgamation.orderedClass_finiteHereditarySAP` proves the complete record. Heredity pulls back the actual target global order. Strong amalgamation first uses old K SAP, then `Ordered/Shuffle.shuffle_orders` constructs an order on the entire resulting carrier. |
| C16–17 exact reduct tests | `ordered_irreducibles_reduct` pulls the DISPLAYED order onto the given old irreducible before applying actual expanded membership. `ordered_completion_reduct` and `ordered_small_reduct` forget only the order, on literally the same closed subset/carrier/cardinality. |
| C27 genuine injective old completion | `Ordered/Completion.ordered_completion` invokes the proved E02 endpoint on the supplied old completion. Its finite target remains an actual old K member. |
| C28–30 displayed-order transport and extension | The given HE into the fixed globally ordered test target strictly preserves every displayed order edge even if that HE is not injective. The separate E02 injection transports those edges. A label into `WithBot` of the fixed test order agrees with the given map on the injection's range; extra points receive bottom. The native finite extension orders the WHOLE target carrier. This handles empty test/source carriers and needs no arbitrary source representative for extra points. |
| C31–33 full expanded HE | Every actual expanded irreducible test is an ordered K member by `hPieces`; ONLY THEN is its old reduct irreducible by the old-class hypothesis. The old HE is full on that entire reduct. Displayed-edge preservation makes its restriction strictly monotone; its actual source linear order gives order reflection. The resulting map is globally injective HE, without a global inducedness claim. |

## Whole-base shuffle construction

For each side point the key records the number of common-base points below
it, whether it is itself a base point, its side, and its within-side rank.
At identified base points both side keys agree, using the actual common
strict order. Exact old SAP overlap ensures that no other point receives
incompatible side keys. Each side key is strictly monotone. A finite rank
tie-break extends the combined label to a linear order on every point of
the old amalgam, including points outside both images. An empty common base
is the same zero-cut construction; no special nonempty-base premise enters.

## Verification and boundaries

The four E02 files were recovered from the complete prior proof/tool source
after the transient workspace loss: 554 lines, with their actual final
compile fixes retained. Fresh narrow verification passed:

- `lake --rehash build +CCO.UnaryHN.EPPABridge.Completion`: 1369 jobs.
- `lake --rehash build +CCO.UnaryHN.Ordered.Amalgamation`: 1517 jobs;
  all five ordered modules built, including genuine ordered SAP.

The final mathematical checkpoint is `6fce0a50d79fb37358e061200044e1e281e281fd`.
The owner receives the actual declarations, not proof-provider assumptions.
The obstruction bound, local-finiteness induction, typed encoding and final
Ramsey assembly belong to the other named B037 owners. No whole CCO build,
axiom audit, public claim/write or integration was repeated by this stream.
Accepted EPPA code/pin, mathematical contracts and original source files
were not changed. Ordinary original class assumptions remain explicit.
