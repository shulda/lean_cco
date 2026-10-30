# B036 generic normalization and restriction-compatible EP composition

Author: actual coordinator `/root`; isolated branch `work/B036-generic`.
Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`, actual
`sections/reset_midpoint_order_ep.tex`, the normalization and relative EP
composition labels. This report covers C07–C12 and C45–C51 only; it is not
a complete B036 acceptance report.

## Concrete structure semantics

`CCO.ResetOrder.Generic.Language` has arbitrary types of sort symbols,
functions of each finite arity and relations of each finite arity. Neither
the signature nor its symbol types need be finite. Function interpretations
are single-valued partial graphs, not silently total operations. Arity-zero
functions and relations are allowed. All tuple typing and every defined
function value are explicit. `Structure.Embedding` has an injective actual
vertex map, sort equality, exact image equality of function fibres and an
iff for every relation tuple. Thus definedness is reflected. In particular
nullary relation truth is retained even on empty carriers.

`Object` retains its actual finite carrier, without arbitrary reindexing
to `Fin n`. An age is a predicate on these concrete objects; heredity under
all induced embeddings includes isomorphism closure. `Arrow` colours ALL
induced embeddings, with `Fin (k+1)` colours for every natural k. This is
the usual arbitrary positive finite colour count, not a copies convention.

## Claim map

| Claims | Actual declarations and argument |
|---|---|
| C07 | `Structure.Embedding.same_map_domain_unique` proves equality of sort, function and relation interpretations for two induced source structures on the same carrier and same vertex map into a common target. `Normalizer.hereditary` applies it to the original and normalized embedding. No uniqueness callback is assumed. |
| C08 | `Normalizer.object`, `normalized_fixed`, `fixed_object_eq`: same actual carrier, legal normalized object and strict structure/object equality. |
| C09 | `Normalizer.fromFixed`, `fromFixed_point` and `arrow` pull an arbitrary normalized-host colouring back along the actual functor action. No map-surjectivity hypothesis appears. |
| C10 | `Normalizer.fromFixed_comp` derives composition on literal point maps using embedding extensionality. `arrow` obtains the normalized monochromatic copy. |
| C11 | `Normalizer.ramsey` and `foundational_ramsey_normalization` use the FULL class of all fixed objects. |
| C12 | `Normalizer.jointEmbedding` normalizes the actual joint host. No generic SAP inheritance is exported. |
| C45–C47 | `foundational_relative_EP_composition` chooses B, then C, before introducing arbitrary final expansion E. Its actual intermediate reduct E1 supplies the original induced f. |
| C48 | `Structure.pullback` constructs every inverse-image interpretation on exactly B.Carrier. `pullbackEmbedding` requires and uses function-closedness; `Reduct.pullback_reduct_eq` proves equality with the exact given B structure by induced same-map uniqueness. `pullbackExpansion` uses upper heredity only after this actual embedding exists. |
| C49–C50 | `pullbackEmbedding` preserves/reflects all upper data, including domains; its composite with the top EP embedding lies in the arbitrary E. The actual `RestrictionGate` is retained explicitly. |
| C51 | `restrictionGate_compose` constructs successive real inherited restrictions. `relativeEP_finite_tower` inducts on actual composed signature maps with every adjacent gate. Only the finitely many levels up to n are assumed. |

## Source hypotheses and limits

The `Normalizer` input is exactly the source's actual endofunctor condition:
legal normalized structures, an action on induced embeddings with the SAME
vertex map, and strict idempotence on members. Functor laws on embeddings
follow from these maps. The ambient hereditary/Ramsey/JEP properties remain
the stated conditional inputs. They are not imported external providers.

`Reduct` is a concrete map of relation/function symbols, retaining their
arities and named sort partition. Actual `Expansion` data live on exactly
the given old carrier and reduce by equality to its whole old diagram.
The composition proof needs actual reduct membership and upper heredity;
the stated source's additional reduct-surjectivity convention is also
defined, but the proof does not need to strengthen or use it.

`RestrictionGate` asserts function-closedness of EVERY legal intermediate
embedding image in EVERY final object. It does not assume existence of a
lifted embedding, an EP conclusion or an abstract restriction provider.
Legality and the lifted embedding are constructed from closedness and
heredity. `Reduct.KeepsFunctions` means EVERY upper function symbol is
retained by the actual reduct. `closed_range_of_keepsFunctions` derives
the gate from domain-reflecting lower embeddings. Hence arbitrary added
relations/orders with the complete old function signature satisfy it;
`relation_only_relative_EP_composition` and
`relation_only_relativeEP_finite_tower` instantiate this automatically.
The unrestricted function-adding composition reading is not exported.

## Validation and handoff

Eight new Lean modules, 604 lines. Final assigned-target command:

```text
lake --rehash build CCO.ResetOrder.Normalization CCO.ResetOrder.FiniteTower
Build completed successfully (406 jobs).
```

Exact pinned Lean4.34.1/Lake and the unchanged receiving manifest were used.
Only the assigned narrow targets were built; no whole-project pipeline,
axiom audit, independent review or complete-batch submission is asserted.
The owner will import these modules and run the one final receiving
pipeline after the complete B036 mathematical and documentation freeze.
