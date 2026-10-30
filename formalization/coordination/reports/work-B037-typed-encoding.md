# B037 literal typed encoding and actual obstruction discharge

Actual implementation author: `/root/workspace_recovery`. Original B036
generic-source recovery is a separate task and is not this new mathematical
implementation. Mathematical source remains
`490c3f36d85db5a0b3ced0598e6c431825254ec5`,
`sections/unary_hn_transfer.tex`; B037's contract and preparation notes are
unchanged. This report covers one implementation stream, not acceptance of
the complete batch.

## Concrete representations and exact maps

The typed language is the accepted `UnarySupport.Signature`, with genuine
single-valued PARTIAL unary functions, input/output sorts, arbitrary relation
arity, and no constants or higher-arity functions. `Raw.language L` has
function symbols `L.Func` of arity one and relation symbols `L.Rel ⊕ L.Sorts`.
The latter interpret old relations literally and each sort by a unary
predicate. `encode` keeps exactly the original carrier, function graphs,
relation tuples and nullary truth.

`embeddingEquiv` is a bijection on actual induced embeddings, preserving the
literal vertex map. It reflects function domains and all defined values.
`closed_encode_iff`, `encode_induce` and `closure_encode` prove the actual
closed subsets, induced interpretations and generated closures coincide.
`pullbackTyped` decodes ANY raw induced source embedded in an encoded typed
target; its actual typing, functionality and relation sorting are derived
from that embedding. It does not assume that source was already typed.

## Claim and declaration map

| Claims | Actual proof and scope |
|---|---|
| C01–C02 | `PairCoverage.lean`: exclusive points in opposite proper closed factors contradict either unary reachability or a displayed POSITIVE binary tuple. `unary_link_reachable` supplies the function case. The source-facing `typed_unary_binary_irreducibility` retains `C.Total`; arbitrary additional relation arities are permitted. |
| C11 | `Basic.lean` proves the same-carrier encoding/decoder, exact embedding equivalence, closedness and induced/closure equalities. `Free.lean` converts typed closed subset decompositions to actual native `ProperFreeDecomposition` diagrams and back. `irreducible_encode_iff` proves genuine irreducibility equivalence. |
| C12 | `EncodedClass K` means an ACTUAL typed K object on the SAME carrier with `encode C = D`. `encoded_finiteHereditarySAP` derives native finiteness, singleton fibres, heredity and SAP. The initially raw common base is decoded through its actual left embedding; the right embedding has the SAME root map. The given typed SAP supplies the target and exact overlap, which are preserved literally. `encoded_allIrreducible` proves the class's irreducibility transfer. |
| C18–C19 | `Typing.lean`: `point_hull_irreducible` uses the independent actual raw one-generated closure theorem. Each entire point hull is an actual `EncodedClass K` member. Its sort predicates force a unique sort at the root; its full graph forces partial functionality, input/output typing and, under completed-class totality, exactly the intended domain. |
| C20–C22 | For EVERY displayed old relation tuple, `typed_of_irreducibles` invokes the actual all-arity `Native.relation_tuple_hull_irreducible` proof and local completed membership. Every tuple coordinate has the prescribed type, including repetitions. Arity zero requires no coordinate and its truth remains literal. The conclusion is an actual typed C with `encode C = D` and `C.Total`, before any typed obstruction premise is used. No raw type/singleton correctness is assumed. |
| C37 | `irreduciblesIn_subsets` supplies the precise B034 subset interface from ALL actual typed induced irreducibles. `b034_singleton_and_total` invokes only accepted actual singleton membership C20 and totality C21, supported by its independent singleton irreducibility C19. No optional m-bound, term identity or hidden-specific provider is used. |
| C38 | `restricted_of_direct` PROVES the main restricted obstruction premise from the direct one. The latter tests only actual K-membership of all singleton generated diagrams. Totality is derived, not an extra unrelated direct-premise assumption. |
| C39–C41 bindings | `encoded_restrictedObstruction` and `encoded_directObstruction` provide the ACTUAL native N-premise for the principal native theorem. `allIrreducible_of_binary` derives completed irreducibility and retains the final source's arity-at-most-two scope. The complete main/direct/binary theorem wrappers are owned by `Source.lean`. |
| C42/C47 scope | Actual completed irreducible membership is an explicit input to raw typing and the restricted bound; arbitrary malformed diagrams are not granted a bound. Tests use actual closed functional subsets and exact cardinalities. This stream certifies no uniform bound on arbitrary sources or on generated closure sizes. |

## HE, completion and ordered-arrow semantics

`TypedTransferBasis.HE` preserves positive relations, sort predicates and
defined unary values and embeds EVERY actual closed irreducible source via
its induced embeddings. It is not the selected-support local notion.
`he_encode_iff` proves equivalence with the native original-partial EHN HE
on the SAME given vertex function. `completion_encode_iff` transports actual
finite K targets, not merely abstract completion assertions. Global injection
or global inducedness is not inserted into ordinary completion.

`OrderedReadout.lean` defines actual typed induced embeddings additionally
preserving AND reflecting the given strict order. `orderedEmbeddingEquiv`
identifies these with the full native ordered embeddings on literal vertex
maps; `orderedArrow_encode_iff` proves that the native arrow colours ALL
these embeddings and has the same monochromatic-copy conclusion. There is
no copies-to-embeddings oracle or representation callback.

The obstruction bound N is an INTEGER, including negative values.
`encoded_restrictedObstruction` first derives a correct typed candidate from
actual raw membership. It then applies the GIVEN typed bound, retains its
SAME finite point set and literal `(S.card : ℤ) ≤ N`, and transports precisely
that induced noncompletion. It neither enlarges S to a generated closure nor
substitutes a different cutoff. The native principal theorem owns the
explicit `Int.toNat (max 1 N)` local-finiteness cutoff.

## Verification and remaining batch work

Seven new modules, 899 Lean lines. Assigned narrow targets:

```text
lake --rehash build CCO.UnaryHN.RawEncoding.Obstruction CCO.UnaryHN.RawEncoding.OrderedReadout
```

The exact Lean4.34.1/manifest was used, with privately copied exact-subtree
106-module Ramsey outputs and private pinned EPPA269 outputs. No provider,
toolchain, old dependency pin, source TeX, contract or public ledger was
changed by this stream. No whole CCO pipeline, transitive axiom audit,
independent review or complete-batch acceptance is claimed here. The owner
must assemble all source exports, the separate C46 boundary and consumer,
then run the one final receiving pipeline and exact public CI/audit.
