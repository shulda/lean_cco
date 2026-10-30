# B039 C49: actual second countable homogeneous model

Actual implementer: `/root/b039_fresh/sap`, reusing the same contributor identity
as the completed hereditary SAP stream. Source pin and B039 contracts remain
unchanged. This stream owns only `Examples/TwoCover*.lean`; the shared finite
permutation-extension lemma is the examples helper's actual B039 proof, not an
unaccepted external dependency. No B037/B038 source is imported.

## Original model and exact failure mechanism

The actual carrier is the disjoint sum of M=(Nat×Bool)×Nat, V=Nat×Bool,
and Q=Nat, with named sorts 0,1,2. The finite ORIGINAL signature has precisely
four total typed unary functions: τ:M→V, r:V→Q, p:M→Q and fibrewise swap on V.
There are no relation symbols or nullary generators. Off-sort identity values
are only the agreed canonical representation of typed functions.

The actual singleton closure of a real (q,b,n) is exactly its real point,
(q,b), (q,not b) and q. Hidden V singleton closures have those two V points
and q; a Q singleton closure is just q. Every hidden point has a literal
named τ or p quotient representation from the real sort, with actual kernel
strictly above identity. The real sort is genuinely transitive under full
automorphisms.

Both actual named real quotient maps satisfy the forced named-factor clause
for EVERY existing typed real-source term, not just the four generators.
For p, a combined bit/coordinate flip inside one p-fibre moves every non-Q
point of a reference real closure. Thus a forced term must have Q output
and has the named identity factor. For τ, a coordinate flip eliminates real
output; the remaining factors are the named identity/swap on V or r:V→Q.
Equality at the reference real point globalizes using actual transitivity
and named-term equivariance. This argument also applies to arbitrary long
syntactic swap words without assuming a finite list of term syntax.

In contrast, τ is unforced for p and its ENTIRE actual image on each p-fibre
is exactly the two V points. `actual_relative_index_two` proves cardinality2
of this actual image, rather than a formal group-index ratio. The full
pointwise-root stabilizer orbit on either V point is exactly that two-point
set, so it is algebraic outside the root's actual singleton unary closure.
`original_not_ageSAP` derives failure of hereditary SAP from the previously
proved actual unary criterion; SAP failure is not supplied as a premise.

## Homogeneity and real-base infinitude are discharged

A concrete family of full automorphisms consists of arbitrary permutations
of Nat roots, independent per-root Bool permutations, and independent Nat
permutations of each real V-fibre. Every Bool permutation commutes with the
named swap. Given ANY finite closed partial induced isomorphism, the actual
root requests extend to a Nat permutation, the τ-kernel requests extend to
per-root Bool permutations, and the remaining real coordinates extend to
independent fibre permutations. These constructions prove homogeneity on
ALL finite closed pieces, including orphan hidden bases.

For any finite REAL base D and point outside cl(D), its actual FULL-Aut orbit
is infinite. A real point moves to arbitrarily fresh coordinates within its
exact V-fibre, while a hidden point moves to a fresh root. Each chosen motion
fixes D pointwise. The proofs exclude every hypothetical finite orbit by
an actual fresh Nat value; no finite-reservoir experiment is used to claim
infinity. Countability, finite signature and local finiteness are also
proved properties of this concrete infinite model.

## Conservative presentation, not extra structure buying homogeneity

Intermediate files use nine typed root-equality predicates to keep root
requests readable. They introduce no function or named factor. In
`TwoCoverOriginal.lean`, `rootValue` is the appropriate ACTUAL named p, r,
or identity on each sort and belongs to every closed piece containing its
argument. Injectivity and function preservation therefore preserve AND
reflect every auxiliary root predicate. `expandedEmbedding` lifts EVERY
original closed partial embedding with the SAME point map, and
`automorphisms_eq` proves literal equality of the full automorphism subgroups.
Consequently `original_homogeneous`, `original_real_base_orbits`,
`original_locallyFinite`, `original_forced_named_factors` and
`original_algebraic_off_closure` are proved for the relation-EMPTY ORIGINAL
signature. Typed terms are explicitly translated between presentations;
no term or quotient is added by the auxiliary predicates.

All declarations are under `CCO.UnaryFreshFrames.Examples.TwoCover`.
`TwoCoverBoundary.lean` additionally provides `tauTerm`, `pTerm`,
`every_hidden_named_quotient`, `tau_unforced_for_p`, `original_not_ageSAP`,
and `original_scope`.

## Validation and history

Seven new TwoCover Lean modules,892lines. Coherent source commits:
`1348bac07b1625d9f2a87f219038e1eb456177a1`,
`20e9d06f73f0427b49115f47b22651e690856d5b`,
`0dc0218f60cec54ac65c175e75e8fd238b3dc49c`,
`0b0d06b8b02ecf0ec6078b350c0bda8c60b0349b`,
`5c4d06db86f0675b934db6dfb1780e13b34d47d8`, and final mathematical
`6153a348564026817db3b833d397eb8a7188ea88`.
Final narrow union `lake build CCO.UnaryFreshFrames.Examples.TwoCoverBoundary`
passed1341jobs, exit0, with all seven TwoCover modules freshly rebuilt.
No warnings remain in these new modules; old accepted B010/shared-helper
style suggestions are unchanged. No full receiving pipeline, test suite
or axiom audit was duplicated by this helper. The coordinator retains final
whole-batch independent review and exact-head/main CI/audit gates.
