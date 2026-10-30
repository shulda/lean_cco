# B042 — internal finite groups, nonfaithful actions and actual cover counts

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`, selected source
`sections/cco_finite_fibres.tex`, claims C09–C12, C16–C27 and C32–C33.
These are elementary support for B042, with no new external theorem provider.
The implementation author is `/root/b042_finite/group_support`; the separate
actual author `/root/b042_finite/group_support/correspondence` supplied the
three `Group/Correspondence` modules and its precise companion report.
Neither contributor is a reviewer.

## Internal proof DAG

`Group.Counting` proves orbit cardinalities are p-powers directly from
orbit-stabilizer and the elementary divisors of a prime power. It expands
the finite orbit partition to obtain the fixed-point congruence. Actions
are arbitrary and may be nonfaithful. A known fixed point in a set whose
cardinality is divisible by p produces a second fixed point.

`Group.Cauchy` defines actual finite product-one tuples. The free-vector
equivalence gives the explicit cardinal `|K|^(p-1)`; `last_entry_iff` also
proves the source's literal first-entries/unique-last-entry assertion.
`rotated_product` records the conjugation identity for noncommutative K.
Actual cyclic rotation gives a permutation whose order divides p. Its
cyclic subgroup has one- or p-element orbits. Fixed tuples are literally
constant lists. The identity tuple and the proved fixed-point count give
a second constant tuple, hence a nonidentity g with order exactly p.
This is the local `local_cauchy` proof, not an imported Cauchy theorem.

`Group.Normalizer` separately factors a positive integer whose only prime
divisor is p, and supplies an odd prime divisor when an integer is not a
power of two. For a finite group of p-power order, it proves subgroup and
coset p-power counts. The fixed cosets of H acting on L/H are identified
with actual normalizer cosets by an explicit equivalence; finite conjugate
containment is turned into equality. Their positive count is divisible by
p, so H is strictly below its normalizer. Maximality then gives normality.
Applying the LOCAL Cauchy proof to the quotient would produce an actual
intermediate subgroup if the quotient order exceeded p. Thus a maximal
proper subgroup has index p.

Both Cauchy and Normalizer have a compiled `assert_not_exists` firewall for
the external `exists_prime_orderOf_dvd_card`, `IsPGroup` and `Sylow` names.
The local proofs cannot silently consume those target theorems. All imported
library facts used here are elementary finite products, prime divisors,
orbit-stabilizer, quotient groups and subgroup maps.

The three `Group.Correspondence` modules implement ALL invariant setoids in
an arbitrary transitive group action. G may be INFINITE and NONFAITHFUL;
the core even permits infinite carriers. The actual base-class subgroup,
coset projection, inverse kernel and full stabilizer-interval order
isomorphism are proved. Relative classes are literal fibers of the canonical
map `Quotient U → Quotient V`, with an actual relative-coset bijection,
uniformity by actual group motions, and exact quotient-fiber multiplication.
An invariant cover yields precisely an ordinary maximal proper subgroup
inside the upper base-class subgroup. No finite CCO/Hasse theorem is used.

`Group.FiniteCover.cover_relative_card_two` applies our local maximal-index
theorem INSIDE that actual upper subgroup, then the actual class/coset
bijection. It proves the cardinal of every relative class is TWO when G
has power-of-two order. It adds no faithful/regular action hypothesis.
The owner separately instantiates it with the actual FULL automorphism
group of its finite symmetric CCO target and the proved group-order theorem.

`Group.Chain` constructs a genuinely finite SATURATED cover chain between
any comparable elements of a finite partial order. It includes a zero-step
chain, explicit adjacent cover proofs, monotonicity and strict monotonicity.
Its `telescope` proves multiplication at every intermediate chain index.
`invariantSaturatedChain` applies that construction to the FULL finite
invariant-equivalence lattice, from equality to top. The proved relative
quotient-fiber counts along every cover telescope to
`Nat.card A = 2^C.length` for this actual chain. No cardinality or chain-length
oracle is a constructor field or a source premise. An independent orbit
route `transitive_card_two_power` supplies the same cardinal support without
homogeneity; named-colour recognition and the palette bound remain separate
source arguments.

## Exact claim map

All short namespaces below are under `CCO.FiniteFibres.Group`.

| Claim | Actual declaration(s) |
|---|---|
| C09 | `ProductOne.complete`, `delete`, `count`, `last_entry_iff` |
| C10 | `ProductOne.rotate`, `rotate_rotate`, `rotate_length`, `rotation_fixed_iff_constant`, `rotated_product`; `prime_rotation_orbits`, `fixed_card_modEq` |
| C11 | `local_cauchy`, using the actual tuple rotation and `second_fixed` |
| C12 | `power_of_prime_divisors`, `odd_prime_of_not_two_power` |
| C16 | `subgroup_card_power`, `quotient_card_power`, `orbit_card_power` |
| C17 | `fixed_coset_iff`, `fixedCosetsEquiv` |
| C18 | `normalizer_quotient_modEq`, `normalizer_strict` |
| C19 | `maximal_normal` |
| C20 | `maximal_index` |
| C21–C24 | `Correspondence.InvEq.subgroup`, `subgroupCorrespondence`, `cosetEquivRelative`, `relative_card_eq_index`, `relative_card_uniform`, `subgroup_cover`, `relative_subgroup_maximal`; companion report records the exact individual map |
| C25–C27 | `cover_relative_card_two`, with actual target/full-Aut/source hypotheses discharged in the owner's export |
| C32 | `SaturatedChain.exists_between`, `invariantSaturatedChain`; exact bottom/top quotient cardinal proofs |
| C33 | `SaturatedChain.telescope`, `chain_card_two_power`, `actual_chain_card_two_power`; independent `transitive_card_power`, `transitive_card_two_power` |

## Validation boundary

Each module and its assigned consumers passed narrow pinned Lean 4.34.1
Lake builds in the same private physical build slot. The final support
target is `lake build CCO.FiniteFibres.Group.FiniteCover`; the complete
support closure contains 1463 Lake jobs. No duplicate local whole receiving
suite, test run or axiom audit was used. Public exact-head PR CI/audit,
actual nonauthor review and actual resulting-main CI/audit remain coordinator
gates. Source/contract/policy/toolchain/manifest/accepted APIs are unchanged.
All prior branch histories and untracked inherited WIP copies are retained;
commits stage only the owned B042 files and this report.
