# B042 — nonfaithful action and invariant-equivalence support

Actual implementation author: `/root/b042_finite/group_support/correspondence`.
This is implementation work, not an independent review. Base is accepted
`1121b2016c7141ac432364b07c49c0ae31b18dbe`; the source pin remains
`490c3f36d85db5a0b3ced0598e6c431825254ec5`. The B042 mathematical contract,
all accepted APIs, toolchain, manifest, policy and source text are unchanged.

All declarations below are in
`CCO.FiniteFibres.Group.Correspondence`, with the explicitly indicated
`InvEq` nested namespace. Only elementary Mathlib setoid, group-action,
coset, order and finite cardinal APIs are imported. There is no CCO,
source Hasse, finite p-group, Cauchy or B040 theorem dependency.

## Actual mathematical scope

`InvEq G A` contains ALL invariant setoids on the actual action carrier.
It is the complete lattice obtained from intersections of all invariant
equivalences, with logical identity as bottom and universal relation as
top. For finite A the whole lattice is finite. Neither the lattice nor
the correspondence requires the acting group to be finite or faithful;
the core correspondence even allows an infinite carrier.

Fix an actual point a and actual transitivity. `InvEq.subgroup E a` is
literally `{g : G | E (g • a) a}`. Its multiplication and inverse proofs
use only invariance and the equivalence laws. It contains the actual
point stabilizer. `relative_motion_iff` proves that membership of
`g⁻¹h` means exactly E-equivalence of `g • a` and `h • a`.

For every H containing that stabilizer, choose a real motion sending a
to each x and project it to the actual left coset space G/H. The choice
is independent modulo H; `projection_move`, `projection_base` and
`projection_orbit` prove the actual equivariance and base/orbit equations.
No group structure on G/H, normality of H, group section or coherent
choice of representatives is assumed. The kernel of this projection is
the inverse invariant equivalence. Both inverse equations and order
reflection are proved, giving the full `subgroupCorrespondence` order
isomorphism onto ALL subgroups above the actual stabilizer.

`RelativeClass U V h a` is the literal fibre of the actual map
`Quotient U.val → Quotient V.val` above the V-class of a. It is not a
chosen abstract set of cardinality supplied by a premise. The explicit
map from `H_V / (H_U.subgroupOf H_V)` sends the coset of g to the
U-class of `g • a`; well-definedness, injection and surjection are
proved. Its cardinal is exactly that subgroup index. Actual motions
give equivalences between relative fibres over any two base points.
Partitioning the actual quotient map into these equal-size fibres then
proves the quotient cardinal multiplication used by finite chains.

A cover in the FULL invariant-equivalence lattice excludes every
intermediate subgroup above H_U and below H_V. Mapping subgroups of H_V
back to G proves that `H_U.subgroupOf H_V` is proper and maximal in H_V.
This is exactly the ordinary subgroup maximality used by the separately
proved local finite p-group theorem, with no finite-group assumption in
the correspondence itself.

## Exact source support map

| Contract item | Actual receiving proof |
|---|---|
| D06/C21 | `InvEq.subgroup`, `InvEq.stabilizer_le`, `InvEq.relative_motion_iff` |
| C22 | `representative_spec`, `projection_move`, `projection_base`, `projection_orbit`, `ofSubgroup`, `subgroup_ofSubgroup`, `ofSubgroup_subgroup`, `subgroup_le_iff`, `subgroupCorrespondence` |
| D07/C23 | `RelativeClass`, `cosetToRelative_bijective`, `cosetEquivRelative`, `relative_card_eq_index`, `relativeMove`, `relative_card_uniform` |
| C24 | `subgroup_cover`, `relative_subgroup_maximal` |
| C32 support | `InvEq` complete lattice, `InvEq.bot_apply`, `InvEq.top_apply`, finite whole `InvEq` instance; saturated-chain existence is supplied by the group-support parent |
| C33 support | `quotient_card_mul_relative`; the index-two and finite-chain specialization is supplied by the group-support parent |

## Validation boundary

All three new modules compiled with the pinned Lean 4.34.1 and existing
private incremental cache. The final narrow command
`lake build CCO.FiniteFibres.Group.Correspondence.Counting` passed 1073
jobs, including its actual Basic/Relative dependency closure. No broad
local tests/audit pipeline or independent reviewer build was run here.
Exact public PR/main CI, complete current-source guards, transitive axiom
audit and actual separate nonauthor approval remain coordinator gates.
There is no open provider or proof obligation in this assigned support.
