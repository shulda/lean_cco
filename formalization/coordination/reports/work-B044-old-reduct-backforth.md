# B044 support — actual old-reduct countable back-and-forth

Actual author: `/root/b043_point_sap`, acting as an independent implementation
helper for B044. This is internal mathematical support, not a new batch claim
or a discharged principal source instance. The B044 owner/root must prove
its two finite extension premises using the actual marked age and original
source.

Owned source: `CCO/APCharacter/SourceAge/BackAndForth.lean`.
Namespace: `CCO.APCharacter.SourceAge`. Actual tables are the accepted
`CCO.OwnerTransversal.CountableColour.Table B C Y` and `Table B C Z`.
All universes of B, C, Y, Z are arbitrary; only Y and Z need be countable
for the final bijection. Finite/empty carriers are included, and neither
inhabitance nor infinitude of either carrier is assumed.

`FiniteExtension T U` has exactly the concrete finite-chart interface:
for arbitrary n,m, j:Fin n↪Fin m, p:Fin m↪Y, q:Fin n↪Z, equality of
all old owner labels and ordered old colours along q and p∘j yields an
actual injective r:Fin m↪Z with the exact old table of p and r∘j=q.
This is a structural finite extension property to be discharged internally,
not an arbitrary global isomorphism or homogeneous-limit oracle.

`finiteExtension_firstOrder` enumerates each actual finite full relational
substructure and its larger finite full substructure by their literal Fin
cardinalities, constructs j,p,q and applies that concrete property once.
Its resulting r is converted to an actual first-order induced embedding,
preserving and reflecting every named owner and colour predicate. The
old restriction equality is proved on each point. All diagonals and both
ordered directions remain literal table values.

`isExtensionPair_of_finiteExtension` then uses the accepted generic finite
full-substructure extension argument to derive Mathlib's genuine
`IsExtensionPair`. Because the owner/colour language is relational, every
finitely generated substructure is finite; no local-finiteness oracle is
added. The theorem applies in either direction, with independent source
and target universes.

`equiv_of_finiteExtension` applies the actual Mathlib
`FirstOrder.Language.equiv_between_cg` theorem to those TWO proved extension
pairs, starting from the empty finitely generated partial isomorphism.
Owner/colour symbols have no arity-zero relation; functions are absent,
so this initial partial map exists even if a carrier itself is empty.
The actual final first-order equivalence is returned as Y≃Z together
with preservation of ALL literal owner labels and ALL ordered colours.
No final equivalence or whole homogeneity is assumed in its signature.

Verification: exact Lean4.34.1/Lake5 and unchanged accepted manifest,
`lake --rehash build +CCO.APCharacter.SourceAge.BackAndForth` PASS1138jobs.
No broad local project build, tests, axiom audit, root-import change or
GitHub mutation was performed. Seven old untracked B043 generic-source
copies in this stable physical checkout were preserved and were not
staged or committed. The helper's new branch starts from accepted green
main`e77b672fd17704e92d39786cbb8818adb36a9fcb` and preserves every earlier
B043/helper branch and original history.
