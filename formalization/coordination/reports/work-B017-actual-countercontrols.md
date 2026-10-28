# B017 C21–22 actual binary countercontrols

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Actual implementer: `/root/b015_groupoid/quotient_calculus`, reused after its
completed B015 C01–05 handoff. All files are under
`CCO/FiniteKernel/Countercontrols/`; no named-axis files or reviewer role were
authored by this implementer.

## C21: literal hidden-parity canonical binary source

`HiddenParity.lean` defines the actual ten-point disjoint union
`(Fin 3 × Bool) ⊕ (Bool × Bool)`, with four named owners and EVERY actual
ordered-pair orbital of the shifts `(u,v,u xor v,(u,v))` as a binary predicate.
The full automorphism group is proved exactly these four shifts: the image of
D(0,0), together with the named orbitals `(D(0,0),x)`, determines every image.
No assumption identifying an arbitrary subgroup with full Aut is used.

The actual ABC projection is exactly `c = (a xor b)`, and all three actual
pair marginals are unrestricted. The whole six-point A∪B∪C finite domain is
used for the lone-A flip. Its map is injective and preserves every unary and
ordered binary instance, but has no full-source automorphism extension.
Consequently the actual canonical source is NOT homogeneous. Its owner kernel
is the full actual automorphism group.

`HiddenParityMarginals.lean` strengthens the coordinate readout at the literal
generic API. EVERY intrinsic whole-fibre motion is the restriction of an actual
global shift, so every actual binding group equals its intrinsic group. The
three axis intrinsic groups have cardinality two, the central one cardinality
four, and all have exponent two. For any two distinct A,B,C axes the ACTUAL
`partition.actualPair` subgroup is the whole product of their intrinsic groups.
The whole-three-axis motion still satisfies the parity equation; an explicit
odd triple is pairwise liftable but not jointly liftable. Thus the obstruction
is eliminated-coordinate width, not an intrinsic/binding discrepancy. All
point sets, motions and pair predicates are the actual source ones.

## C22: literal homogeneous S3 moving-owner source

`RightRegular.lean` treats an arbitrary group K in the actual original binary
language `R_r(x,y) iff y=x*r`, with no unary owner names. Its full automorphism
group consists EXACTLY of left translations, with explicit group isomorphism.
For each nonempty finite prescribed partial isomorphism, fixing a domain point
x₀ proves `f(y)=f(x₀)*x₀⁻¹*y`; this exact map extends. The empty finite domain
uses identity. This proves genuine source homogeneity.

`MovingOwners.lean` specializes to the actual six permutations of Fin 3.
The transposition h=(0 1) has subgroup H={1,h}; owner(x)=x(2) describes the
three two-point left cosets xH. The owner equivalence is definable as actual
equality union R_h and the classes really move under original automorphisms.
The actual owner-action kernel is identified with core(H), and the core is
proved trivial. Each actual induced fibre nevertheless has its FULL permutation
group as intrinsic group, explicitly group-isomorphic to permutations of its
two points, cardinality two and exponent two. Each actual binding subgroup is
trivial and strictly smaller than this intrinsic group.

For distinct actual owners, every local pair motion is identity: a preserving
pair tuple is restriction of one left translation, which fixes two distinct
points of Fin 3 and hence is identity. Thus local pair groups are trivial and
are not subdirect over the nontrivial intrinsic groups. After naming every owner
separately, the actual full automorphism group becomes trivial, but the literal
two-point whole-class flip remains a finite induced partial isomorphism. It has
no extension; the owner-named expansion is NOT homogeneous.

No CCO, SAP, quotient exactness, linear separation, compactness or relative-owner
homogeneity theorem is claimed for either countercontrol. The first original
source is explicitly nonhomogeneous; the second original source is genuinely
homogeneous and its owner expansion explicitly is not.

## Validation

Pinned Lean 4.34.1/Lake and unchanged manifest; independent writable build
directory; targeted imports; all four public modules compiled. Finite explicit
checks use kernel `decide`, not native-decide or an added axiom. Parent imports
all public modules and performs the ONE final whole B017 build, official axiom
audit and complete current-source guard before/after. No duplicate full builds,
remote publishing, queue changes or reviewer activity were performed here.
