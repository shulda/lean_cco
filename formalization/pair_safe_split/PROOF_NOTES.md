# B047 — actual SAP-preserving safe splits and finite terminalisation

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Twelve definitions, 59 human proof claims, TEN selected remaining pair-level
Ramsey I results, FIVE equations and eight tasks. The first three results
of the finite-cover file were prepared by B046; the final two detour/full-
language results are outside this package. No Lean proof is claimed.

This preparation repairs a significant proof-interface omission: a FULL
represented EPP proof cannot be read as a STRONG diversity EPP proof simply
by deleting logical identity. The actual standing character construction
has the needed bridge from original SAP; it is proved in N04B. Actual SAP
of the marked age also has a direct proof in N05, BEFORE any new-source
STRONG calculus is used. The generic reading of a sector with just three
properties is not exported without the standing actual/FULL-triangle context.

## N01: STRONG saturation with a nonempty common meet

**D01/D02; C01–C03.** Work solely in the STRONG exact calculus for this
lemma. All gate palettes and exact domains are nonempty, and the common
finite intersection D of the D_i is NONEMPTY. Distribute left multiplication
by K_a^circ over that meet. Exact convolution makes all products exact and
their meet nonempty. Distribute right multiplication by K_b^circ over this
new nonempty meet. The result is exactly

    meet_i(K_a^circ * D_i * K_b^circ)
        = K_a^circ * (meet_i D_i) * K_b^circ.

Every multiplication uses distinct formal triangle vertices and diversity
outputs. This statement is not the FULL RAW saturation theorem, inserts no
logical Id as an extra diversity atom, and makes no claim for an empty
common meet or for an AP-only source. Its proof imports only the existing
STRONG nonempty distributivity/convolution export.

## N02: Represented closure separation and the actual identity base

**D03; C04/C05.** For the full represented closure theorem, apply the
existing relative-K closure-separation theorem with the ACTUAL shadow's
own equality. If full exact symmetric A,B contain equality and meet only
there, their stable exact-equivalence closures meet only there.

When this shadow is an actual quotient, its logical equality pulls back
to the WHOLE original kernel K, not necessarily old real Id. Apply the
relative-K theorem directly to the original full K-bisaturated relations.
All products and intersections are actual represented ones; no artificial
unit is adjoined to an off-diagonal product. This reading needs only full
exact inverse-image compatibility, not arbitrary mixed exact descent.

## N03: The original maximal gate, rigid groupoid and actual character

**D04–D06; C06–C14.** Visible original SAP parity gives a reachable layer
Y<X, [X:Y]=2, where Y>Id and its diversity part is nonempty. The full even
Y and odd O remain positive represented word relations. Choose maximal
original full exact K_*>=Y with K_* intersect X=Y. The earlier maximal-gate
theorem gives t_*=K_*;O;K_*, with t_*;t_*=K_* and index two above K_*.
It also gives ORIGINAL dominance: every original full exact equivalence
strictly above K_* contains t_*.

The previously expanded rigid groupoid gives one reached kernel K_s per
old named sort, actual quotient-functional bridges, finite connected hom-
torsors, elementary abelian isotropy and free action on quotient points.
Conjugating through a bridge transports t_* and original dominance. The
quotient dominance conclusion follows by inverse image of exact quotient
relations; no arbitrary old-to-quotient exact descent is used.

A coordinate functional on the elementary abelian isotropy with value one
at t_* defines the groupoid character through fixed connectors. Thus
chi(RS)=chi(R)+chi(S), chi(identity)=0 and chi(t_s)=1. One seed bit per free
action orbit propagates a simultaneous global labeling of actual quotient
points. Pulled back to reals, bits are constant on original K_s-classes.
Rigid actual orbital cylinders force their character difference; nonrigid
ones join different action orbits and admit both differences. Inactive
sorts have constant bit zero, and with an inactive endpoint the full old
palette is allowed. Original logical identity is allowed only at the same
sort and equal bits, while K_s also has diversity support.

Represented rigid-product factorisation remains a separate earlier export.
If a nonempty represented product lies in one rigid bridge, it factors
through two compatible bridges. The intermediate kernel is constructed;
if its sort were inactive, the new bridge would reach it, contradiction.
Thus both input character equations can be used in the totality proof.

## N04: FULL phase totality and FULL EPP use RAW saturation

**C15–C21.** FULL totality is exactly the earlier actual AP character
argument: nonrigid outputs are flexible; an entirely wrong rigid output
saturates to an affine coset dS. Original dominance kills S<=ker chi when
S is nontrivial, and bridge factorisation contradicts the wrong character
when S=1. This can yield Id as an allowed endpoint output. It is not yet
STRONG totality or a proof of SAP.

For FULL represented profiles P_i with nonempty common meet in a
particular deterministic sheet, suppose no individual P_i lies there.
Each P_i then meets the opposite allowed mask, because nonrigid atoms are
allowed. Existing full mask-primality says their intersection also meets
that mask, contradiction. This is the full typed-EPP implication.

Its expanded source proof saturates E_i=K_a;P_i;K_b and needs the FULL RAW
nonempty saturation theorem, not N01. The common exact domain is an affine
rigid slice; the original maximal gate makes it one whole bridge d. Right-
translate by d^op. Nonempty full meet distribution gives common intersection
WHOLE K_a. A minimal family gives A,B strictly above K_a with A intersect
B=K_a. Their stable closures meet in K_a by N02, yet both contain t_a by
original dominance, contradiction.

The frozen text currently cites `lem:exact-saturation-intersection`, whose
statement is explicitly STRONG, at this FULL represented step. The proper
provider is `lem:full-typed-exact-saturation`. This cross-calculus reference
is queued for the human article pass, and locally repaired here using the
already proved RAW theorem. No new axiom is introduced. A zero-member FULL
family has intersection typed Top; the actual nontrivial character has both
sheets, so Top is not confined to one deterministic sheet.

Do not now delete Id and claim the STRONG theorem. A RAW common meet might
contain Id as well as a nonempty phase-one diversity part. The extra
hypothesis needed to exclude that case is proved next, from old SAP.

## N04B: The additional original-SAP bridge proves actual STRONG EPP

**C55–C59.** In an actual homogeneous finite binary SAP source, two
nontrivial invariant equivalences E,F cannot meet in Id. They are definable
unions of named pair orbitals. If their meet were Id, choose x, another
a in E[x], and another b in F[x]. The meet condition makes x,a,b distinct.
The intersection E[a] intersect F[b] consists of the unique point x. This
is a finite definable set over {a,b} containing a point outside that base,
contradicting the old SAP infinite-stabilizer-orbit theorem.

Now take a finite family of nonempty original STRONG positive-word profiles
P_i. For each, use its corresponding FULL RAW word relation R_i. Original
SAP injectivisation gives P_i=R_i restricted to distinct endpoints. Thus
for D=meet_i R_i, its diversity slice is exactly meet_i P_i. A nonempty
strong common meet makes D a nonempty full exact relation.

If the strong meet lies in phase zero, a possible extra RAW Id is also
phase zero, so FULL EPP applies to D and hence to one R_j and its diversity
slice P_j. If the strong meet lies in phase one and D has no Id, FULL EPP
again applies directly. Across different original endpoint sorts no Id
exists, so that case is direct too.

The remaining dangerous case is same-sort D containing Id with nonempty
diversity slice wholly in phase one. The original gate K_s is phase zero,
so D intersect K_s=Id. Same-sort symmetry makes D symmetric. Both are full
exact, containing equality. Relative-Id closure separation gives

    <D> intersect K_s = Id.

Since D has a nonempty diversity part, <D>>Id. Every reached K_s>Id, as
proved independently in N05 using only old SAP. Therefore <D> and K_s
would be two nontrivial invariant equivalences meeting in Id, contrary to
the first paragraph. This dangerous case is impossible. The actual STRONG
typed-EPP theorem follows, with a real proof of the extra-diagonal bridge.
It is not a formal consequence of deleting Id from FULL EPP.

The empty-family strong palette contains both characters: for the same
active sort K_s has diversity support and t_s has phase one; for different
active sorts a bridge R and its translate t_s R realize opposite characters.
Thus the empty family cannot satisfy the one-sheet hypothesis either.

## N05: Direct actual SAP of the marked age before STRONG readout

**D07/D08; C22–C33.** Original SAP gives infinite Aut(M/A) orbits outside
every finite real A. In the finite complete binary language each realized
one-point qf fibre is definable by sort, spoke atoms and inequalities.
Hence every finite definable set over A is contained in A.

The source gate K_*>=Y>Id has infinite classes: a finite nontrivial class
would give an algebraic point outside a singleton base. No reached K_s
can be old equality. On the source named sort, path-independent reached
kernels would force K_s=K_*. On a different named sort, a bridge from K_*
to an equality gate would define ONE real target point from each source
point. It is in a disjoint named sort and therefore outside that singleton
base, contradicting original SAP. Thus K_s>Id on every active sort, and
the same singleton-base argument makes all its classes infinite.

Fix finite real A and x outside A, in an active sort. Let S be its old
realized complete one-point fibre and C=K_s[x]. We claim S intersect C
is INFINITE. If it were finite nonempty, choose y in the infinite C outside
S union A. Then

    S intersect K_s[y]

is a finite set definable over A union {y}, contains x, and x lies outside
that base. This contradicts original SAP. This proves the required infinite
type/gate intersection without any new-source SAP or full marked algebra.

Realize a given finite legal marked A+x in ONE actual global seed marking
of M. Every point of S intersect K_s[x] has the same active bit as x,
since labels are constant on K_s-classes. Its old type over A is also the
same. Thus arbitrarily many points have the same expanded one-point type
over A in that ONE marking. Inactive x use the old infinite orbit S,
since their bit is constant.

The existing AP-only character-completion theorem gives the legal finite
marked age with AP/JEP/HP, reasonableness and precompactness, and constructs
its homogeneous marked Fraisse limit H. Its old reduct is M and it has
HOM CCO. An arbitrary global seed marking is not asserted homogeneous.
Embed the finite structure on A+x and N same-type witnesses into H, then
use actual marked homogeneity to align its A+x with the original copy.
Every witness is in the full Aut(H/A) orbit of x. This proves that orbit
infinite for every finite A and x outside A.

Specialize the earlier hereditary unary SAP criterion to the relational
H with NO functions. Every finite A is then closed and cl(A)=A. Infinite
off-base orbits imply SAP, by one simultaneous avoidance automorphism and
the induced union. This is SAP of the ENTIRE marked age. It is not a
substitution of a point-generated hidden-base criterion and is not merely
renaming the prior AP result.

## N06: Actual FULL triangle age and the lifted STRONG normal form

**D09/D12; C34–C40.** A complete locally legal marked diagram has an
actual old-age reduct by the standing FULL old triangle-definedness. Its
pair masks give precisely all finite global phase-extension tests, so it
is an object of the legal marked age. The converse is restriction. Include
actual unary/pair admissibility for fewer than three points. Thus the
actual marked age is the FULL lifted triangle class, not an arbitrary
subclass with the same binary table.

Its full represented pair products are precisely old represented products
restricted by the actual endpoint masks: realized triangles are exactly
old triangles whose labels pass those masks. The earlier B044 full path
normal form, imported as the strict proved C21 ancestor of its completion
export, therefore computes actual full marked word profiles. It includes
possible Id outputs and uses the actual two endpoint bits, retaining fixed
inactive labels.

Only NOW use injectivisation at BOTH sources. Original SAP was a premise;
new SAP was independently proved in N05. Each actual positive STRONG word
profile is its represented word profile guarded by distinct endpoints.
Apply that guard to both sides of the full normal form to obtain

    L_strong(w) = P_old,strong(w) intersect A^(epsilon0,epsilon_n).

This is the advertised STRONG normal form, obtained without a circular
assumption of lifted SAP or STRONG EPP. The independent actual STRONG EPP
proof of N04B is also available.

All legal STRONG lifted forks have genuine diversity outputs: strongly
amalgamate their actual two-point input structures over the common middle
vertex, using the NEW SAP just proved. The outer vertices are distinct,
so their output is diversity. This is stronger than FULL totality with
an Id-only possible output. At the actual new homogeneous SAP source,
the earlier STRONG Set-Pasch/associativity API applies. Actual triangle
permutations give typed Peirce with the correct converse. Its actual HOM
CCO plus SAP likewise gives positive STRONG profile 2-Helly. Thus every
conclusion of the phase-sufficiency result holds for this actual instance.

The printed lemma's three sector properties are read with its standing
actual character/FULL triangle context. We do not export a theorem about
an arbitrary reduct-surjective marked subclass based only on those three
words. A separate purely abstract criterion would need its FULL class and
appropriate table laws stated and proved independently.

## N07: Safe split, whole-expanded orbitals and finite descent

**D10/D11; C41–C51.** The selected odd O lies inside t_*, whose character
is one, while Y<=K_* has character zero. Thus the actual chosen parity
layer is oriented. Every transported t_s moves an actual quotient point
to a distinct one of opposite bit; real representatives give a legal
marked pair. Both active child sorts are consequently nonempty in H.

The resulting source is actual homogeneous, finite complete binary and
FULL triangle-defined, retaining inherited same-sort symmetry. It has
SAP by N05 and HOM CCO by the earlier AP construction, is reasonable,
reduct-surjective and precompact, and has unchanged old reduct. Inactive
sorts have constant bit zero. No arbitrary preassigned two-cover is
asserted safely orientable.

Homogeneity of the WHOLE expanded H identifies each old named colour on
a fixed ordered pair of child sorts with one full new pair orbital;
singleton homogeneity makes realized children transitive. In particular
within each active child no old colour can split into several orbitals.
An old diversity atom in the transported t_s always has phase one, hence
is absent inside BOTH equal-bit children. These facts discharge every
hypothesis of the already expanded conditional rank lemma. Therefore

    Phi=sum_a 3^(k_a)

strictly decreases at each genuine split. Both children are nonempty;
each contributes at most 3^(k_a-1), so together less than the parent's
3^(k_a). This is a whole-expanded orbital assertion, not a claim about
arbitrary nonhomogeneous unary seed markings.

All structural premises are retained at the CURRENT source, so repeat
whenever a proper finite-relative-index interval remains. The integer
Phi cannot descend infinitely. Any residual finite-index interval would
permit another split; hence termination has no such interval, and in
particular all proper same-sort invariant covers have infinite relative
index. Finite unary compositions preserve reasonableness by successive
lifts, reduct-surjectivity by successive choices and precompactness by
finite multiplication. No function-adding restriction issue occurs.
The result has SAP/HOM CCO, unlike the earlier AP-only theorem whose
numerical potential was the same. No later full-language or terminal
Ramsey result has been used.

## N08: Source qualifications, boundaries and finite controls

**C21/C52–C54.** Two article-pass points are explicit. First, FULL EPP
needs RAW nonempty saturation, not the separately stated STRONG saturation
lemma. Second, the phase-sufficiency statement is prepared in its intended
standing actual-character/FULL triangle context. The actual STRONG EPP
bridge and direct marked SAP proof fill the nontrivial proof interface;
they introduce no new hypothesis or external theorem provider for the
standing actual construction. They should be written into the human proof.

The standing FULL context has a concrete boundary. Start with an infinite
pure old set (one diversity colour) and select exactly THREE points by a
new unary predicate P. This unary structure is homogeneous, its finite age
is reduct-surjective, and every typed three-vertex fork is realized: each
child has at least three points. At the one-colour table level the profiles
are singleton and the deterministic-sheet EPP antecedent can be vacuous.
Nevertheless the age forbids a complete four-P object even though all its
triangles occur. It fails SAP over a two-P base: two one-point P-extensions
would require four distinct P points in a strong amalgam. Thus reduct-
surjectivity and local table statements do not replace the FULL triangle
class premise. This is an OUTSIDE-actual-character example, not a counter-
example to the maximal-exact construction proved above.

The finite controls use an actual block/bit/clone model: vertices
(block,bit,index), colours clone/even, opposite-bit-within-block, and far
between different blocks. Its safe character names the bit. The finite
windows have enough blocks and clone indices only for the bounded sizes
checked. Full odd-square includes Id and clone; STRONG odd-square is
clone only, so the two products are genuinely distinguished. Controls
check nonempty saturation in each calculus, legal marked words, lifted
STRONG associativity and Helly, finite type/gate witnesses, strong marked
spans with fresh clone indices and rank decrease. The dangerous Id plus
phase-one menu is not an exact domain of this model.

These calculations do not prove infinite gate/type intersections, the
general no-orthogonal-equivalences theorem, arbitrary abstract sector
sufficiency, unbounded SAP/CCO, new published-provider binding or a Lean
proof. Empty real bases, inactive sorts, isolated/small finite diagrams
and actual pair admissibility are retained throughout. All source TeX
remains unchanged, and all five existing HN/HKN receiving bindings remain.
