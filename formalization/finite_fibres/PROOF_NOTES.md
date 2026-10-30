# B042 — finite symmetric CCO, binary covers and real algebraicity

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Twelve definitions, 50 claims and eight tasks prepare FOUR selected new
Foundations I results: `lem:bip`, `cor:twogroup`, `cor:hasse`, and
`cor:fibre-uniform-acl`. There are no new labelled equation exports.
The existing `lem:fibreCCO` is already prepared in `canonical_hull`;
select ONLY its C09/C10 orbit/homogeneity/CCO proofs. Do not import C03
triangle fullness or that module's later Hasse-dependent conclusions.

The other import is ONLY `parity_hasse` C05, the internally proved finite
high-girth/high-chromatic graph theorem. Its earlier finite graph proof
does not use the original source or Hasse theorem. Cauchy and the finite
p-group normalizer/maximal-index support are proved HERE. No new external
Erdős/Cauchy provider, circular Hasse theorem or Lean certificate is added.

## N01: Monochromatic odd cycles, high girth and a binary palette code

**D01–D03/D12; C01–C08.** For each symmetric diversity atom a form the
actual finite undirected simple graph on F. Symmetry permits reversing
an edge and irreflexivity excludes loops. If this graph is not bipartite,
a breadth-first parity conflict yields a simple odd a-cycle of some
length r≥3. Thus |F|≥r≥3; empty/singleton targets and unused atoms have
no such obstruction.

Choose the already proved internal graph H with girth greater than r
and chromatic number greater than |F|. Its positive parameters are
justified by the odd cycle. Colour every specified H-edge a and leave
other pairs unspecified. Every specified simple H-cycle has a target
homomorphism: an even cycle alternates between endpoints of one a-edge;
an odd cycle of length m has m>r, so traverse the fixed r-cycle and add
`(m-r)/2` backtracking excursions. The closed walk has exactly m edges.
Backtracking preserves a because a is SYMMETRIC. Repeated target points
are permitted by semantic HOMOMORPHIC CCO.

Applying finite-target CCO gives a homomorphism H→F. Adjacent vertices
have distinct images because a is irreflexive, making this a proper
colouring of H by at most |F| vertices, a contradiction. Thus every
atom graph is bipartite. No transitivity, homogeneity, connectedness,
SAP or injective completion is used in this argument.

There is also an independent useful cardinal bound. Let D_F be the
finite set of occurring diversity colours. Choose ANY proper 2-colouring
`c_a:F→{0,1}` of each atom graph and define

\[
 x\longmapsto (c_a(x))_{a\in\mathcal D_F}.
\]

For x≠y their unique actual colour a makes `c_a(x)≠c_a(y)`, so this
code is injective. Consequently `|F|≤2^|D_F|`, even WITHOUT transitivity
or homogeneity. Component flips need no coherence, invariance or canonical
choice. Unused names can be omitted; no occurring colour means at most
one point. This stronger bound is internal proof support, not an extra
numbered source result. It does not by itself make |F| a power of two.

## N02: Expand Cauchy by cyclic tuple counting, then exclude odd automorphisms

**D04; C09–C15.** Let K be any finite group and p prime dividing |K|.
Count the tuples `(g1,...,gp)` with product one. The first p−1 entries
are arbitrary and uniquely determine the last, so their number is
`|K|^(p-1)`, divisible by p. Cyclic rotation preserves this set, even
for noncommutative K, because

\[
 g_2\cdots g_p g_1
   =g_1^{-1}(g_1\cdots g_p)g_1=1.
\]

Every rotation orbit has size one or p. A nonzero shorter period modulo
the prime p generates all shifts, so a fixed tuple is exactly a constant
tuple `(g,...,g)` with `g^p=1`. The number of fixed tuples is congruent
to the total count modulo p. It is positive (the identity tuple), hence
at least p. A second fixed tuple gives nonidentity g of order exactly p.
This proves the needed Cauchy statement rather than assuming it.

A finite group has positive order. Factoring out all powers of two
leaves either one or an odd integer greater than one, whose least
nontrivial divisor is an odd prime. Thus a finite group whose order is
not a power of two has an odd prime divisor; order one is 2^0.

Apply this to ACTUAL Aut(F), a finite permutation group. An automorphism
sigma of odd prime order p is a nonidentity PERMUTATION, so it moves
some x. Its orbit has p distinct points. Every consecutive pair,
including `(sigma^(p-1)x,x)`, has the colour of `(x,sigma x)` because
sigma preserves the complete named structure. They form a monochromatic
simple odd cycle, impossible by N01. Therefore `|Aut(F)|=2^k`.

The moved-point step uses actual permutation faithfulness. This does
not impose faithfulness on the unrelated generic actions in N04.
Target transitivity/homogeneity are still unnecessary. The short source
corollary inherits SYMMETRY from the preceding finite-target context.

## N03: Prove the finite p-group normalizer and maximal index facts locally

**D05; C16–C20.** Let L be a finite group of order p^k and H<L.
Elementary left-coset partitions show |H| and [L:H] are powers of p.
Have H act by left multiplication on L/H. Every orbit is in bijection
with `H/Stab_H(c)`, hence has p-power size. Nonfixed orbits have size
divisible by p; the total coset count is divisible by p because H is
proper.

A coset gH is fixed by H exactly when `g⁻¹Hg⊆H`. These two finite
subgroups have equal size, so containment means equality. Fixed cosets
therefore are precisely `N_L(H)/H`. At least H itself is fixed. The
orbit partition says the fixed-coset count is divisible by p, hence at
least p. This proves the normalizer condition `H<N_L(H)`.

If H is maximal proper, its normalizer must be all L, so H is normal
and L/H is a nontrivial p-group. If its order were p^j with j>1, the
Cauchy proof N02 would give an order-p subgroup, nontrivial and proper;
its inverse image would lie strictly between H and L. Contradiction.
Thus `[L:H]=p`, and in particular a maximal subgroup of a finite 2-group
has index two. No source CCO, symmetry, Hasse theorem or external group
result has been imported into this support proof.

## N04: Nonfaithful transitive actions, invariant equivalences and covers

**D06/D07; C21–C27.** Let any group G act transitively on nonempty
finite Omega, choose x and put K=G_x. Invariance and the equivalence
laws make `H_U={g:gx U x}` a subgroup containing K: products follow by
translating `hx U x` by g and using `gx U x`; inverses follow similarly.

Transitivity gives the equivariant bijection `G/K→Omega`, `gK↦gx`.
For every K≤H≤G take the kernel of `G/K→G/H`. This is an invariant
equivalence and recovers H. Conversely translating pairs to x recovers
U from H_U. Thus invariant equivalences correspond inclusively to ALL
subgroups between K and G. Neither the action kernel nor nonnormality
of K causes a problem; no faithfulness or normality is required.

For U≤V, map `hH_U` to the U-class of hx. This bijects H_V/H_U with
the U-classes in V(x): equality of U-classes is exactly membership of
the relative group element in H_U, and every V-point has a transitive
G representative belonging to H_V. Translation transports the bijection
to every V-class. Therefore

\[
 [V:U]=[H_V:H_U].
\]

If U<V is a Hasse cover, an intermediate subgroup between H_U and H_V
would automatically contain K and give an intermediate invariant
equivalence. Hence H_U is maximal proper in H_V.

Now specialize to nonempty TRANSITIVE finite symmetric CCO F and
G=Aut(F). N02 makes G a finite 2-group, so H_V is one too. N03 gives
`[H_V:H_U]=2`, and the explicit class/coset bijection gives `[V:U]=2`
uniformly. This is for ALL invariant equivalences, not only exact ones.
No homogeneous-target assumption, SAP, AP-only Hasse theorem or arbitrary
imaginary inheritance is included.

## N05: Power-of-two fibre cardinality and the named colour bound

**D08; C31–C35/C43.** On a finite nonempty transitive target, choose
a saturated chain of invariant equivalences from Id to top. The lattice
is finite, so such a chain exists; a singleton has zero steps. In a
symmetric CCO target N04 makes every step index two. Relative class
counts telescope from one-point classes to the whole set, giving
`|F|=2^m`. Homogeneity is NOT needed for this power-of-two conclusion.

For the source's chain-to-palette proof, additionally use induced
homogeneity. Two ordered distinct pairs of the SAME named colour are
an induced two-point isomorphism; constant unary data and the converse
colours agree. Homogeneity extends it, so that colour is precisely one
FULL Aut(F) pair orbital. The diagonal is one orbit by transitivity,
and different named colours cannot merge under automorphisms.

Every invariant equivalence is a union of these full orbitals. Each
strict chain step adds an off-diagonal pair (all equivalences already
contain equality), hence a whole previously absent named diversity
colour. Different steps have disjoint differences, so they add distinct
colours. Thus `m≤d_F`. For an actual fibre, `d_F≤d`, the original named
diversity palette size. This explicit colour/orbital recognition justifies
the source's step count; coarse unnamed relation unions cannot replace it.

As an independent route, N01 already gives `|F|≤2^d_F` by binary codes.
Combine with `|F|=2^m` and strict monotonicity of powers of two to get
`m≤d_F` WITHOUT homogeneity. Both arguments are expanded; this optional
stronger support is not counted as another numbered article result.

## N06: Actual real fibres, spoke vectors and the uniform acl formula

**D09–D11; C29/C30/C36–C42.** Return to an INHABITED transitive
ultrahomogeneous original symmetric binary source M with FINITE palette
D of size d and original semantic HOM CCO. Let A be a finite complete
REAL base. I02 C09 identifies each realized outside one-point fibre
X_q with an actual full pointwise-stabilizer orbit. Its defining formula
is a finite conjunction of the spoke atoms and inequalities to anchors.
Thus an outside point is algebraic exactly when its fibre is finite;
every anchor is fixed. This matches usual real algebraicity: a finite
definable orbit witnesses it, and any finite definable set invariant over
A contains whole finite orbits.

I02 C09/C10 also give nonempty transitivity, induced homogeneity and
semantic HOM CCO of the ACTUAL real fibre. A finite fibre therefore
meets all finite support hypotheses of N05. Its actual palette uses at
most d old diversity colours, giving size `2^m`, `0≤m≤d`. There is
NO import of C03 triangle fullness or that module's later Hasse result;
the finite Hasse proof above is independent.

For `n=|A|≥1`, enumerate the anchors. Every outside point gives an
n-vector of diversity colours in D^n. Complete original binarity and
one-sort transitivity make this vector determine its qf type over the
fixed base, so there are at most d^n realized outside types. The finite
fibres are disjoint and acl is the anchors together with those fibres.
Summing their sizes gives

\[
 |\operatorname{acl}_M(A)|\le n+d^n2^d.
\]

This proves local real algebraic-closure finiteness uniformly in base
size and the finite palette. It is not a bound for tuple types, arbitrary
hidden parameters, higher-arity signatures or extra functions.

For empty A, use a separate argument. If M is infinite, its single
full-Aut orbit is infinite, so real acl(empty) is empty. If M is finite,
apply N05 to M itself: inhabitedness gives `|M|=2^m≤2^d`, and its real
acl(empty) is all M. No `d^0` counting formula is needed. When d=0,
completeness forces inhabited M to be a singleton; for n≥1 outside
types are absent and `0^n=0`. The empty-base branch never uses `0^0`.

## N07: Scope guards, explicit boundary structures and finite controls

**C28/C44–C50.** Empty/singleton finite targets have trivial automorphism
group and no proper invariant cover. The empty-base M statement retains
inhabitedness so it does not call zero a power of two. A generic C2 action
swapping 0,1 and fixing 2 has the invariant cover
`Id < {{0,1},{2}}`, with local counts two and one; transitivity is needed
for a uniform index. This is an ACTION example, not a CCO-source claim.

Symmetry is essential. On Z/3 name the two oriented nonzero difference
colours. Partial constraints are mod-three potential equations. If all
specified simple cycles admit homomorphisms, their oriented sums vanish;
integrating along a spanning forest supplies a homomorphism of the whole
diagram. Its full automorphism group is translations C3. This lies
outside the symmetric premise inherited by both source corollaries.

The complete one-colour K3 is not HOM CCO by N01. A concrete finite
diagnostic is the triangle-free 4-chromatic Mycielski graph of C5:
each simple cycle folds into K3 by the even/odd walk construction, yet
the whole graph cannot. The script explicitly checks this finite graph,
not a black-box high-girth existence theorem.

A 2-group conclusion is not an elementary-abelian, exponent-two or
regularity assertion; the support proofs allow D8/Q8 and nonfaithful
coset actions. Actual real one-point fibre inheritance is not CCO for
arbitrary nonexact quotients or tuple imaginaries, and the real bound
does not describe a hidden owner-kernel group. No SAP is added.

Finite palette is substantive. On the countable direct sum of F2
coordinates name EVERY nonzero difference g as `R_g(x,y) ⇔ y=x+g`.
All atoms are symmetric. Any nonempty partial isomorphism is a translation,
so the complete binary structure is transitive homogeneous. A finite
partial diagram is a system of difference equations; all simple cycle
sums vanish exactly when a spanning-forest potential assignment solves
the system. Thus it has semantic HOM CCO. Nevertheless every point is
uniquely definable over one real anchor by its difference atom, so its
real acl is the ENTIRE infinite carrier. This is outside the finite
palette premise, despite all outside one-point fibres being singletons.

Finite controls independently calculate symmetric atom graphs, actual
permutation automorphisms, odd-prime cycles, Cauchy tuple rotation,
p-group normalizers/cosets, invariant covers and nonfaithful indices.
Further controls compute full automorphism groups, actual real fibres,
named pair orbitals, binary codes and acl bounds in finite models.
These checks do not certify unbounded high-girth existence, general CCO,
SAP or Lean proofs. All 93 frozen source hashes, five HN/HKN receiving
bindings, provider-cache plan, prior source qualifications and overall
source-relative EPPA status stay unchanged.
