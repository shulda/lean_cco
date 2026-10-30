# B046 — orbital parity, full invariant covers and the bad diagonal split

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Eight definitions, 40 human claims and six tasks prepare THREE selected
Ramsey I results from `sections/v27/06_legacy_finite_covers.tex`:
`thm:orbital-parity`, `thm:finite-cover-two`, `prop:bad-diagonal-split`.
The orientation equation is the sole auxiliary export. The twelve later
results in the same file are not prepared or counted by this package.

Only three previously prepared exports are imported: original parity
`parity_hasse` C09–C12; original full invariant Hasse C13/C14; and actual
SAP injectivisation `strong_selectors` C04/C05. The explicit nine-colour
example is proved independently of these imports. No later safe-splitting
theorem, generic algebra-to-CCO theorem or new published input is assumed.
This is human proof preparation, not compiled Lean or certification.

## N01: Original RAW parity and its visible-SAP STRONG upgrade

**D01/D02; C01–C06.** Fix ONE current named original transitive sort
with its actual homogeneous symmetric binary structure and visible SAP.
Let E<F be an actual invariant interval of finite relative index, and t
an occurring diversity orbital in F minus E. The original SAP-free parity
provider applies to exactly this source. It gives stabilized positive
RAW even and odd t-words Y_t,O_t, with Y_t a full exact equivalence,
E_t=Y_t disjoint-union O_t contained in F, and [E_t:Y_t]=2. In particular
Y_t includes original logical identity, and O_t includes t and excludes
identity. No new quotient source or quotient SAP is involved.

The additional SAP statement needs its own argument. Realize t(x,y) and
strongly amalgamate two copies of this actual two-point diagram over y.
The new x-images x1,x2 are distinct and share a t-neighbour. Thus their
pair lies in t;t, hence in the stabilized even relation Y_t, and is not
logical identity. Therefore Y_t>Id. The odd sheet is already nonempty
because it contains t. Apply the SAP injectivisation provider to the
positive stabilized even/odd words: each STRONG simple-path profile is
precisely the distinct-endpoint slice of its represented RAW word. Thus
Y_t minus Id and O_t are nonempty STRONG reachable profiles.

Keep the two levels separate. The FULL RAW exact equivalence is Y_t,
not its identity-free diversity palette. Equality is an allowed RAW
endpoint output and is never inserted as an artificial diversity edge.
The SAP-free provider alone does not imply Y_t>Id: the two-copy SAP
argument is exactly the added input. No general collision-unfolding
lemma or stronger relative completion theorem is needed here.

## N02: Finite covers in the full invariant lattice

**D03; C07–C11.** For E<F a full invariant cover of finite relative
index on the current real sort, apply `parity_hasse` C13/C14. It gives
index two without SAP or exactness of E,F. This is the original full
invariant-lattice Hasse theorem, not a theorem only about finite targets
or an exact sublattice. Current source SAP is available but unnecessary.

For a finite-relative interval, choose a saturated chain: the invariant
equivalence lattice is finite because actual full pair orbitals are the
finitely many named colours plus the logical diagonal. Each subinterval
has finite index since its partition refines the given finite partition.
Transitivity makes relative block counts uniform, and partitioning a
larger block into intermediate blocks multiplies these counts. Every
strict cover contributes two, so the total is 2^m. An equality interval
has m=0 and index one.

This statement does NOT say any chosen two-cover can be oriented safely.
It does not assert reachability of its palette or preservation of AP by
an arbitrary unary orientation. The actual example below separates these
claims; its proof has no dependency on C01–C11 or their imports.

## N03: The actual nine-colour homogeneous triangle-defined SAP model

**D04/D05; C12–C18.** Let U,V,N be countably infinite pure sets and use
vertices (u,v,p,q,n), where p,q belong to F2. For distinct vertices, a
coordinate colour e_i means equal corresponding U/V block and bit
difference i; n means different blocks. There are nine pair colours in
{e0,e1,n} squared. Every combination occurs. The colour (e0,e0) is an
IRREFLEXIVE diversity colour between distinct clones of one owner
quadruple (u,v,p,q), while logical equality is a separate diagonal.

A finite induced partial isomorphism determines injections on the used
U-blocks and V-blocks, and one consistent p-shift on each used U-block
and q-shift on each used V-block. Indeed e0/e1 record precisely the
same-block relation and all signed bit differences. The (e0,e0) relation
records owner coincidences, so the partial maps on clone fibres are
injections. Extend the finite block injections to permutations of the
infinite pure sets, extend the chosen local shifts arbitrarily on unused
blocks, and extend every finite clone injection to a bijection of N.
This gives an actual automorphism extending the original map. It proves
homogeneity and, in particular, transitivity.

Homogeneity aligns any finite amalgamation span inside the source,
possibly with extra intersections. Keep the resulting owner coordinates,
and replace every off-base formal vertex by a fresh N-index in its owner
fibre. Preserve the actual base indices and use disjoint fresh indices
for the two sides. No pair colour changes. The two legs now intersect
exactly in the common base, proving SAP. This is the explicit clone
freshness argument; it does not presume an infinite supply in a fixed
finite diagnostic window.

For one coordinate the actual STRONG triangle product is

    e_i * e_j = {e_(i+j)},
    e_i * n = n * e_i = {n},
    n * n = {e0,e1,n}.

The last line uses a middle block different from both endpoints; infinite
U/V provides one. Distinct real witnesses with repeated coordinate values
use separate clone indices. The two coordinates are independent, so their
triple realizations combine into actual triples with fresh clone indices.

Now take a complete diagram all of whose triples are permitted. For one
coordinate, e-coloured pairs together with equality form an equivalence:
the e*e rule forces transitivity. Within one block, choose an anchor bit;
the allowed triangle rule forces every e_i label to equal the difference
of the resulting endpoint bits. Distinct blocks have n labels. This
reconstructs a coordinate realization, including singleton/two-point
blocks where no triangle argument is needed. Do this independently for
U,p and V,q. Give distinct formal vertices distinct N-indices when owners
coincide. The complete nine-colour diagram embeds inducedly. Thus the
actual triangle table defines precisely the age of the model.

## N04: Direct semantic CCO by coordinate potentials

**C19–C24.** A multiplication table and a Helly assertion are useful
checks, but we prove actual semantic HOM CCO directly. Let a finite
nine-colour partial graph have each specified simple cycle homomorphic
to M. Project its constraints to one coordinate. The e_i edges force
same block and signed F2 difference i, while n edges force different
blocks and impose no signed relation.

The signed equations in the e-edge subgraph are consistent. Otherwise
choose a closed e-walk of odd signed sum. Splitting at repeated vertices
shows some SIMPLE e-cycle has odd sum; immediate backtracking contributes
zero, so this is a genuine simple cycle of length at least three. The
corresponding specified old nine-colour cycle has no coordinate
homomorphism, contradicting the hypothesis.

No n edge can have both endpoints inside one e-component. A shortest
simple e-path between its endpoints together with the n edge would be a
specified simple cycle whose coordinate realization forces both equal
and unequal blocks. A one-edge e-path cannot occur because a simple
partial graph has one label per pair. Thus the resulting cycle has at
least three vertices.

Assign every e-component a fresh block from U and propagate its
consistent bit potential. Isolated vertices are singleton components.
All e_i edges now have their required difference, and every n edge joins
different assigned blocks. Repeat the construction independently for
V,q. Combine the two coordinate assignments and give all distinct formal
vertices distinct clone indices. This preserves every specified pair
colour, including (e0,e0) edges. It constructs a homomorphism of the WHOLE
partial graph. Necessity follows by restriction to each cycle. This proves
semantic HOM CCO independently of generic profile-to-completion results.

As an additional check, actual STRONG products in the nine-colour model
are Cartesian products of the two displayed coordinate products. The
coordinate reachable profiles are exactly the three singleton palettes
and top. Hence every positive word profile is a nonempty box. A finite
pairwise-intersecting family of singleton/top coordinate profiles meets
globally, and Cartesian boxes inherit this property coordinatewise. This
agrees with CCO, but it is not the premise of the direct proof above.

## N05: The coarse diagonal two-cover and every possible orientation

**D06/D07; C25–C28.** Define X by equality of u,v and K by equality of
u,v,p+q. The full equivalences include original logical equality in
addition to their diversity palettes:

    X = {e0,e1} x {e0,e1},
    K = {(e0,e0),(e1,e1)}.

Every X-block has exactly two K-blocks, indexed by p+q. Thus [X:K]=2.
There is no invariant intermediate equivalence. If one containing K
relates the two K-blocks in one X-block, equivalence transitivity merges
that whole X-block; source transitivity transports this merger to every
X-block, giving X. Otherwise the relation is K. This is a cover in the
FULL invariant lattice, not merely an exact sublattice.

The diagonal K diversity palette is not a Cartesian box: both projections
contain e0,e1 but the mixed pairs are omitted. Every positive reachable
STRONG word profile is a box by N04, so this coarse K palette is not such
a profile. The bad example therefore does not contradict selection by
reachable orbital profiles.

Let P be ANY orientation of the two K-classes inside every X-class. It
need not be definable, equivariant, homogeneous or coherent between blocks.
Constancy on K says it depends only on u,v and r=p+q; the two possible r
values have opposite labels. Put h(u,v)=P(u,v,0,0,n). This value is
independent of n. We have exactly

    P(u,v,p,q,n) = p+q+h(u,v).

This proves the labelled orientation equation for an arbitrary function h,
with no extra compatibility requirement.

## N06: A universal ordinary-AP obstruction, including cross-leg collisions

**C29–C35.** Choose u0 != u1, v0 != v1 and abbreviate h_ij=h(ui,vj).
For epsilon in F2 take fresh actual clones of

    b_epsilon = (u0,v0,epsilon,epsilon+h00),
    d         = (u1,v1,h11,0),
    z_epsilon = (u0,v1,epsilon,0).

The suppressed last coordinate is chosen in N. Both b_epsilon and d have
P-value zero. Their pair colour is (n,n), independent of epsilon. Hence
the marked bases {b0,d} and {b1,d} are induced-isomorphic. Each extension
triangle is an actual finite substructure of (M,P). Their two incident
colours are the same:

    col(b_epsilon,z_epsilon)=(e0,n),
    col(z_epsilon,d)=(n,e0),

but P(z_epsilon)=epsilon+h01, so their new vertices have opposite bits.

Suppose an ordinary AP amalgam of these two finite expanded legs exists.
First exclude identification of the two z-images: it would have to
preserve BOTH opposite unary labels, impossible. Each image also differs
from the base points because its own leg embeds. Thus the cross pair is
indeed a DIVERSITY pair. This step matters: ordinary AP does not itself
forbid cross-leg identification, and logical Id must not be silently
excluded merely by drawing distinct formal vertices.

The path through the common b-image gives the cross support
{e0} x {e0,e1,n}; the path through the common d-image gives
{e0,e1,n} x {e0}. Their intersection is exactly {(e0,e0)}. That colour
lies in K, so the orientation requires equal P-values at the two images,
contradicting their opposite labels. Thus no expanded-age AP amalgam
exists, even allowing all ordinary cross-leg collisions.

The calculation works for all values of h00,h01,h11, and uses neither h10
nor any values outside this rectangle. It therefore proves EVERY
orientation of this fixed coarse cover destroys AP. It is not merely a
bad choice of one orientation and does not rely on (M,P) being homogeneous.

## N07: Explicit compatible finer coordinate splits

**D08; C36–C39.** Let K0 fix the entire owner quadruple; its diversity
palette is {(e0,e0)}. Let Xp fix u,v,q and allow p to vary, and let Xq fix
u,v,p and allow q to vary. Both K0<Xp and K0<Xq have relative index two,
with their added colours the individual orbitals (e1,e0) and (e0,e1).
As above, source transitivity shows these are actual full invariant covers.

There are compatible good orientations: name P1=p, then P2=q. The first
label orients K0<Xp. Inside each resulting fixed-p child the second
orients the remaining second-coordinate interval. These choices exist
simultaneously on the full product. We do NOT claim every arbitrary
orientation of a finer cover is safe.

For homogeneity after naming p, the coordinate extension argument of N03
still works: a label-preserving partial map forces its p-shifts to zero
on used U-blocks, and choose zero on unused blocks. All other choices
remain. After naming q, likewise force q-shifts to zero on V-blocks.
Independent permutations of U,V and clone fibres still extend every
finite induced labelled map. The same fresh-clone argument preserves the
new labels and gives SAP at each prefix.

For CCO with named p, local legality of every e_i edge already says its
prescribed endpoint p-values differ by i. Assign each e-component a fresh
U-block and retain these prescribed bits; n edges cannot stay in one
component by the same shortest-path cycle obstruction as N04. Solve the
unnamed q coordinate by potentials as before. After naming q, treat both
coordinates by prescribed bits. Combine and give fresh clones. Complete
locally permitted labelled diagrams are reconstructed similarly, proving
triangle-definedness of these chosen prefix expansions. This proves the
substantive successful finer-split assertion explicitly, without importing
the later safe-character construction it is intended to motivate.

## N08: Acceptance, source clarification and diagnostic limits

**C40.** The example is countable, symmetric, complete, homogeneous,
triangle-defined, SAP and semantic HOM CCO. It has a full invariant coarse
index-two cover whose every orientation fails AP, and explicit finer
compatible successive splits that retain these positive properties.
It refutes orienting an arbitrary preselected two-cover; it does not
refute the later maximal exact character selection algorithm.

Independent reconstruction found no new source gap. The short source AP
argument implicitly excludes a collision z0=z1 by opposite marks; this is
now explicit. The source CCO-by-box-Helly sentence has been supplemented
by the actual coordinate-potential construction, avoiding any hidden
converse theorem. These are proof expansions, not changes to frozen TeX.

`tools/check_orbital_cover_controls.py` compares actual finite-window
nine-colour products with the coordinate table, independently compares
all one-coordinate partial graphs on at most four vertices against a
direct homomorphism search, checks complete nine-colour triangles,
prescribed coordinate bits, all sixteen assignments to the h-rectangle,
K-constancy, the forced cross support and the logical-Id escape. Finite
windows only provide enough witnesses for the stated bounded sizes.
They are not claimed to satisfy unbounded CCO/SAP or infinite clone
freshness, and they do not certify the original parity/Hasse theorem or
compiled Lean proofs. Existing source/provider obligations remain.
