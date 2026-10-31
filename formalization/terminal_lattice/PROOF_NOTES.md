# B050 — original modular lattices, quotient powers, reset and positive layers

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Twelve definitions, 68 claims, ELEVEN selected results, twelve equations and
nine tasks. This covers all nine results of source 08 and ONLY the quotient
STRONG semigroup and original positive-layer theorem from source 09.
No B049 theorem is imported: the narrow same-J saturation support below is
local, so B049 can safely import these two source-09 exports.

This is human proof preparation, not Lean or global certification. Invariance
always refers to the ambient ORIGINAL automorphism group acting on the
selected real sort and its quotient, not an independently enlarged group.

## N01: Same-sort RAW commutation and modularity

**D01/D02; C01–C03.** Every invariant same-sort relation is a union of
symmetric old pair orbitals, including the diagonal where appropriate.
Its represented product with another such relation is also invariant and
therefore symmetric. Since (P;Q)^op=Q;P, actual equality-inclusive RAW
relations commute. One can also extend the complete two-point endpoint
swap; equality cases cause no problem. Nothing here commutes cross-sort
letters or uses CCO, SAP, NR2, exactness or distributivity.

The product of commuting invariant equivalences is itself an equivalence:
(EF)^2=E(FE)F=E^2F^2=EF. It contains both and is contained in any equivalence
containing them, so it is their join. To prove modularity for E<=G, take
x(E join F)y with xGy and choose z with xEzFy. Since xGz and xGy, also
zGy. Thus x(E join(F meet G))y. The reverse inclusion is monotonicity.
This is the FULL original invariant-equivalence lattice, not an exact
sublattice.

## N02: Internal modular diamond extraction and an actual RAW-word obstruction

**D03/D04; C04–C09/C55/C62/C63/C67.** The finite modular nondistributive
criterion needs no new theorem oracle. For lattice elements a,b,c put

    l=(a meet b) join(a meet c) join(b meet c),
    h=(a join b) meet(a join c) meet(b join c).

In a modular lattice, a join l=a join(b meet c), and similarly for b.
Dedekind's law twice gives

    (a join l) meet(b join l)
      =(a meet c) join[b meet(a join(b meet c))]
      =(a meet c) join(b meet c) join(a meet b)=l.

The dual calculation gives (a meet h) join(b meet h)=h. Since l<=h,
modularity identifies a_hat=(a join l) meet h=(a meet h) join l. Cyclically,
the three normalized elements have pairwise meet l and join h. Choose a
nondistributivity witness

    a meet(b join c) > (a meet b) join(a meet c).

Here a meet h is the left side and a meet l is the right side, so l=h is
impossible. Thus l<h and the three normalized elements are distinct,
strictly interior, and form a genuine M3 sublattice.

For the actual original word obstruction take E1,E2,E3 with pairwise meet L
and join H. Choose x E1 y but not xLy, and let A=E1[x], B=E2[x], C=E3[y].
Then x is in A meet B, y in A meet C, and E2;E3=H gives B meet C nonempty.
But A meet B=L[x], A meet C=L[y], and these L-classes are disjoint.
The three classes therefore meet pairwise but not globally.

Use ONE actual RAW old atomic word for each E_i. Delete genuine logical
Id letters. A nonidentity E_i cannot reduce to an empty word, and cannot
be a single irreflexive diversity atom while containing equality. Attach
private paths from root z to centre x for E1,E2 and to centre y for E3,
with the actual complete fine pair xy retained. Every specified simple
cycle uses two private paths, joined either at their common centre or by
xy. The appropriate pairwise class intersection gives an actual old root
witness. Align the centre pair by old two-point homogeneity, then realize
the word walks independently. Repeated nonadjacent images are allowed.

Any whole homomorphism would preserve xy; after aligning it to actual x,y,
its root would lie in the empty A meet B meet C. Thus this original finite
partial diagram has all cycles feasible but no whole homomorphism. No SAP
is used. Under FULL NR2, the earlier CCO-/SAP-free RAW word theorem supplies
words for EVERY invariant equivalence. Combine it with modular extraction
to get the nondistributive-nonCCO diagnostic. We import only its C25–C27
word support, never C28 distributivity. This explicitly discharges the
M3-word hypothesis of C08 when applying it in C09; it is not an extra
independent premise of the diagnostic. A distributive lattice alone is
not claimed sufficient for CCO.

## N03: Generic exact STRONG lifting of quotient composition

**D05; C10–C12/C57.** This standalone source-09 result needs original
homogeneous SAP and a nontrivial invariant J, but NO symmetry, FULL cover,
NR2, CCO or exactness. Repeat strong copies of a realized nontrivial J-pair
over the SAME anchor, embed their finite targets and align the anchor by
homogeneity. This makes every original J-class infinite.

For a quotient relation R define Phi(R) as its FULL preimage restricted
to DISTINCT old real endpoints. Since even equal quotient classes have
two distinct real representatives, Phi is injective and preserves unions
and intersections. Phi(Delta_Q)=J^circ is a nonempty OLD diversity palette,
not old logical equality.

Project an actual strong two-edge old path for one product inclusion.
Conversely for q R r S s and ANY pinned distinct x in q,z in s, choose
a fresh y in the infinite original class r. Full-preimage membership gives
x Phi(R) y Phi(S) z. Thus

    Phi(R)*Phi(S)=Phi(R;S).

For longer quotient walks choose each formal real representative fresh
from all earlier positions and the pinned endpoints. Quotient returns
to a class remain legitimate; old real occurrences are still distinct.
This proves the complete semigroup and Boolean assertions. The graph-cover
applications below instantiate this general fact using their nonzero J;
they do not add a cover premise to this generic export.

## N04: CCO-free powers at a FULL original cover

**D06/D07; C13–C20/C56/C66.** Let Id<J<K be a FULL invariant cover and
Theta one complete external OLD quotient G-orbital. Its undirected graph
has connectedness whose old preimage is an invariant equivalence strictly
above J and below K. The FULL cover makes connected components exactly
the K/J classes. If a component is bipartite, all are by transitivity.
The even-walk equivalence splits each component into two nonempty classes;
its old preimage lies between J and K. FULL cover forces it to be J, so
each parity class is a SINGLE quotient point and [K:J]=2. Conversely an
index-two cover has precisely those two-vertex components. Its odd powers
are Theta and its positive even powers the true quotient diagonal. N03
lifts them to T and J^circ as OLD STRONG diversity powers.

In the other case each component is nonbipartite. Between any q,r in it,
including q=r, an odd detour changes walk parity and two-edge backtracks
pad to every sufficiently large length. There are only finitely many
quotient OLD G-pair orbitals: project the finitely many old fine orbitals.
Choose one witness pair per quotient orbital and take the maximum of their
thresholds; equivariance makes that one threshold uniform for ALL pairs.
Thus Theta^n=K/J, INCLUDING quotient diagonal, for every sufficiently
large n. N03 lifts this to T^n=K^circ with the original fine endpoints
pinned. Every intermediate old J-class has arbitrarily many distinct
representatives. The reverse inclusion is K-transitivity.

No semantic CCO, global NR2, distributivity, exact-domain product law or
mixed-sort transport is used inside this power dichotomy. The FULL cover
is essential: a connected bipartite six-cycle has a proper intermediate
even-walk equivalence and alternating powers despite top index six.
For terminal relative powers, the earlier FULL NR2 RAW theorem is used
ONLY to identify the exact cover as a FULL cover and exclude its local
index-two case. The semantic cylinder is intrinsically the full preimage
of one quotient orbital; no B049 cylinder theorem is needed to define it.

## N05: Narrow same-cut saturation and positive complete-orbital words

**D08; C21–C23.** To avoid a package cycle, prove the narrow helper needed
here locally. For an old diversity atom t and nonzero J, a RAW witness
between distinct x,y has form xJu t vJy. If x=u, choose a fresh anchor
in J[x] and strongly duplicate x over the COMPLETE base consisting of
that anchor,v,y. The moved point x is excluded from this base because
t is diversity and x!=y. Its second copy u1 is different from x, still
in J[x] through the common anchor, and still t-related to v. If v=y,
similarly duplicate y over a fresh J-anchor and the other old points,
fixing x,u1. Now the two exterior steps are genuine J^circ diversity.
Apply old SAP injectivisation with x,y pinned to separate remaining
nonconsecutive occurrences. Hence

    (J;t;J)^circ=J^circ*{t}*J^circ.

The reverse inclusion is direct. This is INTERNAL same-J support, not a
duplicate allocation/export of B049's general typed saturation theorem.

A fine old atom t in a complete quotient orbital preimage T projects onto
that ENTIRE orbital by old pair homogeneity. Thus its whole J-saturation
is T. A given positive word for J^circ concatenated on both sides of t
therefore yields ONE positive OLD word for T. Private interiors may use
other original sorts. This observation requires only J positivity, not
K positivity or non-index-two; those are separate reset premises.

## N06: Absorption and individual theta-cycle feasibility

**D09; C24–C30/C59/C60.** For any nonempty D subset K^circ and distinct
xKz choose one fine atom d in D. Original transitivity supplies a d-neighbour
of z; SAP gives infinitely many such neighbours over z. Choose one avoiding
x,z. It witnesses xK^circ yDz, proving K^circ*D=K^circ; the reverse inclusion
is K-transitivity. The right-sided identity follows similarly. This uses
no CCO or exactness. Same-sort STRONG positive products commute by RAW
commutation plus old SAP injectivisation, and associate directly: glue the two witnessing triangles along their
complete common pair, align by old homogeneity, and SAP-injectivise the
resulting three-edge path with its root fine type pinned. Both
parenthesizations are exactly the four-distinct-point path spectrum.
No Set-Pasch or exact-product theorem is imported. No individual mixed-sort word letters are commuted.

In the separate theta guard each positive branch profile CONTAINS its
assigned nonempty menu. A cycle inside one gadget uses two branches
sharing an actual diversity endpoint atom, hence is feasible. A bare top
spoke specifies NO edge and is omitted. Any other simple cycle traverses
whole private root-to-root branches; otherwise a private vertex has no
exterior incidence. Two branches of the same gadget would close a cycle
there. Contracting therefore yields a SIMPLE root-skeleton cycle.

Through the centre, it uses two K^circ spokes and a nonempty graph path;
absorption gives a complementary endpoint spectrum containing K^circ,
meeting the closing spoke. Avoiding the centre, its length m exceeds
r(N-1)+1. Some label occurs at least N times. Close a DIFFERENT label if
available, otherwise any edge leaves m-1>=N copies. Commute/associate the
assigned SAME-SORT menus to collect T_i^N=K^circ; absorption makes their
whole complementary product K^circ. Actual branch spectra are supersets,
so it meets the closing branch's nonempty menu. Realize both paths over
one common actual fine endpoint pair. These are cycle-by-cycle witnesses,
not a global completion or simultaneous root colouring.

## N07: ONE global CCO completion produces a complete orbital reset

**D10; C31–C40.** Now use the original reset premises: FULL cover,
J>Id, local [K:J]!=2, and positive old words for BOTH J^circ and K^circ.
N05 gives positive words w_i for all complete external T_i. N04 gives
one common N for their eventual K^circ powers. Choose the previously
proved internal sparse labelled graph with r edge labels, fine old
K^circ atoms as vertex-colour palette, and girth>r(N-1)+1. It guarantees
ONE vertex colour with a monochromatic edge of EVERY label in any such
colouring.

Attach ONE positive w_K spoke from a fresh centre to each graph root,
and ONE positive w_i path on each i-edge. All interiors are private and
retain their original prescribed sorts. Every simple cycle traverses
whole paths. The centre and graph-cycle arguments of N06 apply directly
to these single paths, whose profiles equal their menus. Thus every
specified cycle is old homomorphic. This direct proof does not assume
the separate theta-presentation hypothesis A07.

Apply OLD semantic CCO ONCE to the WHOLE network, then old SAP injection
to separate all formal vertices. Only NOW define d_v=col(o,v), which lies
in K^circ by its positive spoke. The sparse graph gives one fine atom d
such that for every i some i-edge vw has d_v=d_w=d. Its actual triangle
yields (d*d) meet T_i nonempty. Since T_i is external to J, necessarily
d is external too.

Let m be the full preimage of the complete quotient orbital M0 containing
d. Narrow saturation gives m=J^circ*d*J^circ. N03 gives J^circ*m=m=m*J^circ:
Phi(Delta_Q) acts as a unit ONLY on full quotient preimages. Thus W=m*m
is J-bisaturated. It meets each complete external T_i, so invariance and
bisaturation force it to contain each whole T_i, hence K minus J.

It must also contain J^circ. Realize a d-edge xy and choose a fresh anchor
a in J[x]. SAP-duplicate x in the complete triangle {a,x,y} over the
complete pair {a,y}. Its distinct copies x,x1 share their J-class through
a and the same d-neighbour y. Thus c=col(x,x1) lies in J^circ meet(d*d),
hence in W. Its whole J-saturation is the quotient diagonal preimage
J^circ, so W's bisaturation gives J^circ subset W. Therefore m*m=K^circ.

The RAW square separately contains TRUE Id because m is symmetric and
serial. Its diversity slice is the STRONG square by old SAP injection.
Thus m;m=K. No identity edge is introduced in the private network.
Terminal relative reset follows by the earlier NR2 RAW representation:
it identifies the exact cover as a FULL cover, gives positive nonzero
J/K word slices by SAP, and excludes the local index-two case. This
instantiates the original reset theorem and uses no B049 transition closure.

## N08: A positive external layer from finite quotient escape

**D11; C42–C54/C65.** For the layer theorem ONLY J^circ positivity is
assumed. List the complete external quotient orbitals C_i. If there is
one, its positive preimage T_1 already IS U=K minus J. This includes every
index-two cover. Otherwise r>=2, so local index two is excluded. A high
T_1 power from N04 gives K^circ a positive word; hence ALL the additional
reset premises of N07 have now been DERIVED. Apply its reset and use
Phi injectivity/composition to get one complete quotient orbital M0 with
M0;M0=K/J. No extra K-positivity hypothesis is added to the layer result.

All invariant quotient relations are symmetric (old fine pair orbitals
project to them), their products commute, and nonempty ones are serial.
If nonempty symmetric serial P,S have P;S subset Delta_Q, each neighbour
choice forces a unique inverse neighbour. Both are the same equivariant
involution graph. If P is external, Delta union P is a nontrivial invariant
equivalence below K/J with two-point classes. FULL cover would force it to
be K/J, giving index two, impossible. Grouping the first external factor
against the remaining nonempty product shows that NO nonempty product of
external complete orbitals can lie wholly in Delta_Q.

Any nonempty invariant W subset K/J with an off-diagonal pair has connected
components exactly the K/J classes by FULL cover. Loops, if present, occur
everywhere by transitivity and give arbitrary padding. Without loops,
a bipartite component would force the forbidden index-two case; odd
detours/backtracks give all sufficiently large lengths. Finite quotient
orbitals make one threshold uniform. Hence W^n=K/J for every large n.

Suppose no DISTINCT complete external orbitals C,D multiply to
Ubar=(K/J) minus Delta. Put P_C=M0;C. Since C subset M0;M0, Peirce and
completeness give M0 subset P_C for every C. Their intersection is EXACTLY
M0. Choose C!=M0: its product contains no diagonal. If some external S
met all P_C, Peirce says M0;S meets every external C, hence contains Ubar.
For S!=M0 it has no diagonal either, so equals Ubar, contradiction. Thus
the only external orbital in that intersection is M0.

Start with a complete external R!=M0. More generally maintain a nonempty
invariant state R subset K/J disjoint from M0, with ONE positive OLD-word
pullback. If R met every P_C, their OLD positive-word pullbacks together
with Phi(R) would form a pairwise-intersecting family with empty total
meet. The direct original positive-word Helly proof contradicts this: attach
private atomic-word paths between two common roots, merging agreeing
one-edge duplicates. Pairwise menu intersections make every specified
simple cycle homomorphic. One original CCO map followed by binary SAP
injectivisation separates all vertices; the distinct root pair then has
a fine atom in every defining profile. No Set-Pasch theorem enters. All P_C contain M0,
and Phi is injective/Boolean and preserves composition. A state may contain
quotient diagonal; Phi still sends it to nonempty OLD DIVERSITY.

Choose C with R meet(M0;C) empty. Peirce makes (R;C) disjoint from M0.
It stays nonempty, invariant, inside K/J and old-positive. It need NOT be
complete or off-diagonal. Make any fixed finite successor choice. There
are finitely many invariant quotient relations, so a state repeats:
R;W=R for a NONEMPTY word W of external complete orbitals. No-return gives
W not contained in Delta. Eventual full powers give W^n=K/J, so

    R=R;W^n=R;(K/J)=K/J

by seriality. This contradicts R disjoint from M0. Thus some DISTINCT C,D
have C;D=Ubar. Phi converts this to the product of their positive old
word pullbacks, giving ONE positive word for K minus J. The two source-09
exports are now prepared with no B049 input and no module cycle.

## N09: Terminal specializations retain their actual premises

**D12; C20/C41/C64.** The original quotient-power theorem uses local FULL
cover and local index not two; it requires neither CCO nor global NR2.
The original reset additionally uses CCO and positive J/K words. The layer
theorem assumes only J positive and allows index two. Each terminal wrapper
supplies its own missing premises from the earlier CCO-free RAW theorem
and original SAP. RAW exactness identifies the represented cover with the
FULL invariant cover; it is not used inside the quotient graph argument.
No arbitrary quotient CCO or hidden SAP is inferred. Reset's RAW diagonal
is justified by actual two-step returns, separately from its STRONG square.

## N10: Source boundaries and finite diagnostics

**C54–C61/C66–C68.** Same-sort RAW commutation/modularity use no CCO/SAP.
The M3 obstruction uses actual RAW words and works without SAP. It is not
a claim that abstract nondistributivity alone always gives such words.
A finite homogeneous F3^2 model with undirected difference-direction colours
provides a concrete NR2, non-SAP, nonCCO sanity example. General modular
extraction is proved in N02; finite enumeration is only a check.

Full-preimage COMPLETE quotient orbitals matter: a fine proper subset need
not permit arbitrary fresh representatives. Nonzero J matters: quotient
closed walks are lifted between distinct OLD points in an infinite class.
At equality Phi(Delta) would be empty and this proof would fail. Private
word interiors may have different sorts; only their SAME-SORT endpoint
relations commute. Bare top spokes specify no edge, while N07 uses its
actual positive w_K word. Neither proof adds equality as diversity.

The internal narrow saturation is proof support, not a second allocation
of B049 generic typed saturation. B049 imports only the two standalone
source-09 exports from this module. All other source-09 results remain
separate until explicitly prepared.

Controls check finite actual products, homogeneity/extensions in the
F3^2 example, modular normalization, an explicit private M3 word diagram,
quotient powers and fresh clone windows, individual expanded cycles,
reset/layer products and boundary cases. They do not certify unbounded
CCO/SAP, infinite freshness, a general exact-domain theorem or Lean proofs.
All frozen source TeX and five existing HN/HKN receiving bindings remain;
overall EPPA keeps its source-relative status.

Countable-provider convention: the selected binary SAP unfolding API may be
formulated on a countable homogeneous realization. Apply it to the countable
Fraisse limit of the SAME finite old SAP age. Its finite output embeds back
into the actual old source, and old homogeneity aligns a pinned complete
endpoint pair. All word/profile statements concern finite diagrams, so this
adds no countability premise to the original source.
