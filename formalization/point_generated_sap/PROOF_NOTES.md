# B043 — point-generated canonical unary strong amalgamation

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Six definitions, 26 human proof claims and four tasks prepare ONE selected
Foundations I result, `lem:typed-point-generated-sap-criterion`, and its
PGO equation. The two other results in the same source file are already
prepared elsewhere and are not counted again.

The only import is `acl_owner_geometry` C03, abstract simultaneous finite
avoidance, with its proved C01/C02 ancestors extracted as internal support.
No CCO, owner geometry, topology or external theorem bridge enters this
module. This is human proof preparation, not Lean code or certification.

## N01: Actual interpretations, full closures and real base alignment

**D01–D03; C01–C04.** Retain the original real sorts and their full
original induced relational structure inside the actual canonical
interpreted expansion. Include identity terms. A point-generated object
contains its real generating points and EVERY value of a well-sorted
unary term on them. Every expanded vertex is such a value somewhere in
the ambient actual structure. Terms have one input source, so

\[
 \widehat{P\cup Q}=\widehat P\cup\widehat Q,
 \qquad \widehat\varnothing=\varnothing.
\]

The second equality uses the absence of additional nullary generators.
Relations, including any nullary relations, do not generate vertices.
All closures of finite real sets are finite by the source premise.
For a real vertex use its identity term when choosing a real source.

Every original automorphism acts on the actual interpreted carrier and
commutes with every named unary map and composition. Thus
`g tau(x)=tau(gx)`, and `Aut(M/D)` fixes the whole of `Dhat` pointwise.
This is the original full automorphism action on real and hidden points;
no replacement by an unrelated hidden automorphism group is necessary.

An object is an actual complete induced point-generated substructure, or
an induced-isomorphic copy. Its embeddings preserve AND reflect the
relations and preserve the functions, and on the real sorts restrict to
induced original embeddings. A base embedding is completely determined
by its map on real generators: the image of `tau(d)` has to be
`tau(image(d))`. To align an arbitrary span, embed both factors into
actual `Mhat`, extend the induced real base isomorphism by original
homogeneity, and act on one entire factor by its canonical expansion.
Every generated base value now agrees. This does not assume any
homogeneity of `Mhat` on arbitrary hidden finite closed sets.

One can use a finite real generating set rather than all real points of
the base. If the closure contains additional real term values, its
embedding still preserves them; choosing all its real points as the real
base gives the same full closure. The original base used for the PGO
condition is always finite and is always retained in its closure.

## N02: One simultaneous move constructs the strong amalgam

**D04/D05; C05–C11.** Assume PGO. After N01 the span consists of actual
`P1hat,P2hat` over literal `Dhat`. At this point additional intersections
are allowed. Put `G=Aut(M/D)`, `S=P2hat\Dhat` and `Z=P1hat`.
All points of S lie outside Dhat, so PGO says each has an infinite orbit
under THIS G. Apply the finite-action avoidance provider ONCE. It gives
one `g∈G` with `gS∩Z=∅`. Meanwhile g fixes every point of Dhat. Hence

\[
 \widehat P_1\cap g\widehat P_2=\widehat D.
\]

Separate moves for separate vertices would not establish this equality.
The avoidance theorem includes empty S and Z and needs no faithfulness.

Let P1 and P2 be finite real generating sets of the two factors. The
complete original real structure on `P1∪gP2` is actual and induced.
Its full interpreted unary closure has carrier exactly
`P1hat∪gP2hat`, because no generating function takes inputs from both
factors. Give that carrier all relations induced from actual Mhat.
Both factor inclusions preserve and reflect each relation and preserve
all maps. Together with the exact intersection they give a strong
amalgam in the point-generated category. The cross relations are induced
from Mhat; they are not asserted free. Empty D is legitimate because
there are no nullary generators.

## N03: Repeated strong copies force every off-closure orbit to be infinite

**D06; C12–C21.** Now assume point-generated SAP, WITHOUT assuming PGO
or importing avoidance into this implication. Suppose finite real D and
`u∉Dhat` have finite orbit `Aut(M/D).u` of size k. The identity shows
`k≥1`. Choose real x and term τ with `τ(x)=u`; identity terms cover real
u. The full closure `Phat=closure(D∪{x})` is a finite point-generated
object containing full Dhat and u. In particular x cannot already belong
to D.

Inductively strongly amalgamate copies of Phat over ONE common Dhat.
At an induction step the previous entire target is one leg and a fresh
Phat is the other. Strongness makes the new copy intersect the previous
entire target only in Dhat; injective embeddings preserve all previously
obtained distinctness. Thus k+1 copies have k+1 distinct images `u_j`
of u outside their common base. They need not exhaust the target.

Every target in this category embeds into actual Mhat by definition.
Embed this finite target and use original real homogeneity to identify
its real D copy with literal D. The canonical expansion of the aligning
automorphism identifies every term-generated point of Dhat as well.
Each copied real source x_j now has the same COMPLETE ORIGINAL finite
one-point diagram over D as x: this follows from the complete induced
leg map restricted to `D∪{x}`. Original homogeneity therefore extends
`D fixed, x↦x_j` to `g_j∈Aut(M/D)`. There is no appeal here to extending
an arbitrary hidden partial isomorphism.

Function preservation and equivariance give

\[
 u_j=\tau(x_j)=\tau(g_jx)=g_j\tau(x)=g_ju.
\]

The k+1 pairwise distinct u_j all belong to the k-element original orbit,
a contradiction. Thus every off-closure orbit is infinite, for every
finite real D including the empty base. This direction uses no
countability, CCO, symmetry, exact multiplication, or prior hidden SAP
criterion.

## N04: Category separation, empty bases and proof boundaries

**C22–C26.** N02 and N03 establish the selected lemma and its PGO equation.
Both sides concern finite COMPLETE INDUCED POINT-GENERATED objects over
FULL point-generated common bases. This qualification has mathematical
content, as the following actual interpreted example shows.

Let original M be a countably infinite pure set R. Let H be a disjoint
interpreted copy and name a bijection `f:R→H`, with NO named inverse.
The only nonidentity generating map is f. Then
`Dhat=D∪f(D)`. A point outside this closure, real or hidden, has an
infinite orbit under all permutations of R fixing D. Hence PGO holds,
and point-generated objects (finite sets of complete matched pairs)
have SAP. On the other hand `{h}` is a unary-closed HEREDITARY subobject
with an orphan hidden point. Two copies of `{r,h}`, each with `f(r)=h`,
over this common `{h}` have no strong amalgam in the actual hereditary
age: injectivity of f forces their real preimages equal. No inverse term
belongs to the signature to place r in the closure of h. This does not
contradict the point-generated criterion; `{h}` is not one of its bases.
It also illustrates the distinction from the separate hereditary theorem.

The finite matching diagnostics reproduce closure and this orphan
obstruction, and bounded factor spans have enough ambient fresh pairs
for the explicitly checked amalgams. They do NOT certify PGO or full
point-generated SAP for a fixed finite ambient matching. Positivity of
the displayed example uses the countably INFINITE pure set.

Empty bases cannot be dropped. As a separate example, take infinite
pure real R with a hidden singleton `{u}` and a named constant unary map
`f:R→{u}`, with no nullary generators. Every nonempty real closure
contains u, so all points outside it have infinite stabilizer orbit.
But emptyhat is empty and u has singleton orbit over the empty base.
Two nonempty point-generated objects necessarily share u in every actual
target, so SAP over the empty base fails. This is a boundary example,
not an instance satisfying full PGO.

For a binary generating function, closure of a union may contain a new
mixed value `F(x,y)` absent from both individual closures. The unary
union argument cannot then be reused. Extra nullary generators also
change the empty full base. Noncanonical added relations or embeddings
which forget the complete real reduct invalidate the original
homogeneity alignment argument. These are explicit proof boundaries;
no stronger theorem is claimed by the controls or metadata.

The source's intended actual-coordinate conventions supply identity
terms, retained real reduct and canonical original action. Making these
conventions explicit is an editorial clarification, not a new external
input or source signature repair. The original TeX remains unchanged.
