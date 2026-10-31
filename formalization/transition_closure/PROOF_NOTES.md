# B049 — typed RAW/STRONG saturation and finite quotient-transition closure

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Twelve definitions, 62 human proof claims, TWELVE source07 results,
fifteen auxiliary equations and eight tasks. Two independent source09
quotient-word prerequisites are imported from `terminal_lattice`; they
are not reallocated here. This is human preparation, not a Lean certificate.

## N01: Actual SAP pinning and the RAW/STRONG identities

**D01/D02; C01–C08.** RAW composition uses actual existential walks and
logical equality. STRONG profiles use specified diversity edges and fully
distinct formal path positions. A nonzero equivalence E means E>Id, not
merely a nonempty relation. Its classes are infinite under original SAP:
repeat a distinct E-neighbour over one fixed anchor and embed the finite
strong amalgam back by homogeneity. Transitivity handles every E-class.

We isolate pinned injectivisation without importing Set-Pasch. In a purely
binary atomic partial graph, every irreducible is a complete clique. A
homomorphism is automatically induced and injective on such a clique,
because all its pairs have preserved exclusive irreflexive atoms. Hence
it is a homomorphism-embedding and the existing relational SAP unfolding
theorem applies. To retain distinct old endpoints x,y, add their actual
complete pair type as a distinguished factor, preserve that induced image
type during unfolding, and use old two-point homogeneity to align the
resulting pair back to literal x,y. All specified path edges survive.
There is no assumption that the entire partial source is embedded inducedly.

Take x!=y and a RAW witness x J u t v K y with diversity atom t. If x=u,
choose a fresh a in J[x], avoiding the existing finite set. Duplicate the
COMPLETE old diagram {a,x,v,y} over its complete {a,v,y} base. This base
EXCLUDES x: t ensures x!=v, and the original roots differ. The new u'
is different from x, still J-related through a, and retains t to v.
If x!=u, keep u'=u. If v=y, choose a fresh b in K[y] and duplicate y
over the complete diagram on the other vertices and b, fixing x,u'. This
base excludes y because u' t y and x!=y. The new v' retains t from u'
and lies in K[y] through b. Otherwise keep v. The resulting consecutive
steps are all genuine diversity. Use pinned injectivisation to separate
any remaining nonconsecutive occurrences. This proves

    (J;{t};K)^circ = J^circ * {t} * K^circ.

Every original endpoint fine atom stays unchanged. The opposite inclusion
is just projection of the actual distinct-point path. No CCO or NR2 is used.

For x J z K y with x!=y, treat ALL middle cases. If z is outside {x,y},
duplicate its complete old triple over {x,y}. If z=x, choose fresh a in
J[x] outside {x,y} and duplicate x over {a,y}. The new z' satisfies
z' J a J x and z' K y, and differs from both endpoints. If z=y, choose
fresh b in K[y] and duplicate y over {x,b}; then x J z' and z' K b K y.
Never clone a point over a base that already contains it. Thus

    (J;K)^circ = J^circ * K^circ.

On one actual same-sort symmetric homogeneous source, invariant equivalences
commute under RAW composition: extend the old two-point endpoint swap to
an automorphism. Their product is an equivalence and their least upper
bound. Hence the last menu also equals (J join K)^circ. No mixed-sort
commutation is asserted.

If an exterior kernel is Id, OMIT its exterior step. Multiplying by its
empty diversity palette is wrong; adding an equality diversity atom is
also wrong. The same pinned argument applies to the remaining nonzero
exterior, giving all four cases later used by cylinders.

## N02: Exact PC domains versus independent positive-word Helly

**D03/D04; C09/C10.** The exact-domain result is a precise reuse of the
existing STRONG PC theorem: nonempty fixed domains equal finite nonempty
profile meets, the empty defining family is full diversity Top, and
support-consistent three domains have a simultaneous actual three-root
realization. Its proof provider has its own STRONG algebra hypotheses.
We do NOT use it in the original first-hit or MI-primality argument.

For those arguments the needed positive-word Helly has a direct proof.
Given pairwise-intersecting positive old typed profiles, draw their private
paths between common roots. Equal length-one branches must have the same
atom by overlap and are merged. Every simple cycle uses two branches;
their common diversity output supplies a homomorphism of that cycle.
Original HOM CCO gives a whole homomorphism. The purely relational old
SAP injectivisation of N01 separates all formal vertices, so the roots
are distinct and their fine atom belongs to every profile. Finite meets
of positive profiles inherit the result by flattening the defining
families. This proof uses no exact product formula, distributivity,
Set-Pasch theorem or hidden SAP.

## N03: Original first-hit cover interpolation

**D05/D06; C11–C18.** Work at the LOCAL FULL original cover Id<J<K,
where J is meet-irreducible with unique FULL cover K. Assume J^circ and
K^circ have single positive OLD word presentations. Do not replace these
premises by an exact-sublattice MI or by terminality without proving the
identification separately.

Two standalone source09 inputs are selected. At J>Id, the old diversity
pullback Phi of quotient relations is injective and preserves finite
meets/unions. Actual quotient composition lifts exactly to STRONG products,
because every old J-class is infinite and all formal intermediate old
representatives may be chosen fresh. In particular Phi(Delta_Q)=J^circ,
a nonempty diversity menu, not old logical Id. The second input proves
that U=K minus J itself has ONE positive original word at every local
FULL cover with positive J^circ, including index two. Its independent
proof does not use interpolation or cylinders from this module.

Suppose positive P meets J^circ and exits J, but avoids U. Saturate

    S = J^circ * P * J^circ = Phi(Sbar).

It is a single positive old word, and Sbar contains the TRUE quotient
diagonal because P meets J^circ. J-saturation cannot change K-relatedness
of endpoint classes. Thus Sbar intersect K/J=Delta_Q, while Sbar has an
edge outside K/J. Its connectedness equivalence pulls back to an original
invariant equivalence H>J. The UNIQUE FULL cover gives K<=H. Reflexivity
makes powers increase. Choose the least n>=2 with Sbar^n meeting the
external quotient layer Ubar=(K/J) minus Delta_Q. Put

    Abar=Sbar^(n-1),       Tbar=Sbar;Ubar.

Minimality gives Abar intersect K/J=Delta_Q. Since Sbar has only diagonal
edges inside K/J, Tbar intersect K/J=Ubar: a Tbar witness ending in the
same K-component must have its Sbar step diagonal, and Delta_Q subset
Sbar supplies every Ubar pair. An ACTUAL first-hit quotient triangle,
rotated with same-sort symmetry, gives Abar intersect Tbar nonempty.
This is ordinary witness rotation, not an imported typed Set-Pasch theorem.

The three OLD diversity pullbacks Phi(Abar), Phi(Tbar), K^circ are SINGLE
positive word profiles. Indeed quotient composition gives respectively
S^(n-1) and S*U. They meet pairwise: the first and third at J^circ, the
second and third at U, and the first two through Abar intersect Tbar.
Their total intersection is empty, since inside K/J the first two supports
are the disjoint Delta_Q and Ubar. This contradicts N02's direct positive-
word Helly. Hence P meets K minus J. Interior sorts of every word may be
arbitrary named original sorts; only their endpoints are on this fixed a.

## N04: Original MI-primality and terminal represented wrappers

**C19–C23.** For original D1,D2 that are nonempty finite intersections
of positive old profiles, suppose their nonempty common meet is inside
J^circ but both exit J. If one defining family is empty, that domain is
Top and the premise already puts the other in J^circ. Otherwise choose
one common fine atom c. Every defining P of either Di contains c and
exits J, because Di does. First-hit interpolation makes P meet the
positive external layer U. For each i its defining family together with
U is pairwise-intersecting, so positive-word Helly gives Di intersect U
nonempty. Flatten D1,D2,U; all cross defining profiles meet through
D1 intersect D2, and profiles against U meet by the previous argument.
Helly then gives D1 intersect D2 intersect U nonempty, impossible. This
proves the ORIGINAL OWP theorem without typed exact-domain algebra.

Only the represented wrappers use terminal FULL NR2. The independent
`real_closure` RAW-word theorem makes every original invariant equivalence
FULL RAW exact/represented. Therefore a represented MI/cover is a FULL
invariant MI/cover. Nonzero RAW word presentations have positive diversity
profiles by the old pinned SAP path argument. Apply N03/N04. For typed
PC exact domains additionally use N02's exact-domain provider to obtain
the finite defining positive-word families. J=Id is vacuous because a
nonempty STRONG diversity menu cannot meet logical Id. Empty defining
families retain diversity Top. Terminality concerns the FULL original
invariant lattice, not only an already chosen exact sublattice.

## N05: Generic transport and original SAP noncollapse are distinct

**D07/D08; C24–C30.** Nonempty invariant relations between transitive
sorts are serial and coserial. The existing generic transport theorem
therefore defines lambda_(R,E)(y) as the unique E-class of a predecessor
when R;R^op subset E. Its kernel is F=R^op;E;R. It is onto, and its
inverse induced map q:a/E→b/F is the canonical quotient bijection. In
the finite actual named full-orbital context these invariant relations
are definable, and the theorem transports the entire invariant upper
interval, not just exact named objects.

Properness transfers by quotient cardinality: if E is not Top, a/E has
at least two classes, so b/F does also. Ruling out F=Id requires a
SEPARATE original SAP argument. Any total 0-definable real function f
must be identity. Otherwise f(x)=y!=x; two copies of the complete pair
{x,y} strongly amalgamated over input x must have distinct y-images,
while functionality forces them equal. Disjoint named sorts also force
y!=x. Thus source and target sorts agree and f is literal identity.

If E>Id and F=E^R were equality, R would be a total function a→b: two
successors of x are F-related. It would be old identity, making F=E,
contradiction. Hence F is proper and NONIDENTITY. For the final source
assertion R;R^op=Id_a, functionality is instead in the CONVERSE direction:
every target y has one predecessor x. Apply the same SAP argument to the
input y of R^op:b→a to get R=Id on the same old sort. Do not assume an
unproved equality of E^R in that converse argument. No hidden or quotient
SAP is inferred from these real-sort statements.

## N06: Identity redundancy, composition and finite unary functions

**D09/D10; C31–C40.** If actual same-sort R contains Id and R;R^op
subset J, then R subset J. Indeed symmetry and Id subset R give
R=Id;R subset R;R^op. Consequently R^op;J;R=J, with one inclusion from
R subset J and the other from Id subset R. Each R-pair stays inside J,
so q_R is exactly the already named identity on a/J. This covers mixtures
of Id with diversity atoms; it creates no positive-path identity edge.

For R:a→b and S:b→c, use the LITERAL intermediate kernel F=E^R. If two
sources reach the same target through T=R;S, their intermediate witnesses
are S;S^op-related and hence F-related, so their E-classes agree. Thus
T;T^op subset E. Actual RAW associativity gives E^T=F^S, and a witness
xRySz shows pointwise that q_T=q_S composed q_R. Seriality covers every
source class. Do not substitute unrelated quotient charts or commute
mixed-sort factors.

For H>=F pull it back through the FULL upper-interval isomorphism to H0.
Both u_(F,H) after q_(R,E) and q_(R,H0) after u_(E,H0) send each E-class
to the same H-class of its R-neighbours. This proves the upward rewrite
TQU. The interval isomorphism preserves proper MI; this is full-lattice
MI too, because any equivalences meeting in H0 are already >=H0>=E.
Generic transport gives only an invariant MI. TERMINAL FULL NR2 supplies
its FULL RAW exact/represented membership separately, while visible SAP
excludes equality targets. These gates are retained before naming a
proper hidden quotient object.

Repeated canonical composition replaces a transition-only term by one
q_(T,E) for an actual old invariant RAW relation. If a same-sort T contains
logical Id, identity redundancy eliminates it. Move upward maps toward
the source using TQU; each rewrite lowers the number of transition/upward
inversions. Compose successive upward maps. A term then has one initial
projection or upward map and at most one q_(T,H), or identity. There are
finitely many old source/target sorts, represented kernels and Rel-families.
Therefore there are finitely many unary term FUNCTIONS. There may be
infinitely many syntactic expressions for the same function. Such closure
creates no new visible real point.

## N07: Actual representative cylinders and their partition

**D11; C41–C43.** Fix actual coordinate classes q,r and a distinct old
representative pair x,y of fine atom t. Their entire distinct-representative
spectrum is (J;{t};K)^circ. One inclusion moves representatives inside
the same old classes. Conversely an actual saturated witness contains a
middle t-pair; align it to x,y by old two-point homogeneity. Its exterior
endpoints lie in q,r and realize the desired endpoint fine atom. Thus the
spectrum is independent of which representative atom was chosen.

N01 converts this RAW spectrum to the four STRONG cylinder cases, omitting
an exterior for equality coordinates. If two spectra share an atom,
old two-point homogeneity takes representatives of one class-pair to the
other, so their spectra are equal. Distinct spectra therefore define a
partition of compatible ordered distinct HIDDEN coordinate vertices.
When both endpoints are real this is the old diversity partition. Omit
the diagonal only when the endpoint positions are the SAME hidden sort;
quotient equality is not the same as old representative equality.

## N08: Atomic naming of full functional branches

**D12; C44–C52.** If t is ANY old atom inside a nonempty invariant R
with R;R^op subset J, t is serial and coserial. For each target y pick
x t y, hence x R y. The source J-class assigned through t and through
R is the same unique class. Therefore lambda_t=lambda_R POINTWISE on
the whole target sort; their actual kernels and canonical inverse quotient
bijections agree. This is equality of maps, not of the fine relations.

Every matched quotient pair admits an actual t-edge by seriality and
the canonical labelling. Old two-point homogeneity makes their entire
graph one complete quotient-pair orbital. Its old representative spectrum
is independent of t and is

    (J;{t};K)^circ = (J;R;K)^circ
        = J^circ * R * K^circ.

Both kernels are nonzero by the original SAP noncollapse statement. For
reachability use TERMINAL positive words for J^circ,K^circ and insert
ONE chosen atom t between them. This is one positive old word for the
whole graph spectrum even when R is a union of many atoms. No assumption
that a union R is an atomic word is made. Every distinct old representative
pair in that spectrum belongs to a matched quotient class-pair, and every
matched pair has that full spectrum. Hidden vertex coincidence is checked
by equality, not an artificial off-diagonal graph colour.

For an identity-free positive strong branch P, apply the same pointwise
argument to any atom t subset P: J^t=J^P and pi_t=pi_P. A proper MI target
is proper MI by FULL interval transport, nonidentity by old SAP, and FULL
RAW represented by terminality. Since t is a genuine old diversity atom,
its transition symbol was already named. The whole branch thus induces
an existing finite-language transition function. No new visible point is
created; a transport starting from real equality would be old identity
by the converse-function argument of N05.

## N09: Boundaries, gates and finite diagnostics

**C53–C62.** The first-hit/prime branch has a strict firewall against
typed exact-domain products, Set-Pasch, global terminality and hidden SAP.
The exact PC provider and terminal RAW word provider occur only in their
specified wrapper/namedness branches. Same-sort commutation is never
used to reorder mixed typed factors; mixed old words are permitted only
with their actual endpoint sorts and canonical quotient labels.

Old SAP is essential for the RAW/STRONG exterior identities. On the old
two-point one-colour complete structure with J=K=Top, RAW J;t;K has
nonempty diversity, but a four-distinct-vertex J^circ,t,K^circ path cannot
exist. The source has ordinary AP, not SAP. An identity-only exterior
also cannot be replaced by its empty diversity palette: it is OMITTED.

The controls use finite original clone windows only for bounded diagrams.
They check actual relation products, distinct-interior saturation, pinned
middle-witness cases, quotient labellings and finite normal-function closure,
cylinder spectra and atomic/whole-branch map equality. They establish no
infinite class freshness, general first-hit or cover-layer theorem, hidden
SAP/CCO or Lean proof. Empty defining families, genuine logical Id versus
diversity Top, inactive/empty syntax cases and actual unary/pair
admissibility remain explicit. Existing B047 actual/FULL-sector qualifiers,
five HN/HKN receiving bindings and the source-relative EPPA status remain.

Countable-provider convention: the selected binary SAP unfolding API may be
formulated on a countable homogeneous realization. Apply it to the countable
Fraisse limit of the SAME finite old SAP age. Its finite output embeds back
into the actual old source, and old homogeneity aligns a pinned complete
endpoint pair. All word/profile statements concern finite diagrams, so this
adds no countability premise to the original source.
