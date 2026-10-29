# Finite exact reconstruction, with the selected real root preserved

Status: **HUMAN_EXPANDED_NOT_LEAN**. This is the private B029 proof expansion at
mathematical source `490c3f36d85db5a0b3ced0598e6c431825254ec5`. No source TeX
is changed. The only new numbered result is `lem:acf-finite-lift`; the only
new auxiliary equation is `eq:acf-finite-acl`. The preceding
`lem:acf-point-homogeneity` is already expanded by B018, `owner_action`
C12/C30, and is outside the new module scope and dependency set.
The shared prescribed-action criterion is B001 support, with its elementary proof recalled below, rather than a new export.

These notes prove the local finite reconstruction implication. They neither
construct its supplied quotient witness nor certify global rooted ACF,
ordinary EPPA, a coherent choice of lifts, or Lean compilation. In particular,
there is no age-level ordinary EPPA assumption on Q. The rank-restoration
consumer uses the ordinary branch and needs none of the stronger relative
owner-cover hypotheses.

## N01: Exact scope, actual quotient orbitals and repeated sorts

Let Q be a nonempty transitive homogeneous structure in a finite complete
symmetric binary language naming its actual RAW pair orbitals, including
logical equality. Original invariant endorelations commute. For the prepared
actual exact quotient/joint homogeneity providers retain semantic homomorphic
CCO and their countable-source convention. Let K be an ACTUAL invariant FULL
RAW EXACT equivalence with finite real classes, and let
pi:Q -> Qbar=Q/K be its actual quotient. K=Id is allowed. There is no
assumption that the greatest finite equivalence F_Q is exact, that K=F_Q,
that Q is finite-exact-normalized, that finite packets are thin, or that
Q has SAP.

Qbar names ALL actual pair orbitals of the old group Aut(Q) on K-classes.
These are the canonical quotient colours used throughout. Its FULL
structure automorphism group can be larger than the image of Aut(Q).
Nothing below identifies these groups or chooses a section between them.
RAW exact-source inheritance C28 supplies homogeneity, transitivity and the
finite complete symmetric binary standing language for this actual quotient.
Finite real bases in either source have finite acl: the pointwise stabilizer
of a finite tuple has only finitely many point orbits, since homogeneity in a
finite relational language identifies them with the finitely many possible
finite diagrams over that tuple. Its algebraic points are the union of the
finitely many finite such orbits. This proves C01.

Here is the elementary actual orbital pullback proof used locally, rather
than relabeling internal RAW C14 as a new export. Suppose an old atom a is
realized by (x,y), and q is the orbit of (K[x],K[y]). If
(u,v) belongs to K;a;K, some u' K u and v' K v have old colour a. An original
automorphism carries (x,y) to (u',v'), so (K[u],K[v]) belongs to q. Conversely,
if (K[u],K[v]) belongs to q, an original automorphism carries
(K[x],K[y]) to that pair of classes; the images of x,y give witnesses to
(u,v) in K;a;K. Thus the full inverse image of q is exactly K;a;K. It is an
invariant union of old fine atoms. This applies to equality as well as
diversity. Likewise K itself is a union of named old atoms. No individual
fine colour is asserted to be constant on a full cross matrix.

The local imports are RAW exact products C09, mixed join C16, nested mixed
C17, joint lifting C23, and quotient inheritance C28. The point support and
already-prepared B018 point homogeneity are kept distinct; the latter is not
needed or imported by this finite-lift module. In particular, we do not import an
EPPA-dependent owner provider merely for an elementary point-action argument.
No unary/rank-one real-closure provider is used: K reconstruction has arbitrary
rank.

All displayed maps concern ACTUAL sorts. If two kernels are equal, merge
their sort maps; do not invent two independently movable copies of the same
actual sort. The Id quotient is the real sort. In a two-sort lift with
K=Id, compatibility says p0 agrees with the finite quotient automorphism on
its real domain. In the relative lift, K=H implies J=K=H and the relative
quotient owner map is identity: Dbar=Bbar=B as sets of classes, so agreement
on the common quotient forces the supplied K- and H-actions to coincide.
If H=Id, then J=K, the quotient coarse owner is the K-sort itself,
Bbar=Dbar, and complete B is the real set D; the prescribed gamma agrees
with p0 on its domain and induces the supplied K-action. If K=Id, the given
barbeta is itself the real map on all of D and agrees with p0. If J=Top,
the common quotient is the actual singleton; its action is forced. These
are consistent merged maps, including cases where several equalities hold
simultaneously. No extra hypothesis is imposed to exclude degeneracy.

## N02: Both algebraic-closure directions with stabilizers distinguished

This section proves C02–C06 and `eq:acf-finite-acl` for EVERY finite real
A0, including A0 empty. Write

\[
 G_{A_0}=\operatorname{Aut}(Q/A_0),\qquad
 \overline G_{\pi A_0}=\operatorname{Aut}(\overline Q/\pi A_0).
\]

Both groups are FULL pointwise stabilizers in their own actual languages.
The original stabilizer induces a subgroup of the quotient stabilizer.
Equality of the two groups or surjectivity onto the latter is not assumed.

By transitivity all K-classes have one finite positive size k: take any
original automorphism sending a point of one class to a point of another;
it maps the entire first class bijectively onto the second. Thus the full
preimage of a finite set Tbar has k|Tbar| points. In particular it is finite,
including when Tbar is empty. This is C02.

First suppose xbar=pi(x) belongs to acl_Qbar(pi A0). Its orbit under the
FULL quotient stabilizer is finite. The orbit of x under G_A0 lies in the
union of the corresponding finitely many K-classes, each having k points.
It is finite, so x belongs to acl_Q(A0). This is the inclusion

\[
 \pi^{-1}\operatorname{acl}_{\overline Q}(\pi A_0)
       \subseteq\operatorname{acl}_Q(A_0).
\]

Only containment of the original stabilizer image in the quotient
stabilizer was used. This proves C03.

For the other direction suppose xbar is NOT algebraic over pi A0 in the
quotient. There are infinitely many DISTINCT classes c in its full
quotient-stabilizer orbit. In particular xbar is not one of the named classes
pi A0, each of which the stabilizer fixes individually. For each c choose
one quotient automorphism fixing pi A0 pointwise and sending xbar to c.
Restrict it to the FINITE set pi A0 union {xbar}. Join this finite K-sort
map to the identity on EVERY ACTUAL real point a in A0. Within the real
sort the map is identity, and within the K-sort it is a restriction of the
chosen quotient automorphism, so within-sort orbitals are preserved.

For EVERY mixed pair (a,d), where a is a named real parameter and d is any
named K-class, its orbital depends only on (pi(a),d), by nested mixed
reduction at Id<=K. Both quotient classes occur in the finite K-sort map,
and that map fixes pi(a). Hence every mixed pair is preserved, including
class membership and quotient diagonal cases. This is a genuine finite
joint partial isomorphism. The preceding repeated-sort convention handles
K=Id: the quotient map fixes A0 and agrees there with the real identity.
This proves C04 and the mixed part of C05.

Joint exact homogeneity supplies ONE original automorphism g_c extending
this finite map. It fixes A0 POINTWISE and sends pi(x) to c. The points
g_c(x) lie in distinct K-classes as c varies, and so give infinitely many
distinct G_A0-images of x. Thus x is not algebraic over A0. Taking the
contrapositive proves the reverse inclusion. We have established

\[
 \boxed{\operatorname{acl}_Q(A_0)
     =\pi^{-1}\!\left(\operatorname{acl}_{\overline Q}(\pi A_0)\right).}
 \tag{finite-acl}
\]

The proof uses only a separately selected finite joint lift for each orbit
point, never a lift of the entire quotient automorphism or a group section.
It applies at empty A0 unchanged; in a finite transitive source both
empty-base closures are their entire source and the formula still holds.
The result does not require S, a supplied witness, owner H, thin packets,
normalization, or any EPPA input. C01/C02 also give finiteness of both sides.

## N03: Uniform complete-matrix palette and abstract closed-span descent

This section proves C07–C10. Assume the GIVEN original palette S_Q has
strong amalgamation for finite induced ABSOLUTELY acl_Q-closed spans. It
makes no assertion of raw SAP, and the resulting amalgam need not be closed.

For an actual DIVERSITY quotient atom q and an actual class pair (C,C') in
q, consider ALL fine colours in the full C×C' matrix. Any other class pair
in q is the image of this pair under one original automorphism, by the
DEFINITION of the actual old-group quotient orbital. That automorphism
transports the ENTIRE two classes and their matrix. Its fine colour support
is therefore independent of the chosen pair. Denote this common support by
Lambda_K(q). No entry is equality because C and C' are distinct K-classes.
Define

\[
 \overline S=\{q\in\mathcal D(\overline Q):
                         \Lambda_K(q)\subseteq S_Q\}.
\]

Then q is in barS exactly when EVERY entry of EVERY full cross matrix above
q is in S_Q. An existentially safe entry would give a different palette
and is insufficient for the later unsafe-clique argument. Quotient logical
equality is not included in this diversity palette. This proves C07.

Take ANY finite absolutely closed quotient span

\[
 \overline L\ \longleftarrow\ \overline C
              \ \longrightarrow\ \overline R.
\]

Treat its objects as induced age members with their actual quotient charts.
Each quotient base embedding is a finite partial isomorphism on ACTUAL
K-sort elements. Apply joint exact homogeneity to THAT finite map and
restrict its ambient lift to the full finite K-preimage of the base. This
gives a genuine original fine-coloured embedding of that preimage into the
full preimage of the corresponding factor. Its image is exactly the full
preimage of the quotient base image, because the ambient lift carries full
K-classes to full K-classes. The two base embeddings can be chosen
separately; no canonical identification of individual fibres is asserted.

Take abstract copies of the two original fine factors and identify them
ONLY along their common full base using these actual fine embeddings. Their
complete base diagrams agree. If their chosen actual charts happened to
meet elsewhere, that accidental overlap is absent from this abstract span.
This is legitimate input to strong closed amalgamation, which is a property
of all finite age spans; it does not presuppose raw SAP or an actual union
with no unwanted intersections. Equivalently one may normalize each complete
quotient base by homogeneity first, but one must still retain the abstract
span with precisely the prescribed base. This is the base-map part of C08.

For each quotient object Tbar, let T=pi^-1(Tbar). It is finite by C02.
The finite-acl identity at the finite real set T gives

\[
 \operatorname{acl}_Q(T)
   =\pi^{-1}\operatorname{acl}_{\overline Q}(\pi T)
   =\pi^{-1}\operatorname{acl}_{\overline Q}(\overline T)=T,
\]

because Tbar is ABSOLUTELY closed. The identity also handles an empty base,
including the case when empty is not closed and hence is not an admissible
closed span object in the first place. The lifted factors and base are
therefore absolutely closed original structures, completing C08.

Apply the original strong closed-S_Q assumption to this span, and realize
the resulting finite age amalgam as an induced actual subset of Q. It is
harmless to restrict the amalgam to the union of the two factor images.
Every original fine embedding of a finite factor extends ambiently by
homogeneity of Q. It preserves K and therefore maps each full k-point
K-class of the factor into one actual K-class. That actual target class
also has k points; injectivity makes the image the ENTIRE class. In
particular the factor images, and their union, remain full K-preimages.

This fullness is essential. If an off-base quotient class from each factor
had the same target K-class, their full real images would coincide, giving
real intersection outside the full common base. That contradicts strongness.
A single factor likewise cannot collapse two quotient classes because its
embedding preserves and reflects K. Its off-base classes cannot collapse
onto a base class either. Thus the projected factor images intersect exactly
in the quotient base and give a STRONG quotient amalgam. These are C09 and
the strongness part of C10.

For a new off-base cross pair of quotient classes, the entire first real
class belongs to one real factor outside the base and the entire second
class to the other. EVERY entry between them is a new real cross edge and
has colour in S_Q. Their quotient edge consequently belongs to barS by C07.
All canonical quotient embeddings preserve their pair orbitals by the actual
pullback argument of N01. This proves strong closed-barS amalgamation in
Qbar. No closedness of the resulting amalgam is needed or claimed, and no
relative owner map, kernel condition, or witness was used.

## N04: Finite recognizability, one full preimage and the two-sort lift

This section proves C11–C14. Let p be ANY original partial isomorphism of a
finite induced real structure, not necessarily a map on a union of full
K-classes. If x K y in its domain, the old fine colour of (x,y) belongs to
the named union K. Preservation of that fine colour gives p(x) K p(y).
The same argument for the inverse map proves the converse. Therefore

\[
 \overline p(\pi x)=\pi p(x)
\]

is WELL-DEFINED and INJECTIVE, with range pi(ran p). For each quotient pair
colour q, its pullback is a union of old fine atoms, as proved in N01.
Preserving the old fine colour of every representative pair preserves q.
This includes pairs within one K-class and logical equality. Hence barp is
a genuine quotient partial isomorphism. This proves C11 without choosing a
section of real representatives; homogeneity could alternatively extend p
first and then project its finite action.

Fix ANY finite induced Tbar subset Qbar and set D=pi^-1(Tbar), its FULL
finite preimage. Apply the same recognition argument to beta and beta^-1
for any beta in FULL Aut(D). All classes of Tbar occur in D, so beta
induces a unique bijection of Tbar, and it preserves all named quotient
colours. Composition is respected. Thus every finite beta descends to
Aut(Tbar), establishing C12. Ambient invariance alone would not guarantee
this for an arbitrary unnamed relation on a sparse finite structure; here
both the kernel and the pair-colour pullbacks are recognizable fine-colour
unions.

If Tbar contains acl_Qbar(pi A0), its full finite preimage contains
acl_Q(A0) by N02, and hence contains A0. The SAME D will be retained for
every source request and every selected root. It is K-saturated. The
finite-acl identity applied to finite D gives the useful precise boundary

\[
 \operatorname{acl}_Q(D)=D
  \quad\Longleftrightarrow\quad
 \operatorname{acl}_{\overline Q}(\overline T)=\overline T.
\]

Indeed the identity identifies the first closure with the full preimage
of the second, and pi is onto Tbar. This is C13. Merely containing the
closure of A0 does NOT make either entire witness closed. No unconditional
closedness of arbitrary D is asserted.

Here is the finite lifting observation used in both witness arguments.
Let barbeta be an automorphism of Tbar. Let p0 be an original partial
isomorphism with domain and range in D satisfying

\[
                  \pi p_0=\overline\beta\pi
                    \quad\hbox{on dom}(p_0).
\]

Form ONE finite map with p0 on the real sort and barbeta on ALL named
K-classes of Tbar. Within-sort orbitals are preserved by hypothesis. For
EVERY mixed pair (x,c), where x is in dom(p0) and c is ANY named K-class,
nested mixed reduction makes its orbital depend only on (pi x,c). Both
classes occur in Tbar and are moved by barbeta. The compatibility equation
therefore verifies every mixed pair, not merely x with its own class.
Coincident actual sorts are merged as in N01. This is a genuine finite
joint partial isomorphism, so joint exact homogeneity gives ONE ambient
g in Aut(Q) extending it.

Since g permutes ALL the K-classes of Tbar by barbeta, it preserves their
ENTIRE preimage D setwise; its inverse gives equality rather than one-sided
inclusion. Restricting g to D is an original automorphism extending p0 and
inducing EXACTLY barbeta. This proves C14. No arbitrary fibre permutations,
coherent assignment of lifts or global quotient-automorphism surjectivity
were constructed.

## N05: Ordinary source extensions, unsafe projection and literal roots

This section proves C15–C18. Now A0 is finite NONEMPTY and one finite
induced ordinary witness Dbar over pi A0 is SUPPLIED in Qbar. It contains
acl_Qbar(pi A0), extends every partial automorphism of pi A0 and has rooted
barS-ACF. Its construction is outside this implication. Let
D=pi^-1(Dbar), once and for all. C13 already proves finiteness and
containment of acl_Q(A0).

For EVERY original partial automorphism p of A0, N04 produces the quotient
partial automorphism barp of pi A0. The supplied quotient EPPA witness
extends barp to some barbeta in Aut(Dbar). Use N04's two-sort lift with
p0=p. Its restriction to the SAME D extends p. This proves ordinary EPPA
for the input A0 (C15). It is conditional finite-witness transfer, not an
age-level EPPA theorem for Q, and it uses none of the stronger H/B/kernel
premises.

Let Z subset D be a nonempty S_Q-unsafe clique and select ANY z in Z.
Regard pi(Z) as the SET of distinct K-classes, without requiring pi|Z to be
injective. For any two distinct such classes c,d choose representatives
x,y in Z. They are distinct real points, so their fine colour a is outside
S_Q. That colour is an entry of their full cross matrix and belongs to
Lambda_K(q), where q is the quotient colour of (c,d). Thus Lambda_K(q) is
not contained in S_Q and q is outside barS. Internal K-edges disappear on
projection. If the projection is a singleton it is unsafe vacuously. Hence
pi(Z) is always nonempty and barS-unsafe. This proves C16.

Quotient rooted ACF supplies an automorphism baralpha of Dbar such that

\[
 \overline\alpha(\pi Z)
      \subseteq\operatorname{acl}_{\overline Q}(\pi A_0),
 \qquad \overline\alpha(\pi z)\in\pi A_0.
\]

Choose an ACTUAL a in A0 representing the last class, so
baralpha(pi z)=pi a. Original transitivity makes the singleton map z->a
a genuine original partial isomorphism; no colour or unary type obstacle
is hidden. Apply the two-sort lift with p0 this singleton and barbeta equal
to baralpha. The resulting automorphism alpha of the SAME D sends z
LITERALLY to a, rather than merely to some point of K[a]. For every
x in Z, its image projects into the displayed quotient closure and hence
lies in acl_Q(A0) by N02. This proves C17.

Together C13/C15/C17 give C18: one finite D contains the actual closure,
extends all ordinary source maps, and handles EVERY unsafe clique and EVERY
selected root. The lift may be chosen separately for each request or root;
no coherence is claimed. K=Id simply makes D=Dbar and the compatible maps
merge. No owner master, H, finite inverse owner set, or fibre-transitive
owner kernel is needed by this ordinary reconstruction.

## N06: Actual exact owner cover, its finite completeness and action maps

This section proves C19–C20, beginning the SEPARATE stronger relative
assertion. Let H be an ACTUAL invariant FULL RAW EXACT equivalence of Q,
possibly incomparable with K. Put

\[
 J=K\vee H=K;H,\qquad
 T=Q/J,\qquad \overline H=J/K,
 \qquad r:Q/H\longrightarrow Q/J.
\]

Original invariant commutation and equivalence idempotence prove
K;H=K join H: the product contains K,H, is reflexive and symmetric, and
its square is K;K;H;H=K;H, so it is the least equivalence containing them.
The RAW exact product provider makes J full exact. The quotient
Qbar/barH is canonically the ACTUAL T=Q/J, retaining its canonical
pair orbitals. This is an actual quotient identification, with no arbitrary
choice of a quotient chart or group section.

For c in T choose any real x in that J-class. EVERY H-class in c meets
the finite K-class K[x]. Indeed, for any y in that H-class,
(x,y) in J=K;H gives u with x K u H y. More generally the same argument
works for ANY K-class in c, not just the initially chosen one. Thus the
number of H-classes above c is at most k, and the complete inverse image

\[
                    B=r^{-1}(\overline B)
\]

of ANY finite barB subset T is finite, with at most k|barB| elements. It
maps onto barB. This establishes finite owner packets in C19; it does not
assert that all compatible tuples in unrelated quotient systems are
realized.

The supplied relative rooted witness explicitly contains acl_Qbar(pi A0),
by the rooted ACF containment clause, just as in the ordinary branch.
Now use the supplied relative quotient witness Dbar->barB, which is onto
EXACTLY barB, and let D be its full K-preimage. Each K-class of Dbar with
J-owner c meets EVERY H-class over c by the preceding incidence fact.
Since every c in barB occurs, EVERY element of complete B is met by D.
Conversely each point of D has J-owner in barB. Therefore

\[
                         \pi_H(D)=B
\]

EXACTLY. Merely selecting some representatives from an inverse owner packet
would not give this equality.

The needed finite action maps are actual recognizable quotient actions,
not abstract homomorphisms attached by assertion. H is an invariant union
of old fine atoms; each H-quotient pair predicate has fine-atom-union
pullback H;a;H by the same actual-orbit proof as N01. Consequently every
finite original automorphism of D descends to Aut(B), since all B occur.
Likewise every finite automorphism of Dbar descends along J/K to Aut(barB).
For the remaining cover B->barB, the kernel J/H is a union of named
H-sort orbitals: an H-pair orbital either belongs entirely to J or is
disjoint from it, since the projection is equivariant. Each actual T-pair
predicate likewise pulls back to a union of H-sort pair orbitals. Thus
EVERY gamma in FULL Aut(B) preserves and reflects the cover kernel and
induces a unique automorphism rho(gamma) in FULL Aut(barB). Its equivariance
is

\[
               r(\gamma b)=\rho(\gamma)(r(b))
                  \qquad\text{for EVERY }b\in B.
\]

All source owner elements occur in B, so composition gives the ACTUAL group
homomorphism rho:Aut(B)->Aut(barB). These recognition arguments prove C20.
They do NOT prove rho onto or its kernel transitive. Those substantive
additional assumptions will first be used in N08 for a rooted transport.

## N07: Entire three-sort maps and all compatible relative source requests

This section proves C21–C23 WITHOUT the onto/kernel-transitivity assumption.
Let barbeta be an automorphism of the supplied Dbar, inducing its ACTUAL
component bargamma on ALL barB. Let gamma be in FULL Aut(B) with
rho(gamma)=bargamma. Let p0 be an original partial isomorphism within D
compatible with BOTH maps:

\[
 \pi_Kp_0=\overline\beta\pi_K,
 \qquad \pi_Hp_0=\gamma\pi_H.
\]

Make ONE finite map on the real domain of p0, ALL K-classes in Dbar and
ALL H-classes in B. The within-sort diagrams are preserved separately.
For every real/K pair and every real/H pair use nested mixed reduction,
respectively Id<=K and Id<=H, as in N04. The whole projected real domain
lies in the named quotient set in each case; this checks pairs with every
other named owner, not just the real point's own owner.

For the remaining K/H mixed pairs, write a for ANY representative old RAW
atom, INCLUDING logical equality. Original commutation gives the exact
identity

\[
 K;a;H=K;H;a=J;a=J;a;J=a;J.
\]

The equality a=Id gives K;H=J and is retained; it cannot be omitted as a
supposedly nondiversity case. The right-hand side is the full pullback of
one ACTUAL J-quotient pair orbital. Thus the K/H mixed pair orbital is
determined by the pair of their J-projections. Both projections lie in
barB, and both are moved by the SAME bargamma, because barbeta has that
coarse component and rho(gamma)=bargamma on the ENTIRE set. Every K/H
mixed pair is therefore preserved. Exactness of H and K allows application
of the joint lifting theorem AFTER this binary verification; the algebraic
identity alone would not provide a lift for arbitrary nonexact H.

Merge coincident actual sorts as detailed in N01. Compatibility proves
agreement on their overlaps, including H=Id, K=Id, K=H and J=Top; there
are no independently prescribed conflicting copies. The union is now a
genuine finite joint partial isomorphism of the ACTUAL full exact sorts.
Joint exact homogeneity supplies ONE ambient original automorphism.
It permutes all named K-classes by barbeta, hence preserves D setwise, and
its restriction induces EXACTLY gamma on EVERY b in B. This proves C21.
No global section or independently selected real-fibre permutations are used.

Take ANY original request (p,gamma), where p is a partial automorphism of
A0, gamma is in FULL Aut(B), and

\[
                 \pi_H p(x)=\gamma\pi_H(x)
                       \quad(x\in\operatorname{dom}p).
\]

N04 gives the genuine quotient partial map barp. Project the compatibility
equation through r and use r pi_H=pi_J. It says precisely that barp is
compatible with the ACTUAL coarse action rho(gamma) on ALL barB. The
supplied relative quotient EPPA witness extends this pair to barbeta with
EXACT component rho(gamma). Use C21 with the original prescribed gamma
and p0=p. Its restriction to D extends p and retains gamma on ENTIRE B.
This proves C22/C23 for all requests on the SAME full D.

In particular, if p is empty, every prescribed gamma remains a request;
its projected empty request retains rho(gamma), and the three-sort lift
realizes gamma exactly. The same covers every compatible singleton request.
We never replace full Aut(B) by a selected subgroup, request-generator list,
or merely its action on owners meeting dom(p). Onto rho and fibre-transitive
ker(rho) were not needed: gamma was ALREADY prescribed. No ordinary EPPA(Q)
or owner master enters this extension argument.

## N08: The extra owner-kernel hypothesis is used for relative roots only

This section proves C24–C26. Now additionally assume the ACTUAL
projection-equivariant rho:FULL Aut(B)->FULL Aut(barB) is onto, with kernel
transitive on each actual cover fibre B->barB. These are substantive extra
owner hypotheses, not consequences of finite K, exactness, or the ordinary
quotient witness.

Recall directly the shared prescribed-action point proof in this actual
setting. Given b,b' in B and bargamma in Aut(barB) with
bargamma(r(b))=r(b'), choose gamma0 lifting bargamma by onto rho.
The points gamma0(b) and b' lie in the SAME actual r-fibre. Kernel
transitivity gives eta in ker(rho) sending the first to the second. Then

\[
 \gamma=\eta\gamma_0,\qquad
 \rho(\gamma)=\overline\gamma,\qquad \gamma b=b'.
\]

This proves C24. Neither action need be faithful, and there is no requirement
to choose gamma0 homomorphically in bargamma. The B001 criterion is recalled
as support; B018's conjugation point lemma is an already-covered independent
result outside this module and is not being used as an unrelated action-surjectivity theorem.

For ANY nonempty unsafe Z subset D and ANY selected z, N05 shows that
pi(Z) is a nonempty barS-unsafe set of distinct classes, possibly a
singleton. The supplied relative rooted quotient witness gives relative
baralpha on Dbar with its actual entire barB component bargamma, satisfying

\[
 \overline\alpha(\pi Z)
       \subseteq\operatorname{acl}_{\overline Q}(\pi A_0),
 \qquad \overline\alpha(\pi z)=\pi a
       \quad\text{for SOME ACTUAL }a\in A_0.
\]

In particular bargamma(J[z])=J[a]. Apply C24 to b=H[z], b'=H[a]
and this bargamma. It supplies gamma in Aut(B) with the SAME entire
coarse component and gamma(H[z])=H[a]. The singleton original map z->a
is genuine by original transitivity. It agrees with baralpha on the
K-projection and gamma on the H-projection, so N07's three-sort lift applies
with p0 this singleton. Its restriction alpha to the SAME D sends z
LITERALLY to a, has exact owner component gamma on ALL B, and sends every
point of Z into

\[
 \pi^{-1}\operatorname{acl}_{\overline Q}(\pi A_0)
             =\operatorname{acl}_Q(A_0).
\]

This proves C25. The rooted assertion allows choosing its resulting owner
component; it does NOT demand an independently prescribed gamma from an
unrelated source-extension request. No independent permutation of finite
real fibres is selected. Full owner kernel transitivity only arranges one
actual H-owner point, and joint exact homogeneity realizes the compatible
real root simultaneously with both entire quotient actions.

C13, C20, C23 and C25 together prove C26: the ONE finite full K-preimage
contains acl_Q(A0), has exact complete finite owner image B, extends every
compatible request and has all relative rooted transports. The hypotheses
H full exact, complete B and actual onto/fibre-transitive rho remain visible.
There is no conclusion for arbitrary nonexact H or an incomplete chosen
finite inverse owner subset under these assumptions alone.

## N09: Source export, implementation order and downstream boundary

C27 combines the four scoped subcontracts of `lem:acf-finite-lift`:

1. For EVERY finite real A0, including empty, the two-sided finite-acl
   identity C06.
2. From the GIVEN original strong absolute closed-S_Q premise, strong
   closed-barS descent C10 using every entry of the full K×K matrix.
3. For nonempty A0 and a supplied ordinary quotient rooted EPPA witness,
   the SAME full K-preimage has ordinary source extension and literal-root
   transport, C18.
4. Under the separate stronger ACTUAL full exact owner/complete finite
   packet/actual onto owner map and fibre-transitive kernel hypotheses,
   the analogous relative conclusion C26 with exact entire B actions.

Only C06 is also mapped to the selected auxiliary
`eq:acf-finite-acl`. There are 10 definitions, 27 human-expanded local
claims and 6 implementation tasks. The point lemma, mixed join, nested
mixed reduction, exact source inheritance and shared action criterion are
providers and are not counted as new numbered results. The receiving Lean
project still has to implement all these contracts; metadata DAG validation
and finite controls are provenance/diagnostic checks, not proof checking.

The provider-before-consumer order has explicit firewalls. Closure and safe
descent precede all witnesses. Finite recognition/two-sort lifts precede
ordinary EPPA and use no S or owner H. Ordinary reconstruction has no
relative H/B/kernel or owner-master dependency. Relative source extension
uses the prescribed gamma directly and precedes the owner-kernel correction.
Only relative root transport depends on that correction. The six tasks
retain exactly these branches.

In the later rank-restoration consumer, a NONIDENTITY finite exact kernel
is chosen and strict quotient rank decrease is proved there. Apply the
lower-rank result to Q/K with the descended full-matrix palette, then use
ONLY the ordinary C18 implication. B029 itself allows K=Id and proves no
rank decrease. The rank step needs no relative H, owner packet B, owner
master, or prescribed owner-kernel hypothesis. In particular B028's
normalized one-direction geometry and the exactness of the greatest finite
F are not inserted into this arbitrary-rank reconstruction.

An arbitrary reconstructed witness need not be absolutely acl-closed.
It is full-K-saturated and contains acl_Q(A0); it is absolutely closed
exactly when its supplied quotient witness is. If a later consumer requires
additional full-F closure, it must supply and justify the corresponding
quotient closure property separately. No such extra assertion is hidden in
the source's ordinary finite rooted implication.

The finite control script covers bounded action/recognition/matrix/root
models, including dropped-premise failures. These cannot establish actual
infinite-source CCO, joint exact homogeneity, strong closed-S amalgamation or
global EPPA. There are no external theorem inputs newly introduced here and
no mathematical source changes or new proof axioms.
