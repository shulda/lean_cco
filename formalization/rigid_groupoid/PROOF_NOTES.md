# Actual rigid groupoids and phase seeds — proof notes

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`. Mathematical preparation for OTHER Lean projects; no Lean proof is claimed. The human TeX is unchanged. Precise node contracts, selected source coverage and dependency firewalls are in `module.json`. Object kernels, original logical equality and quotient logical equality have distinct roles.

## N00: Actual simultaneous quotient blocks and exact calculus

Fix one ambient group G=Aut(N), acting on finitely many inhabited named
original sorts, each transitively. The finite complete original atomic
palette consists of its ACTUAL ordered-pair orbitals. Same-sort orbitals
are symmetric; mixed orbitals have typed converses and are not assumed
self-converse. All compositions are represented relations. Use the original
FULL RAW exact calculus of `thm:full-typed-exact-balls`: exact converse,
nonempty exact product closure, and finite exact support 2-Helly. The
elementary ingredients are associativity, identities, monotonicity, atomic
Peirce, and seriality/coseriality of nonempty invariant typed relations.
No heterogeneous BALL Helly or exact CRT is needed in this section.

These may be taken as precise upstream calculus contracts. When they are
instantiated via the pinned source-level theorem, retain that theorem's
original hypotheses, including its stated countability convention. The
arguments below introduce no new countability premise, countable lifting,
quotient homogeneity theorem, or uncountable source-inheritance claim.

This section fully expands the selected source result
`lem:typed-simultaneous-blocks`. Choose a full exact invariant equivalence
E_s on every original sort visited by the quotient language. Put Q_s=N_s/E_s
and name all ACTUAL G-orbitals on ordered quotient pairs. This is the induced
ambient action; no assertion that every automorphism of the resulting
quotient structure lifts to N is used. Fix one kernel per named quotient
sort. If two endpoints have the same original sort name, that assignment
must be consistent. Alternatively distinct formal quotient copies must be
explicitly indexed, and a composable middle object must be the very same
copy with the same assigned kernel.

For an old atom c:s->t define the OLD block B_c=E_s;c;E_t. It contains c
by reflexivity of the kernels, is nonempty full exact by original exact
convolution, and is saturated by E_s,E_t. It is invariant and hence a union
of whole original atoms. If an old atom d belongs to B_c, take a represented
d-edge obtained by moving the two endpoints of a c-edge within their
E_s,E_t-classes. Reversing the equivalence moves proves c belongs to B_d.
Saturation and monotonicity then give both B_d<=B_c and B_c<=B_d. Thus if
two blocks intersect, an atom in their intersection makes them equal.
Every old atom lies in its own block, so the DISTINCT blocks partition
the old typed atom palette; the list indexed by all old atoms can contain
duplicates.

Let c^Q denote the actual quotient orbital of ([x]_(E_s),[y]_(E_t)) for
an old c-pair (x,y). Its full old inverse image is exactly B_c. Indeed, an
old pair (u,v) projects to a G-translate of that quotient pair iff some
original automorphism g satisfies u E_s gx and gy E_t v, which gives a
represented B_c-walk. Conversely such a walk has a middle c-pair, which
is a G-translate of (x,y); its quotient endpoints are the required
translate. Every quotient pair has old representatives, so every actual
quotient orbital occurs this way. This identifies the block partition
with the actual quotient pair-orbital partition.

In particular the inverse image of quotient equality is E_s, including
when an old DIVERSITY atom inside E_s projects to equality. A same-sort
diversity quotient orbital has pullback disjoint from E_s. The OLD relation
B_c is generally a union of old atoms; it is not literally the quotient
atom c^Q, which is a relation on quotient points. Original logical equality
projects to quotient equality, and its block is E_s. Typed top pulls back
to typed top. Quotient same-sort orbitals remain symmetric by projection;
mixed converse retains its types.

For composable quotient invariant relations U:s->t and V:t->u, write
U_tilde,V_tilde for full inverse images. Then

    inverse_image(U;V) = U_tilde;E_t;V_tilde
                       = U_tilde;V_tilde.

A quotient intermediate class can have witnesses y_1,y_2 which are
different old points, but y_1 E_t y_2. This proves the first equality.
The full inverse images satisfy U_tilde;E_t=U_tilde and
E_t;V_tilde=V_tilde, proving the second. Equivalently, choose any one real
representative of the intermediate class: the full preimage constraints
hold for it. Surjectivity of each quotient map makes inverse image faithful.
Converse and all intersections commute with inverse image as ordinary set
operations. No commutativity of mixed arrows is used.

Consequently the inverse image of a quotient atomic word with old letters
c_1,...,c_k is the represented product of their exact blocks, namely

    E_s0;c_1;E_s1;c_2;...;c_k;E_sk.

The doubled middle E-factors in a product of blocks collapse by idempotence.
The remaining middle factors are genuine and may NOT be removed without
an additional intertwining argument. For a zero-length loop word the
pullback is E_s, not old Id_s. Thus every quotient word has nonempty old
full exact inverse image, by repeated original exact convolution. A
nonempty quotient exact menu is a finite meet of quotient words; its
pullback is their nonempty exact old meet. The empty restriction family
gives top. This proves the unrestricted SAFE direction: quotient full
exactness implies original full exactness under inverse image. It does
not prove arbitrary mixed old exact descent.

To obtain quotient WORD 2-Helly, take finitely many nonempty quotient word
profiles which meet pairwise. Their full inverse images are old full exact
relations with pairwise nonempty intersections, because quotient maps are
onto. Original exact support Helly gives an old pair in every inverse
image. Its quotient pair lies in every quotient profile. Equivalently the
old atom of that pair lies in every saturated pullback, and its whole
quotient block belongs to every quotient menu. An empty family gives the
inhabited typed top. Flattening presentations gives quotient full exact
2-Helly, and reversal of quotient words gives exact converse closure.

We also need quotient exact CONVOLUTION, not merely exact old pullback of
a quotient product. Derive it algebraically from this quotient word Helly
and the elementary quotient Peirce law. Both belong to actual represented
G-orbit relations, independently of quotient homogeneity or CCO.

Let D=intersect_alpha P_alpha:s->t and F=intersect_beta Q_beta:t->u
be nonempty quotient exact menus with nonempty restriction lists for now.
For a quotient atom c:s->u assume c belongs to every P_alpha;Q_beta.
Consider the quotient WORD family

    {P_alpha}_alpha union {c;Q_beta^converse}_beta

of type s->t. The P_alpha meet pairwise because D is nonempty. The second
family meets pairwise: choose an atom f_0 in F; the nonempty product
c;f_0^converse is contained in every c;Q_beta^converse. All cross pairs
meet by typed Peirce and the assumed c-memberships. Quotient word Helly
therefore gives a quotient atom d in D and in every c;Q_beta^converse.

Now the WORD family {Q_beta}_beta together with the single profile
d^converse;c, of type t->u, meets pairwise: the Q_beta have nonempty common
intersection F, and each cross intersection is nonempty by Peirce applied
to d in c;Q_beta^converse. A second use of quotient word Helly gives an
atom f in F intersect (d^converse;c). Peirce yields c in d;f, hence c in
D;F. Monotonicity gives the opposite inclusion, proving

    D;F = intersect_(alpha,beta) (P_alpha;Q_beta).

Every displayed factor on the right is a quotient word by concatenation.
The product is nonempty by seriality of invariant relations on transitive
quotient sorts. If a restriction family is empty, its relation is typed
top. Typed top absorbs a compatible nonempty invariant factor, by
seriality/coseriality; this proves the same formula with the empty-list
convention. Nonempty-result meet distributivity follows by flattening
presentations. Identity-bearing words and identity outputs remain present
throughout both Helly steps.

This reuses the algebraic two-Helly proof of RAW convolution, with its
inputs now proved on Q. It does not infer quotient product exactness from
the exactness of its OLD preimage, which would be the forbidden reverse
descent step. It also does not invoke `thm:typed-simultaneous-exact-quotients`,
countable back-and-forth, or any theorem saying Q is a new homogeneous CCO
source. The elementary block/product/pullback portion matches the prepared
`exact_crt` C19/C20 interfaces; quotient word Helly and the displayed
convolution argument complete the additional selected source export.

## N01: Bridge kernels and quotient bijections

Fix a full exact original invariant equivalence K_a. A bridge R:a->b is
nonempty full exact, K_a;R=R, and R;R^converse=K_a. All types are original
named sorts in the same ambient G-action. Define K_b=R^converse;R.
Converse and exact convolution are the only non-elementary RAW calculus
inputs for the kernel construction; exact support Helly is not used here.

Nonempty invariant R is serial at every source point and coserial at every
target point. Thus K_b contains Id_b. It is symmetric and full exact, and

    K_b^2=R^converse;K_a;R=R^converse;R=K_b,
    R;K_b=K_a;R=R.

It is therefore a full exact equivalence. R is saturated on both ends and
its converse is a bridge with source K_b and target K_a. The identity
relation of the quotient object (a,K_a) is K_a, not necessarily old Id_a.

Define the induced relation between actual classes in N_a/K_a and N_b/K_b.
Saturation makes it well-defined and fills every corresponding rectangular
pair of classes. Seriality gives a value for every source class. If xRy
and xRz, then yK_bz, so the value is unique. If two source classes have
the same value, right saturation allows representatives with one common
target y; their source points are K_a-related by R;R^converse=K_a.
Coseriality gives surjectivity. Hence the induced relation is an actual
G-equivariant bijection. R itself need not be a function on original real
points. A bridge with nontrivial gates can have many real neighbours per
point on either side.

The graph of this quotient bijection is one G-orbital: G is transitive on
its source quotient, and equivariance transports the corresponding target
class at the same time. This does not require either quotient to be
homogeneous under its full automorphism group. It gives the useful block
identity for EVERY old atom c contained in R:

    R=K_a;c;K_b.

For the nontrivial inclusion, choose one old c-pair. Its quotient graph
pair can be moved to the quotient graph pair of any desired R-pair by an
original automorphism. The two endpoint K-moves then recover that R-pair.
The reverse inclusion follows from c<=R and saturation. Logical equality
is permitted as c when its type and the particular bridge allow it; no
diversity-only assertion is being made.

Now take two bridges R,S:a_*->b with the SAME source kernel K_*.
Set T=R^converse;S, an invariant SAME-SORT relation on b. It is symmetric
because all old b-orbitals are symmetric. Consequently

    R^converse;R
      = R^converse;S;S^converse;R
      = T;T^converse
      = T^converse;T
      = S^converse;R;R^converse;S
      = S^converse;S.

The first and last equalities use the bridge source equations and source
saturation. Thus the target kernel depends only on the reached original
sort b and the chosen root object, not on the bridge/path. This is NOT
proved by commuting arbitrary mixed relations: only the same-sort T was
made self-converse. For a return to the root compare with its identity
bridge K_*; the returned kernel is K_*.

## N02: Finite connected rigid groupoid

Initially regard objects as pairs (original sort, reached kernel), rather
than assuming one kernel per sort before N01 proves it. Starting with one
root object, close under all applicable full exact bridges, converses and
represented compositions. For R:a->b and S:b->c with the SAME middle
kernel K_b, exact convolution makes R;S nonempty full exact and

    (R;S);(R;S)^converse
       =R;K_b;R^converse=K_a,
    K_a;(R;S)=R;S.

Thus it is again a bridge; its target kernel is K_c by the converse
calculation or by the uniqueness proved in N01. Composition is represented
associativity, and K_a,K_b act as the appropriate identity arrows.
Converse supplies inverse arrows. Every reached object is connected to
the root. N01 identifies all reached kernels at the same original sort,
so there are at most as many objects as named original sorts. There are
finitely many old atomic supports of each ordered type, hence finitely
many possible arrows. The resulting groupoid is finite and connected.

For an isotropy arrow h:a->a, old same-sort symmetry gives h=h^converse.
The bridge equations yield h^2=K_a. Therefore every element of the
isotropy group is self-inverse. It follows algebraically that hk=kh,
since (hk)^(-1)=k^(-1)h^(-1)=kh but also (hk)^(-1)=hk. A finite abelian
group of exponent two is an elementary abelian 2-group; an elementary
basis construction repeatedly adjoins an element outside the generated
subgroup, doubling its size, and terminates by finiteness. No Hasse
index-two theorem or parity pivot is used.

If R,S:a->b, the isotope h=R;S^converse at a satisfies h;S=R. It is unique,
as multiplying on the right by S^converse recovers h. Likewise the isotope
k=S^converse;R at b is the unique element with S;k=R. Thus every nonempty
hom-set is a torsor under either endpoint isotropy group. Empty hom-sets
outside the reached connected component are not implicitly declared torsors.

For freeness, a G-equivariant permutation of a transitive quotient fixing
one point fixes every point: express any point as a G-translate of the
fixed one. An isotropy arrow fixing a quotient point is consequently the
identity permutation and, by saturation, the old relation K_a. If R,S
agree at one quotient source point, R;S^converse fixes it, so R=S.
Distinct arrows of one type have disjoint quotient graphs and disjoint
old represented relations. This uses no faithful ambient action assumption.
Nonidentity isotropy arrows are fixed-point-free on quotient points.

The one-object trivial-isotropy case is allowed. A quotient object with
one point has only its identity isotropy permutation; it cannot supply a
nonidentity gate in N03. None of these conclusions asserts that every
equivariant quotient bijection is word-exact: the groupoid consists of
the exact bridges selected by the definition.

## N03: Dominant involution transport

Assume the preceding groupoid has a chosen nonidentity root isotropy arrow
t_* and that EVERY original full exact invariant equivalence Z_*>K_*
contains t_*. This is an explicit original-level dominance premise. The
maximal exact parity-gate theorem of `parity_hasse` can supply such initial
data in its own source setting; neither that theorem, the Hasse proof nor
relative closure separation is needed to prove transport once the data
are supplied. In a genuinely typed setting retain the exact scope of the
chosen initial-gate provider rather than silently applying a one-original-
sort gate construction to mixed words.

For a root bridge R:a_*->b put t_b=R^converse;t_*;R. It is a full exact
isotropy arrow by closure, and t_b^2=K_b. If t_b were K_b, conjugating back
by R would make t_*=K_*, a contradiction. For another root bridge S set
h=S;R^converse. Then S=h;R, and the abelian root isotropy group gives

    S^converse;t_*;S
       =R^converse;h^converse;t_*;h;R
       =R^converse;t_*;R.

Thus t_b is independent of R. This calculation uses commutativity INSIDE
one isotropy group, not commutativity of differently typed relations.

For any original full exact equivalence Z_b>=K_b define
C_R(Z_b)=R;Z_b;R^converse. It is nonempty full exact by convolution,
symmetric, and contains K_*. Its square equals itself because
R^converse;R=K_b and K_b;Z_b=Z_b=Z_b^2. Thus it is an equivalence above
K_*. The reverse construction D_R(Z_*)=R^converse;Z_*;R sends full exact
equivalences above K_* to ones above K_b. The two composites are

    D_R(C_R(Z_b))=K_b;Z_b;K_b=Z_b,
    C_R(D_R(Z_*))=K_*;Z_*;K_*=Z_*.

Both preserve inclusion, so this is an order isomorphism of the ORIGINAL
exact-equivalence posets. It preserves strictness, since the kernels map
to one another and the maps are inverse. No assertion that every old exact
relation descends to a quotient word is used to obtain this isomorphism.

If Z_b>K_b, its image Z_*>K_* contains t_* by dominance. Conjugating this
inclusion back gives t_b<=Z_b. Hence each reached object has the transported
dominant nonidentity exact involution at the original level.

For a nonidentity full exact equivalence on N_b/K_b, use the unrestricted
quotient FULL WORD PULLBACK of N00. Its old inverse image is a full exact
equivalence Z_b>K_b; strictness follows from faithful inverse image and
the fact that quotient identity pulls back to K_b. Apply old dominance
and project to obtain the quotient containment. If the quotient word
language includes other quotient sorts, supply full exact kernels on
every visited sort, for example the already reached K_s or explicit
identity kernels; otherwise state that only the one quotient sort is used.
No arbitrary old-to-quotient exact descent is needed.

In fact the projected graph of t_b on N_b/K_b is one named actual quotient
orbital by N01 and is therefore itself exact as a single letter. It is
fixed-point-free by N02. This special atomicity is different from general
exact descent. There is no need for general quotient source inheritance,
SAP, a section of automorphism groups, or countable lifting.

## N04: Exact quotient bridge correspondence

Fix full exact invariant E_a<=K_a and E_b<=K_b, with compatible exact
kernel assignments on any remaining quotient sorts. Form the actual Q
from N00, and ASSUME that K_a^Q=K_a/E_a and K_b^Q=K_b/E_b are FULL RAW
exact equivalences of its quotient word algebra. Being old full exact
and lying above an exact kernel does not by itself establish this premise
in the general independently quotiented mixed-sort situation.

The prepared one-original-sort symmetric descent theorem from `exact_crt`
can verify this premise in its stated one-original-sort setting. A supplied
presentation-local intertwining condition can also verify it by the typed
descent criterion there. Neither is an unrestricted mixed descent theorem.
Merely knowing the inverse image of a quotient exact menu is old exact
does not supply this forward direction. Retain projected-gate exactness
as a hypothesis when neither sufficient criterion has been established.

Every original bridge R with source K_a and target K_b is automatically
E_a,E_b-bisaturated, by its K-saturation and the nested equivalences.
Let R^Q be its quotient image. The elementary faithful quotient product
identities of N00 preserve the bridge equations, so R^Q is a functional
bridge at the projected gates, before its exactness is checked. It is
functional between Q_a/K_a^Q and Q_b/K_b^Q, canonically the original
coarse quotients N_a/K_a and N_b/K_b. It need not be a function on the
finer Q_a,Q_b point sets themselves.

Choose any old atom c<=R. N01 gives R=K_a;c;K_b. Let c^Q be the named
actual quotient atom with old pullback E_a;c;E_b. Faithful inverse image
and kernel absorption show

    R^Q=K_a^Q;c^Q;K_b^Q.

Indeed the pullback of the right-hand product is
K_a;E_a;c;E_b;K_b=K_a;c;K_b=R. Only nested-equivalence absorption was
used; no mixed commutation occurred. Because both projected gates are
exact by hypothesis and c^Q is an atomic word profile, the quotient exact
convolution proved in N00 makes R^Q full exact. This is the essential
forward exactness step. It is not inferred from the exactness of R alone
or from old exactness of the product's pullback.

Conversely let R^Q be a quotient full exact bridge with source K_a^Q and
target K_b^Q. Its old inverse image R is nonempty full exact by N00 and is
endpoint-saturated. Pulling back the quotient bridge equations gives

    K_a;R=R, R;R^converse=K_a,
    R^converse;R=K_b.

Thus it is an original full exact bridge. Projection and inverse image
are inverse on all endpoint-saturated invariant relations, so their
restrictions give the asserted bijection of bridge sets. They preserve
converse and composition because the middle quotient object, its assigned
kernel, and the full saturated pullbacks match in every composable pair.
In particular no new exact functional bridge appears in Q and none of
the old ones disappears under these explicit projected-gate hypotheses.

The identity arrow of a bridge object remains its gate: K_a projects to
K_a^Q, which is quotient equality only when E_a=K_a. Empty word conventions
at the fine quotient still pull back to E_a, whereas the identity at the
coarse bridge object pulls back to K_a. Distinguish these two identities.
The cases of singleton quotient sorts or trivial bridge isotropy require
no separate algebraic exception.

For this correspondence, the necessary upstream obligations are original
typed exact product/converse/Helly, the fully expanded selected quotient
block/pullback lemma N00, and the explicit quotient-gate exactness. The
abstract groupoid and dominance transports use only the weaker original
convolution/converse part until their quotient consequences. The optional
`parity_hasse` provider supplies initial dominant data, and optional
`exact_crt` descent criteria may discharge projected-gate hypotheses. No
general simultaneous quotient-source theorem, hidden SAP, heterogeneous
ball Helly, or countable joint-lifting argument is imported here.

## N05: Affine translate Helly and rigid slices

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`. This expands `lem:foundational-rigid-affine` and selects the independent upstream `lem:foundational-affine-translate-helly` from `sections/finite_packet_kernel_constraints.tex`. The selected finite affine lemma does not import that file's moving-owner kernel/CSP theorems, countability assumptions or compactness arguments.

First prove the finite-group lemma completely. Let V be a finite elementary abelian 2-group, viewed as an F2-vector space, and let A be a nonempty subset. Assume every finite pairwise-intersecting family of translates of A has nonempty total intersection. An affine subspace contained in A exists because any singleton is one. Choose one of maximal dimension, say v+K, with K linear, and replace A by A+v. This preserves the translate-Helly property and maximal possible affine dimension, and now K is contained in A and 0 belongs to A.

If A is not K, choose a in A outside K and put W=K+<a>. Then W=K union (a+K), and dim(W)=dim(K)+1. Every element of K is 0+k for two elements of A, and every element a+k is also the sum of two elements of A. Hence W is contained in A+A. For u,v in W, u+v belongs to W and therefore A+A. If u+v=a_1+a_2 with a_1,a_2 in A, then a_1+u=a_2+v, showing (A+u) intersect (A+v) is nonempty. Thus the FINITE family {A+w:w in W} is pairwise-intersecting. Its assumed common point z satisfies z+w in A for every w in W, since minus equals plus in characteristic two. This puts the affine space z+W inside A, contradicting maximality. Therefore the translated A is K, and the original A is an affine coset. This includes the zero-dimensional group and singleton A. Nonemptiness of A, finiteness of V and its exponent-two law are explicit premises. No CCO, SAP, exactness, group action or lattice distributivity occurs in this proof.

For rigid slices, assume the previously constructed finite connected groupoid of original full RAW exact bridges, with one actual kernel K_a at each reached original sort, elementary abelian isotropy, and free action on the actual quotient point sets Q_a=M_a/K_a. Original named sorts are individually transitive. The needed exact-calculus contracts are typed nonempty product closure/converse and support 2-Helly, from `thm:full-typed-exact-balls`(i),(ii). Different-centre ball Helly (iii) is unnecessary for this slice argument. Its geometric source realization uses the original symmetric/converse-paired homogeneous CCO source but no SAP.

Let D:a->b be a nonempty full RAW exact relation, K_a,K_b-bisaturated, all of whose pairs belong to the union of rigid arrows a->b. Each rigid quotient bijection is an equivariant graph on Q_a times Q_b. Because the ambient group is transitive on Q_a, its graph is one actual ambient pair orbital. This is only a transitive-group-action fact, not a claim that the quotient has independently inherited a homogeneous/AP/CCO source structure. Distinct rigid arrows have disjoint quotient graphs by freeness. They also have disjoint full old pullbacks.

The bisaturated D descends to an ambient-invariant quotient relation. If it meets one rigid quotient graph, it contains that whole orbital; lifting back by saturation makes it contain the whole corresponding old bridge. Its support hypothesis therefore expresses D as a union of entire rigid arrows. These old bridges are generally rectangular relations between kernel classes, not graphs of functions on original real points. They become bijection graphs only on Q_a,Q_b.

Choose one reference arrow d:a->b. The hom-set is a torsor for the target isotropy V=H(b,b), so write D as the union of d;h for h in a nonempty subset A of V. For every target isotropy arrow v, the represented product D;v is nonempty full exact by typed convolution, and corresponds precisely to the translate A+v. Translate intersections in the finite coefficient set are equivalent to intersections of these full exact old relations, because each arrow is nonempty and the arrow relations are disjoint. If finitely many translates meet pairwise, support 2-Helly produces one old pair in all the translated relations; that pair belongs to a unique rigid arrow and hence gives a common coefficient. Thus A satisfies the finite affine lemma just proved.

Write A=h_0+S for a subgroup S<=V and absorb h_0 into d. Then D=dS, meaning the UNION of the bridges d;s, s in S. Put U_S=union_(s in S) s as an old relation b->b. Relational composition distributes over unions, d^converse;d=K_b, and subgroup closure gives

    D^converse;D = U_S.

Typed convolution makes U_S full RAW exact. It is an actual invariant equivalence containing K_b: the identity arrow is K_b, inverses give symmetry and subgroup multiplication gives transitivity. This is the meaning of 'exact subgroup' in this proof. It does not say that every abstract isotropy subgroup has an exact union. Nor does old exactness of U_S alone assert quotient word-exactness of its image under K_b; arbitrary exact descent remains a separate interface.

## N06: Factorisation of products inside a rigid bridge

This expands `lem:foundational-rigid-factor`. Assume individually transitive original source sorts and actual invariant relations with the typed full exact product/converse calculus. Let nonempty full exact A:a->b and B:b->c satisfy A;B contained in one full exact bridge R:a->c with source kernel K_a. No endpoint bisaturation of A or B is presumed. This argument needs represented seriality/coseriality and exact convolution, not support Helly, affine slices, SAP, a phase character or a quotient-source inheritance theorem.

Every nonempty invariant typed relation is serial at every source point and coserial at every target point, by transitivity of the respective original sorts. In particular Id_b is contained in B;B^converse and Id_a in A;A^converse. Consequently

    A;A^converse <= A;B;B^converse;A^converse
                 <= R;R^converse = K_a.

Set R_1=K_a;A. It is nonempty full exact by typed convolution and K_a;R_1=R_1. Its square against converse is K_a;A;A^converse;K_a, contained in K_a by the previous inclusion. The reverse inclusion follows from Id_a<=A;A^converse and K_a squared=K_a. Thus R_1;R_1^converse=K_a, so R_1 is a bridge. It contains A because K_a contains real identity. Let K_b=R_1^converse;R_1; the bridge calculus proves this is its target full exact invariant equivalence.

The target K_b is CONSTRUCTED here. Do not infer that it equals any arbitrary preassigned owner kernel on sort b. If b has already been reached from the same rooted rigid component, the separately proved path/kernel uniqueness theorem identifies it with that component's kernel. Without that premise no unrelated owner-kernel equality follows.

Since R_1;B=K_a;A;B is contained in K_a;R=R, set

    B'=K_b;B,    C=R_1^converse;R.

Then B'=R_1^converse;R_1;B is contained in C. C is a full exact bridge from (b,K_b) to the target object of R, by converse/composition in the rigid bridge groupoid. B' is nonempty full exact, K_b-left-saturated and contains B. It is coserial onto the ORIGINAL target sort c because B already is.

For any (y,z) in C choose y' with (y',z) in B' by this coseriality. Since B' is contained in C, the common z gives (y,y') in C;C^converse=K_b. Left saturation K_b;B'=B' now gives (y,z) in B'. Hence B'=C. Take R_2=C. It contains B, and

    R_1;R_2=R_1;R_1^converse;R=K_a;R=R.

This is enlargement to bridges. It does not assert A=R_1, B=R_2 or A;B=R, and does not make the old real relations functional. The bridge equalities refer to kernel-saturated relations and actual quotient bijections. If the intermediate sort was not previously reached, R_1 supplies its reached object; no hidden owner sort is assumed beforehand.

## N07: Binary characters and global phase marking

This expands `thm:foundational-rigid-character`. The abstract input is a finite connected rigid groupoid with elementary abelian isotropy, an actual free action on its reached quotient point sets, and a distinguished nonidentity isotropy arrow t_* at a root object *. These groupoid/action facts were established earlier from the original exact source. Once supplied, this character construction needs only finite linear algebra and the choice of orbit seeds; it uses neither further CCO nor SAP nor a full exact quotient-source theorem. Tag quotient point sets by their objects when forming their disjoint union.

View the root isotropy as a finite F2-vector space. Its nonzero element t_* extends to a basis: start with {t_*}, repeatedly add a vector outside the current span, and stop by finiteness. Define chi_* as the coefficient of t_* in that basis. This is a homomorphism to F2 with chi_*(t_*)=1. The nonidentity premise is essential for this specified value.

Choose reference bridges B_b:*->b, with B_*=K_*. For an arrow R:b->c its unique root coefficient is h_R=B_b;R;B_c^converse, and

    R=B_b^converse;h_R;B_c.

Uniqueness follows by multiplying with the reference bridges and their inverses. For composable R:b->c and S:c->d, inserting B_c^converse;B_c=K_c gives h_(R;S)=h_R;h_S. Define chi(R)=chi_*(h_R). Then chi(K_b)=0, chi(R;S)=chi(R)+chi(S), and chi(R^converse)=chi(R). Thus chi is a functor to the one-object additive group F2. The chosen references define a functor but no canonical choice of functor is asserted.

For any bridge P:*->b put t_b=P^converse;t_*;P. If another path is h;P for root isotropy h, conjugating t_* by h changes nothing because root isotropy is abelian. Hence t_b is path-independent. Conjugation is injective, so it is nonidentity, and chi(t_b)=chi(P)+1+chi(P)=1. This path-independence uses abelian isotropy, not the separate dominance hypothesis from `lem:foundational-rigid-gate-transport`. No conclusion that all nontrivial exact equivalences contain t_b is needed or created here.

Freeness means a transporting arrow between two points in the same groupoid orbit is unique: two such arrows would differ by an isotropy arrow fixing a point, hence by identity. Choose one point q_0 and one initial bit on each groupoid orbit. Use ordinary classical choice if there are infinitely many orbits; no finiteness of the real universe is assumed. Define lambda(R q_0)=lambda(q_0)+chi(R), where R q denotes the endpoint given by the induced quotient bijection (independently of the convention for writing relational composition). Unique transport makes this well-defined. Functoriality gives the required equation for every further arrow.

These global bits need not be invariant under the ambient automorphism group and need not be definable. They intentionally add a unary marking. Pulling them back to the original reached sorts makes each bit constant on the relevant K_b-classes. The finitely many reached sorts and two bits give a finite unary expansion signature; the construction does not name every groupoid orbit by a predicate.

Every rigid arrow graph is one actual quotient pair orbital, and its phase difference is forced to equal its character. Conversely, if endpoints of a pair belong to the same groupoid orbit, some rigid arrow carries one to the other; equivariance and transitivity make their actual pair orbital exactly that arrow graph. Thus a nonrigid actual quotient pair orbital has endpoints in DIFFERENT groupoid orbits. Toggle one orbit's seed, leaving the other unchanged, to realize either phase difference on any selected such pair. This is existence across appropriate GLOBAL choices, not an assertion that an arbitrary single fixed marking realizes both differences everywhere. A nonrigid orbital is not assigned one forced character value.

Any finite original induced structure embeds in the original source and inherits a marking by restricting one globally chosen lambda. Hence forgetting unary phases is surjective onto the original finite age. This is reduct-surjectivity only. It does not prove AP, SAP, CCO, same-host lifting for every prescribed marking, owner homogeneity or preservation of arbitrary prescribed finite bit assignments. The latter issue has exactly the seed criterion in N08.

## N08: Finite phase seed extension and scope boundaries

This expands `lem:foundational-finite-phase-extension` and its auxiliary equation `eq:foundational-phase-seed-test`. Assume the free action of the finite connected rigid groupoid and a FIXED functor chi to F2. No distinguished t_* or chosen linear basis is required once that character is given; if supplied by N07 it already has the desired gate value.

Let F be an actual finite SET of tagged quotient points and epsilon:F->F2 a function. A necessary condition for a global compatible marking extending epsilon is that whenever q,r in F are in the same groupoid orbit and Rq=r, then

    epsilon(r)=epsilon(q)+chi(R).

The arrow R is unique by freeness. For q=r its identity arrow has character zero, so the condition is automatic. If a real input presentation mentions one quotient point repeatedly, its assigned bits must first define a consistent function epsilon on the actual point set. In particular, real representatives of the same K_b-class cannot be assigned conflicting bits. That equality condition must not disappear when translating the criterion to finite real data.

For sufficiency, partition the whole quotient-point universe into its groupoid orbits. In each orbit meeting F, choose q_0 in F and give it bit epsilon(q_0). In each orbit disjoint from F, choose an arbitrary seed point and bit. Define the bit on the entire orbit by lambda(Rq_0)=epsilon(q_0)+chi(R), with the arbitrary seed bit in the unprescribed case. Unique transporting arrows prove well-definedness, and functoriality proves every global arrow equation. For any other r in F in this orbit, the stated pairwise condition gives precisely epsilon(r). Distinct orbits impose no constraints on one another. This proves the if-and-only-if criterion.

The empty finite seed set is allowed and gives N07's unrestricted seed construction. A singleton always extends. Every prescribed pair in one orbit must satisfy its transport equation; pairs in different orbits impose no condition. There is no additional higher-arity character holonomy test, because chi is already a functor and the action is free. These two facts replace any putative extra loop constraints. This proof neither invokes compactness/Konig's lemma nor assumes an owner-stabilizer extension theorem.

Keep the nature of the output explicit: it is a global unary BIT FUNCTION satisfying fixed rigid-arrow equations, not an ambient automorphism, not a family of fibre permutations and not an element of a pointwise-owner kernel. Pairwise sufficiency for these seed bits does not imply that arbitrary finite pairwise compatible owner motions extend to global automorphisms. In particular `thm:finite-fibre-kernel-csp`, its compact-projection formula and its possible higher-arity eliminated constraints are NOT providers or consequences of this seed lemma. The neighbouring affine-translate lemma was selected from that file independently of all those theorems.

Likewise no new AP/SAP/CCO statement for a marked age follows here. Actual marked completion and moving-owner projection arguments require their own hypotheses and proofs. Nonrigid-pair flexibility comes from changing whole groupoid-orbit seeds globally, not from an unproved ability to change one point while keeping all its rigid partners fixed. Upstairs bridge relations may have many real successors; freeness and character transport refer to their actual quotient graphs, with the identity of object (b,K_b) equal to K_b rather than real equality.
